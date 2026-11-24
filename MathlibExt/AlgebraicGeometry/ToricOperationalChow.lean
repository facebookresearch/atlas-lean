/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ToricMinkowskiWeights
public import MathlibExt.AlgebraicGeometry.IntegralOperationalClasses

/-!
# Actual integral orbit-closure cap coordinates

Orbit closures are the closed subschemes whose pullbacks to every toric
monomial chart have the actual orbit monomial ideal. Cap coordinates are
degree of the compatible operational class applied to the integral orbit
fundamental cycle. Both Chow groups and degree are the actual integral
principal-divisor quotient and residue-degree map.

The fan-subdivision map is fixed on all monomial charts. Refined weights are
the literal sum over containing cones of the same dimension.

Source: Fulton--Sturmfels, *Intersection Theory on Toric Varieties*,
alg-geom/9403002v1, Theorems 2.1/3.2 and section 2. Toric chart gluing and
orbit schemes are source integration from TauCeti
62bbc0596dc3539d488232e4e924a338548ea0a9 (Apache 2.0),
Geometry/Toric/Algebraic/Fan/Scheme. Ordinary integral bivariant operations
and their normal-cone realization are credited in `IntegralGysinRecipes`.
The Minkowski balance, inverse and product comparisons are separate targets.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ToricOperationalChow

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open IntegerSchemeChow IntegralOperationalChow IntegralGysinRecipes IntegralOperationalClasses
open FiniteToricCoordinates ToricMinkowskiWeights
open scoped BigOperators

variable {n : ℕ} (F : FiniteFan n)

structure Model where
  source : FieldScheme ℂ
  realization : Realization ℂ F
  identifies : source.scheme ≅ realization.scheme
  [proper : IsProper source.scheme.hom]

attribute [instance] Model.proper

variable (M : Model F)

def chart (tau : F.Face) : affineChart ℂ tau.val ⟶ M.source.scheme :=
  M.realization.chartMap tau ≫ M.identifies.inv

def orbitIdeal (sigma tau : F.Face) : Ideal (CoordinateRing ℂ tau.val) := by
  classical
  exact if sigma.val.IsFaceOf tau.val then
    Ideal.span {f | ∃ u : dualSemigroup tau.val,
      (¬∀ x ∈ sigma.val, character n u.val x = 0) ∧ f = AddMonoidAlgebra.single u 1}
  else ⊤

structure OrbitClosures where
  source : F.Face → FieldScheme ℂ
  inclusion : ∀ sigma, (source sigma).scheme ⟶ M.source.scheme
  [closed : ∀ sigma, IsClosedImmersion (inclusion sigma).left]
  [integral : ∀ sigma, IsIntegral (source sigma).scheme.left]
  [proper : ∀ sigma, IsProper (source sigma).scheme.hom]
  dimension : ∀ sigma, topologicalKrullDim (source sigma).scheme.left =
    ((n - coneDimension sigma.val : ℕ) : WithBot ℕ∞)
  chartIdeal : ∀ sigma tau : F.Face,
    RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing ℂ tau.val))).inv ≫
      (pullback.snd (inclusion sigma).left (chart F M tau).left).appTop).hom) =
        orbitIdeal F sigma tau

attribute [instance] OrbitClosures.closed OrbitClosures.integral OrbitClosures.proper

variable (V : OrbitClosures F M) (O : CycleOperations (k := ℂ))
  (D : ∀ sigma : F.Face, DegreeComparison (V.source sigma))

def orbitClass (sigma : F.Face) (d : ℤ) : ChowGroup (V.source sigma) d :=
  cycleClass (V.source sigma) d (fundamental (V.source sigma) d)

def capCoordinates (k : ℕ) (A : ActionFamily M.source (k : ℤ)) : F.Face → ℤ := by
  classical
  exact fun sigma ↦ if coneDimension sigma.val + k = n then
    (D sigma).degree (chowCast (V.source sigma) (by omega)
      (A ⟨V.source sigma, V.inclusion sigma⟩ (k : ℤ) (orbitClass F M V sigma k)))
  else 0

def capHom (k : ℕ) : Class O M.source (k : ℤ) →+ (F.Face → ℤ) where
  toFun A := capCoordinates F M V D k A.val
  map_zero' := by
    classical
    ext sigma
    by_cases h : coneDimension sigma.val + k = n
    · simp [capCoordinates, h]
    · simp [capCoordinates, h]
  map_add' A B := by
    classical
    ext sigma
    by_cases h : coneDimension sigma.val + k = n
    · simp [capCoordinates, h, map_add]
    · simp [capCoordinates, h]

variable {G : FiniteFan n}

structure FanSubdivision (G : FiniteFan n) where
  contained : ∀ gamma : G.Face, ∃ sigma : F.Face, gamma.val ≤ sigma.val
  support : G.support = F.support

def refinedWeight (G : FiniteFan n) (k : ℕ) (w : F.Face → ℤ) : G.Face → ℤ := by
  classical
  exact fun gamma ↦ ∑ sigma : F.Face,
    if gamma.val ≤ sigma.val ∧ coneDimension gamma.val + k = n ∧
      coneDimension sigma.val = coneDimension gamma.val then w sigma else 0

def containingSemigroupMap {sigma gamma : Cone n} (h : gamma ≤ sigma) :
    dualSemigroup sigma →+ dualSemigroup gamma where
  toFun u := ⟨u.val, fun x hx ↦ u.property x (h hx)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

def containingChartMap {sigma gamma : Cone n} (h : gamma ≤ sigma) :
    affineChart ℂ gamma ⟶ affineChart ℂ sigma :=
  Over.homMk (Spec.map (CommRingCat.ofHom
    (AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ (containingSemigroupMap h)).toRingHom)) (by
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have hc : (AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ (containingSemigroupMap h)).toRingHom.comp
          (algebraMap ℂ (CoordinateRing ℂ sigma)) =
          algebraMap ℂ (CoordinateRing ℂ gamma) :=
        RingHom.ext fun z ↦ (AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ
          (containingSemigroupMap h)).commutes z
      rw [hc])

structure SubdivisionMorphism (G : FiniteFan n) (R : FanSubdivision F G) (N : Model G) where
  map : N.source.scheme ⟶ M.source.scheme
  [proper : IsProper map.left]
  normalized : ∀ (gamma : G.Face) (sigma : F.Face) (h : gamma.val ≤ sigma.val),
    chart G N gamma ≫ map = containingChartMap h ≫ chart F M sigma

attribute [instance] SubdivisionMorphism.proper

end MathlibExt.AlgebraicGeometry.ToricOperationalChow
