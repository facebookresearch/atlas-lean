/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BehrendEulerObstructionModels
public import MathlibExt.AlgebraicGeometry.RelativeDifferentialForms
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Actual critical ideals and Milnor fibres for Behrend normalization

The critical ideal is fixed on every affine open by all linear
coefficients of the actual universal derivative df. Its native
kernel subscheme retains nilpotents. No pointwise zero predicate
replaces the critical scheme.

The Milnor fibre is the actual nearby level f(q)=f(p)+η inside a
small Euclidean coordinate ball of an actual algebraic embedding.
Its Euler characteristic is computed from ordinary rational Betti
cohomology. The normalization statement retains every sufficiently
small positive ε and every sufficiently small nonzero η.

Reference: Behrend, arXiv:math/0507523v2, §1.2, equation (4).
The derivative uses the completed RelativeDifferentialForms.d0.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CriticalMilnorFibreModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open IntegralChowChernModels ComplexAnalytification
open BehrendEulerObstructionModels ConstructibleEulerCharacteristics

/-- The actual section module of Ω^1 on the open. -/
abbrev DifferentialSections (M : SchemeData) (U : M.scheme.left.Opens) :=
  ((LineBundleTaskContracts.forgetModules M.scheme.left).obj
    (RelativeDifferentialForms.forms M.scheme.hom 1)).obj (op U)

/-- The universal relative derivative of the original regular function, on this open. -/
def derivative (M : SchemeData) (f : Γ(M.scheme.left, ⊤)) (U : M.scheme.left.Opens) :
    DifferentialSections M U :=
  (RelativeDifferentialForms.d0 M.scheme.hom).d
    ((M.scheme.left.presheaf.map (homOfLE le_top).op).hom f)

/-- All coefficients of df are actual module-linear evaluations on Ω sections. -/
def criticalIdeal (M : SchemeData) (f : Γ(M.scheme.left, ⊤)) (U : M.scheme.left.Opens) :
    Ideal Γ(M.scheme.left, U) :=
  Ideal.span (Set.range (fun a : DifferentialSections M U →ₗ[Γ(M.scheme.left,U)]
    Γ(M.scheme.left,U) => a (derivative M f U)))

/-- The global ideal is normalized on every native affine open. -/
structure CriticalIdealModel (M : SchemeData) (f : Γ(M.scheme.left, ⊤)) where
  ideal : M.scheme.left.IdealSheafData
  normalized : ∀ U : M.scheme.left.affineOpens, ideal.ideal U=criticalIdeal M f U.val

/-- The source scheme is exactly the native unreduced critical-locus subscheme. -/
structure CriticalChart (X : SchemeData) where
  ambient : SchemeData
  dimension : ℕ
  [smooth : SmoothOfRelativeDimension dimension ambient.scheme.hom]
  function : Γ(ambient.scheme.left, ⊤)
  critical : CriticalIdealModel ambient function
  normalized : X.scheme = Over.mk (critical.ideal.subschemeι ≫ ambient.scheme.hom)

def criticalInclusion {X : SchemeData} (C : CriticalChart X) : X.scheme ⟶ C.ambient.scheme := by
  rw [C.normalized]
  exact Over.homMk C.critical.ideal.subschemeι rfl

/-- The actual affine space coordinate scheme. -/
def affineSpace (n : ℕ) : Over (Spec (.of ℂ)) :=
  Over.mk (Spec.algebraMap ℂ (MvPolynomial (Fin n) ℂ))

structure CoordinateEmbedding (U : SchemeData) where
  dimension : ℕ
  embedding : U.scheme ⟶ affineSpace dimension
  [closed : IsClosedImmersion embedding.left]

def coordinateFunction {U : SchemeData} (E : CoordinateEmbedding U)
    (i : Fin E.dimension) : Γ(U.scheme.left, ⊤) :=
  E.embedding.left.appTop
    ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin E.dimension) ℂ))).inv (MvPolynomial.X i))

/-- Evaluation is the actual regular-function evaluation on complex analytification. -/
def regularValue {U : SchemeData} (f : Γ(U.scheme.left, ⊤)) (p : space U.scheme) : ℂ :=
  p.eval f (by simp [ComplexPoints.Mem])

def coordinates {U : SchemeData} (E : CoordinateEmbedding U) (p : space U.scheme) :
    Fin E.dimension → ℂ := fun i => regularValue (coordinateFunction E i) p

def squaredDistance {U : SchemeData} (E : CoordinateEmbedding U)
    (p q : space U.scheme) : ℝ :=
  ∑ i, Complex.normSq (coordinates E q i - coordinates E p i)

/-- The literal nearby-level subspace inside the small coordinate ball. -/
def milnorFibre {U : SchemeData} (E : CoordinateEmbedding U) (f : Γ(U.scheme.left, ⊤))
    (p : space U.scheme) (epsilon : ℝ) (eta : ℂ) : TopCat.{0} :=
  TopCat.of {q : space U.scheme | squaredDistance E p q < epsilon^2 ∧
    regularValue f q=regularValue f p+eta}

def openInclusion {M : SchemeData} (V : M.scheme.left.Opens) (U : SchemeData)
    (h : U.scheme=Over.mk (V.ι ≫ M.scheme.hom)) : U.scheme ⟶ M.scheme := by
  rw [h]
  exact Over.homMk V.ι rfl

/-- The coordinate neighbourhood is an actual open of the same ambient critical chart. -/
structure CriticalNeighbourhood {X : SchemeData} (C : CriticalChart X) (p : space X.scheme) where
  openSet : C.ambient.scheme.left.Opens
  chart : SchemeData
  normalized : chart.scheme=Over.mk (openSet.ι ≫ C.ambient.scheme.hom)
  coordinate : CoordinateEmbedding chart
  centre : space chart.scheme
  centre_normalized :
    spaceMap (openInclusion openSet chart normalized) centre=spaceMap (criticalInclusion C) p

def localFunction {X : SchemeData} {C : CriticalChart X} {p : space X.scheme}
    (U : CriticalNeighbourhood C p) : Γ(U.chart.scheme.left, ⊤) :=
  (openInclusion U.openSet U.chart U.normalized).left.appTop C.function

/-- The source formula (4), with its actual small-radius/nearby-level quantifiers.
This is a theorem target; it is not a hypothesis of the Behrend weight model. -/
def MilnorNormalization {X : SchemeData} (C : CriticalChart X) (W : SchemeBehrendModel X)
    (p : space X.scheme) (U : CriticalNeighbourhood C p) : Prop :=
  ∃ epsilon0 : ℝ, 0<epsilon0 ∧
    ∀ epsilon : ℝ, 0<epsilon → epsilon<epsilon0 →
      ∃ delta : ℝ, 0<delta ∧
        ∀ eta : ℂ, eta≠0 → ‖eta‖<delta →
          ∃ B : FiniteOrdinaryBetti (milnorFibre U.coordinate (localFunction U)
            U.centre epsilon eta),
          W.value p=(-1 : ℤ)^C.dimension * (1-ordinaryEuler B)

end MathlibExt.AlgebraicGeometry.CriticalMilnorFibreModels
