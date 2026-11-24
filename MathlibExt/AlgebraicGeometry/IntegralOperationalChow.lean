/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.IntegerSchemeChow
public import MathlibExt.AlgebraicGeometry.GeometricChowOperators
public import Mathlib.RingTheory.ReesAlgebra
public import MathlibExt.AlgebraicGeometry.SchemeNormalConeCharts

/-!
# Native integral cycle operations and normal-cone comparison contracts

The groups are the actual integral principal-divisor quotients. Proper
pushforward is normalized by residue degrees. Flat pullback is the literal
inverse-image fundamental-cycle sum; pure relative dimension is recorded
independently of the selected output grading. Normal cones are characterized
on every affine chart by the actual quotient-tensor-Rees algebra.

These are source integration contracts, not new scheme Chow Wanted results.
Sources: AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
Chow/FlatPullback and the normal-cone constructions (Apache 2.0).
The Rees algebra is Mathlib's actual subalgebra of A[t], Andrew Yang (2022),
56a005855ea17e0b0958f73ec801ae140b0a1679, Apache 2.0.
Refined Gysin compatibility additionally requires the canonical normal-cone
embedding and inverse bundle pullback; proper-intersection Tor formulas
alone do not specify an operational class in excess intersections.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.IntegralOperationalChow

open CategoryTheory CategoryTheory.Limits IntegerSchemeChow StackCycleGeometry
open scoped TensorProduct

variable {k : Type} [Field k]

structure TestScheme (X : FieldScheme k) where
  source : FieldScheme k
  map : source.scheme ⟶ X.scheme

universe u in
/-- The coordinates of an algebraic cycle on a Noetherian scheme (of any universe), as a
finitely supported function. -/
def cycleCoordinates (X : Scheme.{u}) [IsNoetherian X] :
    AlgebraicCycle X ℤ →ₗ[ℤ] (X →₀ ℤ) where
  toFun c := Finsupp.ofSupportFinite c c.finite_support
  map_add' a b := by ext x; rfl
  map_smul' a c := by ext x; rfl

def flatBasis {X Y : FieldScheme k} (f : Y.scheme ⟶ X.scheme)
    (d r : ℤ) (x : X.scheme.left) : CycleGroup Y.scheme.left (d + r) :=
  dimensionPart Y.scheme.left (d + r)
    (AlgebraicCycle.map (MathlibExt.AlgebraicGeometry.GeometricChowOperators.fiberInclusion
      f.left x) Order.height Order.height
      (integralFundamentalCycle
        (MathlibExt.AlgebraicGeometry.GeometricChowOperators.pointFiber f.left x)))

def flatCycleMap {X Y : FieldScheme k} (f : Y.scheme ⟶ X.scheme) (d r : ℤ) :
    CycleGroup X.scheme.left d →ₗ[ℤ] CycleGroup Y.scheme.left (d + r) :=
  (Finsupp.linearCombination ℤ (flatBasis f d r)).comp
    ((cycleCoordinates X.scheme.left).comp
      (cyclesOfDimension X.scheme.left d).subtype.toIntLinearMap)

/-- Purity is a geometric fibre condition, not an output-degree label. -/
def PureRelativeDimension {X Y : FieldScheme k} (f : Y.scheme ⟶ X.scheme) (r : ℕ) : Prop :=
  ∀ x : X.scheme.left,
    let Q : Scheme := pullback f.left (X.scheme.left.fromSpecResidueField x)
    ∀ (Z : Set Q), Z ∈ irreducibleComponents Q →
      topologicalKrullDim Z = (r : ℕ)

abbrev NormalRing (A : Type) [CommRing A] (I : Ideal A) :=
  (A ⧸ I) ⊗[A] reesAlgebra I

/-- The field-scheme wrapper retains the full coefficient/degree-one and
restriction-normalized geometric model, together with its actual base map. -/
structure NormalConeModel {Z Y : FieldScheme k} (i : Z.scheme ⟶ Y.scheme)
    [IsClosedImmersion i.left] where
  geometric : MathlibExt.AlgebraicGeometry.SchemeNormalConeCharts.NormalConeModel i.left
  cone : FieldScheme k
  projection : cone.scheme ⟶ Z.scheme
  identifies : cone.scheme.left ≅ geometric.cone
  projection_normalized : identifies.hom ≫ geometric.projection = projection.left

/-- Ordinary source-proved maps, normalized on every actual cycle. -/
structure CycleOperations where
  proper : ∀ {X Y : FieldScheme k} (f : X.scheme ⟶ Y.scheme)
    [IsProper f.left] (d : ℤ), ChowGroup X d →+ ChowGroup Y d
  proper_cycle : ∀ {X Y : FieldScheme k} (f : X.scheme ⟶ Y.scheme)
    [IsProper f.left] (d : ℤ) (c : CycleGroup X.scheme.left d),
    proper f d (cycleClass X d c) = cycleClass Y d
      (dimensionPart Y.scheme.left d (AlgebraicCycle.map f.left Order.height Order.height c.val))
  flat : ∀ {X Y : FieldScheme k} (f : Y.scheme ⟶ X.scheme)
    [Flat f.left] (r : ℕ), PureRelativeDimension f r →
      ∀ d : ℤ, ChowGroup X d →+ ChowGroup Y (d + r)
  flat_cycle : ∀ {X Y : FieldScheme k} (f : Y.scheme ⟶ X.scheme)
    [Flat f.left] (r : ℕ) (hr : PureRelativeDimension f r)
    (d : ℤ) (c : CycleGroup X.scheme.left d),
    flat f r hr d (cycleClass X d c) =
      cycleClass Y (d + r) (flatCycleMap f d r c)

end AlgebraicGeometry.IntegralOperationalChow
