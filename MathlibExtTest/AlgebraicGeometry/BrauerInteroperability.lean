/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.BrauerZeroCycles
import Mathlib.Tactic.NormNum

/-!
# Brauer cocycle and invariant regression

The cyclic group of order two has a nonconstant homogeneous one-cochain
`a(g,h)=0` for `g=h`, and `1` otherwise. Its native two-boundary has
inhomogeneous value `2` at `(s,s)` and `0` at `(s,1)`, yet its native class is
zero. In particular the `(1,g,g*h)` normalization is observable.

The local invariant probes distinguish degree-two annihilation from
degree-three scaling and the two possible signs at degree three. Completion
is checked on an actual integer class reduced to `ZMod 6`.
-/

noncomputable section

namespace MathlibExtTest.BrauerInteroperability

open CategoryTheory ContRepresentation
open AlgebraicGeometry.BrauerCoefficients
open AlgebraicGeometry.BrauerArithmeticCompletion
open AlgebraicGeometry.BrauerEvaluation AlgebraicGeometry.BrauerInteroperability
open AlgebraicGeometry.BrauerLocalInvariant

private abbrev G := Multiplicative (ZMod 2)

private instance : TopologicalSpace G := ⊥
private instance : DiscreteTopology G := ⟨rfl⟩
private instance : IsTopologicalGroup G := inferInstance

private def trivialRep : TopRep ℤ G :=
  TopRep.of (ContRepresentation.trivial ℤ G ℤ)

private def oneCochain : (TopRep.homogeneousCochains trivialRep).X 1 :=
  ⟨⟨fun g => ⟨fun h => if g = h then (0 : ℤ) else (1 : ℤ),
      continuous_of_discreteTopology⟩, continuous_of_discreteTopology⟩, by
    intro g
    ext x y
    change (if g⁻¹ * x = g⁻¹ * y then (0 : ℤ) else 1) =
      (if x = y then (0 : ℤ) else 1)
    simp only [mul_left_cancel_iff]⟩

private def boundary : ContinuousCohomology.cocycles trivialRep 2 :=
  (TopRep.homogeneousCochains trivialRep).toCycles 1 2 oneCochain

private def boundaryValue (g h : G) : ℤ :=
  inhomogeneousTwoCocycleValue trivialRep boundary g h

private theorem boundary_inclusion :
    (TopRep.homogeneousCochains trivialRep).iCycles 2 boundary =
      ((TopRep.homogeneousCochains trivialRep).d 1 2) oneCochain :=
  ConcreteCategory.congr_hom
    ((TopRep.homogeneousCochains trivialRep).toCycles_i 1 2) oneCochain

private theorem boundary_formula (g h : G) :
    boundaryValue g h =
      (if g = g * h then (0 : ℤ) else 1) -
        ((if (1 : G) = g * h then (0 : ℤ) else 1) -
          (if (1 : G) = g then (0 : ℤ) else 1)) := by
  rw [boundaryValue, inhomogeneousTwoCocycleValue, boundary_inclusion,
    TopRep.homogeneousCochains.d_apply]
  rfl

example : boundaryValue (Multiplicative.ofAdd (1 : ZMod 2))
    (Multiplicative.ofAdd (1 : ZMod 2)) = 2 := by
  rw [boundary_formula]
  decide

example : boundaryValue (Multiplicative.ofAdd (1 : ZMod 2)) 1 = 0 := by
  rw [boundary_formula]
  decide

example : ContinuousCohomology.π trivialRep 2 boundary = 0 :=
  ConcreteCategory.congr_hom
    ((TopRep.homogeneousCochains trivialRep).toCycles_comp_homologyπ 1 2) oneCochain

example : invariantRestriction 2 ((1 / 2 : ℚ) : InvariantTarget) = 0 := by
  rw [invariantRestriction_apply, ← AddCircle.coe_nsmul]
  exact (AddCircle.coe_eq_zero_iff (1 : ℚ)).mpr ⟨1, by norm_num⟩

example : invariantRestriction 2 ((1 / 3 : ℚ) : InvariantTarget) =
    ((2 / 3 : ℚ) : InvariantTarget) := by
  rw [invariantRestriction_apply, ← AddCircle.coe_nsmul]
  congr 1
  norm_num

example : ((1 / 3 : ℚ) : InvariantTarget) ≠ ((2 / 3 : ℚ) : InvariantTarget) := by
  intro h
  have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (by norm_num : (1 / 3 : ℚ) ∈ Set.Ico 0 (0 + 1))
    (by norm_num : (2 / 3 : ℚ) ∈ Set.Ico 0 (0 + 1))).mp h
  norm_num at heq

/-- A third-order actual cocycle cannot retain normalization after negating
the geometric comparison. Its geometric class is supplied by the same provider. -/
example (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (B : FieldGmComparison K)
    (I : NormalizedLocalInvariant K) (c : TwoCocycles K)
    (hc : I.val (cocycleClass K c) = ((1 / 3 : ℚ) : InvariantTarget)) :
    -(fieldComparison K B (fieldGeometricClass K B c)) ≠ cocycleClass K c := by
  apply geometric_normalization_rejects_negation K B c (B.realization c)
  intro h
  have hi := congrArg I.val h
  rw [map_nsmul, map_zero, hc] at hi
  have hthird : 2 • ((1 / 3 : ℚ) : InvariantTarget) =
      ((2 / 3 : ℚ) : InvariantTarget) := by
    rw [← AddCircle.coe_nsmul]
    congr 1
    norm_num
  rw [hthird] at hi
  have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (by norm_num : (2 / 3 : ℚ) ∈ Set.Ico 0 (0 + 1))
    (by norm_num : (0 : ℚ) ∈ Set.Ico 0 (0 + 1))).mp hi
  norm_num at heq

private def reduceSix : ℤ →+ ZMod 6 := Int.castAddHom _

private theorem reduceSix_killed (a : ℤ) : 6 • reduceSix a = 0 := by
  have hz : (6 : ZMod 6) = 0 := by decide
  simp [reduceSix, nsmul_eq_mul, hz]

example : completedEvaluation ℤ reduceSix ⟨6, by decide⟩ reduceSix_killed
    (unit ℤ 37) = (1 : ZMod 6) := by
  rw [completedEvaluation_unit]
  decide

/-- The identity is a compatible coefficient pair for a field over itself, so the structure is
not vacuous. -/
def identityPair (K : Type) [Field K] :
    FieldCoefficientPair (K := K) K (ContinuousMonoidHom.id _) where
  embedding := RingHom.id _
  base _ := rfl
  equivariant _ _ := rfl

-- Its unit map is the identity.
example (K : Type) [Field K] (u : SepUnits K) :
    unitsMap K (ContinuousMonoidHom.id _) (identityPair K) u = u := rfl

-- Restriction along a coefficient pair is computed on actual cocycles.
example (K : Type) [Field K] (c : TwoCocycles K) :
    AlgebraicGeometry.BrauerInteroperability.restriction K (ContinuousMonoidHom.id _)
        (identityPair K) (cocycleClass K c) =
      cocycleClass K (restrictCocycle K (ContinuousMonoidHom.id _) (identityPair K) c) :=
  restriction_cocycleClass K _ _ c

-- Restriction along the identity pair keeps the inhomogeneous values (`restrictCocycle_values`).
example (K : Type) [Field K] (c : TwoCocycles K) (g h : Field.absoluteGaloisGroup K) :
    inhomogeneousValue K (restrictCocycle K (ContinuousMonoidHom.id _) (identityPair K) c) g h =
      inhomogeneousValue K c g h :=
  restrictCocycle_values K _ _ c g h

-- Evaluation at a field point is pullback followed by the field comparison.
example (K : Type) [Field K] (B : FieldGmComparison K) {X : AlgebraicGeometry.Scheme.{0}}
    (p : AlgebraicGeometry.Spec (.of K) ⟶ X) (a : GmH2 X) :
    evaluate K B p a = B.val (pointPullback K p a) := evaluate_apply K B p a

#print axioms AlgebraicGeometry.BrauerCoefficients.unitsRepContinuousSMul
#print axioms AlgebraicGeometry.BrauerInteroperability.restriction_cocycleClass
#print axioms AlgebraicGeometry.BrauerEvaluation.pullback_comp
#print axioms DiscreteGModules.abelian
#print axioms DiscreteGModules.axiomDerivedCohomology
#print axioms AlgebraicGeometry.BrauerEvaluation.geometricCechClass
#print axioms AlgebraicGeometry.BrauerEvaluation.unitSectionMap
#print axioms AlgebraicGeometry.BrauerInteroperability.geometric_normalization_rejects_negation

end MathlibExtTest.BrauerInteroperability
