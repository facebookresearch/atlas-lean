/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.BrauerZeroCycles

/-!
# Zero-cycle Brauer evaluation endpoints

Integer coordinates on dimension-zero points are faithful, and the
evaluation of the cycle `n · [x]` is `n` times the residue evaluation at `x`,
including through any Chow descent. The norm cokernel map is surjective and
kills norms. The identity base-change square of a field scheme is an actual
`CartesianFieldExtension`.
-/

noncomputable section

namespace MathlibExtTest.BrauerZeroCycles

open CategoryTheory
open AlgebraicGeometry.BrauerCoefficients AlgebraicGeometry.BrauerEvaluation
  AlgebraicGeometry.BrauerInteroperability AlgebraicGeometry.IntegerSchemeChow
  AlgebraicGeometry.BrauerZeroCycles
open AlgebraicGeometry (Scheme Spec AlgebraicCycle)

variable {k : Type} [Field k] (X : FieldScheme k)

/-! ## Coordinates -/

example (c : CycleGroup X.scheme.left 0) (x : ZeroPoint X) :
    cycleCoordinates X c x = c.val x.val := rfl

/-- Coordinates on zero-dimensional points are faithful. -/
example : Function.Injective (cycleCoordinates X) := by
  intro c d h
  apply Subtype.ext
  ext x
  by_cases hx : PointDimension X.scheme.left x 0
  · exact DFunLike.congr_fun h ⟨x, hx⟩
  · have hc : c.val x = 0 := by
      by_contra hc
      exact hx (c.2 x hc)
    have hd : d.val x = 0 := by
      by_contra hd
      exact hx (d.2 x hd)
    rw [hc, hd]

/-- The cycle `n · [x]` at a dimension-zero point. -/
def pointCycle (x : ZeroPoint X) (n : ℤ) : CycleGroup X.scheme.left 0 := by
  classical
  exact ⟨Function.locallyFinsuppWithin.single x.val n, fun y hy => by
    by_cases h : y = x.val
    · exact h ▸ x.2
    · simp [h] at hy⟩

theorem cycleCoordinates_pointCycle (x : ZeroPoint X) (n : ℤ) :
    cycleCoordinates X (pointCycle X x n) = Finsupp.single x n := by
  classical
  ext y
  by_cases h : y = x
  · subst h
    simp [cycleCoordinates, pointCycle]
  · have h' : y.val ≠ x.val := fun e => h (Subtype.ext e)
    simp [cycleCoordinates, pointCycle, h', Ne.symm h]

/-! ## Evaluation -/

variable (B : FieldComparisonFamily) (D : ∀ x : ZeroPoint X, ResidueFieldData X x)
  (a : Brauer X.scheme.left)

theorem cycleEvaluation_pointCycle (x : ZeroPoint X) (n : ℤ) :
    cycleEvaluation X B D a (pointCycle X x n) = n • residueEvaluation X B D a x := by
  simp only [cycleEvaluation, AddMonoidHom.coe_comp, Function.comp_apply,
    cycleCoordinates_pointCycle, LinearMap.toAddMonoidHom_coe, Finsupp.linearCombination_single]
  -- The module structure of `Br k` is the category's, not definitionally `zsmul`.
  exact int_smul_eq_zsmul _ _ _

example : cycleEvaluation X B D a 0 = 0 := map_zero _

example (f : ChowEvaluation X B D a) (x : ZeroPoint X) (n : ℤ) :
    f.val (cycleClass X 0 (pointCycle X x n)) = n • residueEvaluation X B D a x := by
  rw [f.2, cycleEvaluation_pointCycle]

example (f : ChowEvaluation X B D a) (c : CycleGroup X.scheme.left 0)
    (hc : IsPrincipalRelation X.scheme.left 0 c) : cycleEvaluation X B D a c = 0 := by
  have h0 : cycleClass X 0 c = 0 :=
    (QuotientAddGroup.eq_zero_iff c).mpr (AddSubgroup.subset_closure hc)
  rw [← f.2, h0, map_zero]

/-! ## Norms and completion -/

section Norm

variable {l : Type} [Field l] (Y : FieldScheme l) (i : k →+* l)
  (E : CartesianFieldExtension X Y i) (N : NormalizedNorm X Y i E)

example : Function.Surjective (normQuotientMap X Y i E N) := QuotientAddGroup.mk'_surjective _

example (y : ChowGroup Y 0) : normQuotientMap X Y i E N (N.val y) = 0 :=
  (QuotientAddGroup.eq_zero_iff _).mpr ⟨y, rfl⟩

example (c : CycleGroup Y.scheme.left 0) :
    normQuotientMap X Y i E N (cycleClass X 0 (dimensionPart X.scheme.left 0
      (AlgebraicCycle.map E.map Order.height Order.height c.val))) = 0 := by
  rw [← N.2 c]
  exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨_, rfl⟩

example (q : NormQuotient X Y i E N) (n : AlgebraicGeometry.BrauerArithmeticCompletion.Modulus) :
    AlgebraicGeometry.BrauerArithmeticCompletion.projection _ n
      (AlgebraicGeometry.BrauerArithmeticCompletion.unit (NormQuotient X Y i E N) q :
        CompletedNormQuotient X Y i E N) = QuotientAddGroup.mk q := rfl

end Norm

/-- The identity base-change square is cartesian, along the finite extension `k = k`. -/
def identityExtension : CartesianFieldExtension X X (RingHom.id k) where
  map := 𝟙 _
  cartesian := by
    rw [CommRingCat.ofHom_id, AlgebraicGeometry.Spec.map_id]
    exact IsPullback.of_id_fst
  finite := RingHom.Finite.id k

example (c : CycleGroup X.scheme.left 0)
    (n : AlgebraicGeometry.BrauerArithmeticCompletion.Modulus) :
    AlgebraicGeometry.BrauerArithmeticCompletion.projection _ n
      (AlgebraicGeometry.BrauerArithmeticCompletion.unit (ChowGroup X 0) (cycleClass X 0 c) :
        CompletedChow X) = QuotientAddGroup.mk (cycleClass X 0 c) := rfl

end MathlibExtTest.BrauerZeroCycles
