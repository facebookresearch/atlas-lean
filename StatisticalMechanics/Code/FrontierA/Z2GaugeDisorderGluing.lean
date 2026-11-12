/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















import Code.FrontierA.IsingSurfaceTensionThermodynamic

open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.flexible false
set_option linter.style.multiGoal false

namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]



theorem multibondIsingAction_coupling_sub_abs_le
    (ends : P → V × V) (J J' : P → Real) (s : V → Bool) :
    |multibondIsingAction ends J s - multibondIsingAction ends J' s| ≤
      ∑ p : P, |J p - J' p| := by
  classical
  unfold multibondIsingAction
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ p : P, (
        (J p * if s (ends p).1 = s (ends p).2 then 1 else -1) -
          J' p * if s (ends p).1 = s (ends p).2 then 1 else -1)|
        ≤ ∑ p : P, |(
            (J p * if s (ends p).1 = s (ends p).2 then 1 else -1) -
              J' p * if s (ends p).1 = s (ends p).2 then 1 else -1)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ p : P, |J p - J' p| := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hs : s (ends p).1 = s (ends p).2
      · simp [hs]
      · simp [hs]
        have hneg : -J p + J' p = -(J p - J' p) := by ring
        rw [hneg, abs_neg]



theorem multibondIsing_logPartition_coupling_sub_abs_le
    (ends : P → V × V) (J J' : P → Real) :
    |Real.log (multibondIsingPartition ends J) -
        Real.log (multibondIsingPartition ends J')| ≤
      ∑ p : P, |J p - J' p| := by
  rw [multibondIsingPartition_eq_Z_neg_one,
    multibondIsingPartition_eq_Z_neg_one]
  simpa using StatMech.Ising.logZ_dist_le (-1)
    (multibondIsingAction ends J) (multibondIsingAction ends J')
    (∑ p : P, |J p - J' p|)
    (multibondIsingAction_coupling_sub_abs_le ends J J')



theorem abs_multibondTwistCoupling_sub
    (J J' : P → Real) (D : Finset P) (p : P) :
    |multibondTwistCoupling J D p - multibondTwistCoupling J' D p| =
      |J p - J' p| := by
  by_cases hp : p ∈ D
  · rw [multibondTwistCoupling_apply_mem J D hp,
      multibondTwistCoupling_apply_mem J' D hp]
    have hneg : -J p - -J' p = -(J p - J' p) := by ring
    rw [hneg, abs_neg]
  · simp [multibondTwistCoupling, hp]




theorem multibondDisorderFreeEnergy_coupling_sub_abs_le
    (ends : P → V × V) (J J' : P → Real) (D : Finset P) :
    |multibondDisorderFreeEnergy ends J D -
        multibondDisorderFreeEnergy ends J' D| ≤
      2 * ∑ p : P, |J p - J' p| := by
  let A := Real.log (multibondIsingPartition ends J)
  let B := Real.log
    (multibondIsingPartition ends (multibondTwistCoupling J D))
  let A' := Real.log (multibondIsingPartition ends J')
  let B' := Real.log
    (multibondIsingPartition ends (multibondTwistCoupling J' D))
  have hordinary : |A - A'| ≤ ∑ p : P, |J p - J' p| :=
    multibondIsing_logPartition_coupling_sub_abs_le ends J J'
  have htwisted : |B - B'| ≤ ∑ p : P, |J p - J' p| := by
    have h := multibondIsing_logPartition_coupling_sub_abs_le ends
      (multibondTwistCoupling J D) (multibondTwistCoupling J' D)
    simpa only [abs_multibondTwistCoupling_sub] using h
  unfold multibondDisorderFreeEnergy
  change |(A - B) - (A' - B')| ≤ _
  calc
    |(A - B) - (A' - B')| = |(A - A') - (B - B')| := by ring_nf
    _ ≤ |A - A'| + |B - B'| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (A - A') (-(B - B'))
    _ ≤ (∑ p : P, |J p - J' p|) + ∑ p : P, |J p - J' p| :=
      add_le_add hordinary htwisted
    _ = 2 * ∑ p : P, |J p - J' p| := by ring


def eraseMultibondCouplings (J : P → Real) (S : Finset P) : P → Real :=
  fun p => if p ∈ S then 0 else J p



theorem sum_abs_sub_eraseMultibondCouplings
    (J : P → Real) (S : Finset P) :
    (∑ p : P, |J p - eraseMultibondCouplings J S p|) =
      ∑ p ∈ S, |J p| := by
  classical
  calc
    (∑ p : P, |J p - eraseMultibondCouplings J S p|) =
        ∑ p : P, if p ∈ S then |J p| else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : p ∈ S <;> simp [eraseMultibondCouplings, hp]
    _ = ∑ p ∈ S, |J p| := by
      rw [← Finset.sum_filter]
      simp only [subset_univ, filter_mem_eq_of_subset]



theorem multibondDisorderFreeEnergy_eraseSeam_sub_abs_le
    (ends : P → V × V) (J : P → Real) (D S : Finset P) :
    |multibondDisorderFreeEnergy ends J D -
        multibondDisorderFreeEnergy ends
          (eraseMultibondCouplings J S) D| ≤
      2 * ∑ p ∈ S, |J p| := by
  simpa only [sum_abs_sub_eraseMultibondCouplings] using
    multibondDisorderFreeEnergy_coupling_sub_abs_le ends J
      (eraseMultibondCouplings J S) D




theorem multibondDisorderFreeEnergy_le_blockCost_add_seam
    (ends : P → V × V) (J : P → Real) (D S : Finset P)
    (blockCost : Real)
    (hblock : multibondDisorderFreeEnergy ends
      (eraseMultibondCouplings J S) D ≤ blockCost) :
    multibondDisorderFreeEnergy ends J D ≤
      blockCost + 2 * ∑ p ∈ S, |J p| := by
  have hdist := multibondDisorderFreeEnergy_eraseSeam_sub_abs_le ends J D S
  have hone := le_trans (le_abs_self
    (multibondDisorderFreeEnergy ends J D -
      multibondDisorderFreeEnergy ends (eraseMultibondCouplings J S) D)) hdist
  linarith



theorem multibondDisorderFreeEnergy_eraseSeam_homogeneous_sub_abs_le
    (ends : P → V × V) (J : Real) (D S : Finset P) :
    |multibondDisorderFreeEnergy ends (fun _ => J) D -
        multibondDisorderFreeEnergy ends
          (eraseMultibondCouplings (fun _ => J) S) D| ≤
      2 * S.card * |J| := by
  simpa [Finset.sum_const, nsmul_eq_mul, mul_assoc] using
    multibondDisorderFreeEnergy_eraseSeam_sub_abs_le ends
      (fun _ => J) D S



theorem cubicalDisorderFreeEnergy_eraseSeam_sub_abs_le
    {a b c : Nat} {beta : Real} (hbeta : 0 < beta)
    (D S : Finset (CubicalPlaquette a b c)) :
    |multibondDisorderFreeEnergy cubicalDualEnds
          (fun _ => gaugeDualCoupling beta) D -
        multibondDisorderFreeEnergy cubicalDualEnds
          (eraseMultibondCouplings (fun _ => gaugeDualCoupling beta) S) D| ≤
      2 * S.card * gaugeDualCoupling beta := by
  have hdual := gaugeDualCoupling_pos hbeta
  simpa [abs_of_pos hdual] using
    multibondDisorderFreeEnergy_eraseSeam_homogeneous_sub_abs_le
      cubicalDualEnds (gaugeDualCoupling beta) D S

section DisjointBlocks

variable {P₁ P₂ V₁ V₂ : Type*}
  [Fintype P₁] [DecidableEq P₁] [Fintype P₂] [DecidableEq P₂]
  [Fintype V₁] [DecidableEq V₁] [Fintype V₂] [DecidableEq V₂]


def multibondSumEnds (ends₁ : P₁ → V₁ × V₁) (ends₂ : P₂ → V₂ × V₂) :
    P₁ ⊕ P₂ → (V₁ ⊕ V₂) × (V₁ ⊕ V₂)
  | .inl p => (.inl (ends₁ p).1, .inl (ends₁ p).2)
  | .inr p => (.inr (ends₂ p).1, .inr (ends₂ p).2)


def multibondSumCoupling (J₁ : P₁ → Real) (J₂ : P₂ → Real) :
    P₁ ⊕ P₂ → Real :=
  Sum.elim J₁ J₂


def multibondSumSheet (D₁ : Finset P₁) (D₂ : Finset P₂) : Finset (P₁ ⊕ P₂) :=
  D₁.disjSum D₂


theorem multibondIsingAction_sum
    (ends₁ : P₁ → V₁ × V₁) (ends₂ : P₂ → V₂ × V₂)
    (J₁ : P₁ → Real) (J₂ : P₂ → Real)
    (s₁ : V₁ → Bool) (s₂ : V₂ → Bool) :
    multibondIsingAction (multibondSumEnds ends₁ ends₂)
        (multibondSumCoupling J₁ J₂)
        ((Equiv.sumArrowEquivProdArrow V₁ V₂ Bool).symm (s₁, s₂)) =
      multibondIsingAction ends₁ J₁ s₁ +
        multibondIsingAction ends₂ J₂ s₂ := by
  unfold multibondIsingAction
  rw [Fintype.sum_sum_type]
  congr 1


theorem multibondIsingWeight_sum
    (ends₁ : P₁ → V₁ × V₁) (ends₂ : P₂ → V₂ × V₂)
    (J₁ : P₁ → Real) (J₂ : P₂ → Real)
    (s₁ : V₁ → Bool) (s₂ : V₂ → Bool) :
    multibondIsingWeight (multibondSumEnds ends₁ ends₂)
        (multibondSumCoupling J₁ J₂)
        ((Equiv.sumArrowEquivProdArrow V₁ V₂ Bool).symm (s₁, s₂)) =
      multibondIsingWeight ends₁ J₁ s₁ *
        multibondIsingWeight ends₂ J₂ s₂ := by
  change Real.exp (multibondIsingAction (multibondSumEnds ends₁ ends₂)
      (multibondSumCoupling J₁ J₂)
      ((Equiv.sumArrowEquivProdArrow V₁ V₂ Bool).symm (s₁, s₂))) =
    Real.exp (multibondIsingAction ends₁ J₁ s₁) *
      Real.exp (multibondIsingAction ends₂ J₂ s₂)
  rw [multibondIsingAction_sum, Real.exp_add]


theorem multibondIsingPartition_sum
    (ends₁ : P₁ → V₁ × V₁) (ends₂ : P₂ → V₂ × V₂)
    (J₁ : P₁ → Real) (J₂ : P₂ → Real) :
    multibondIsingPartition (multibondSumEnds ends₁ ends₂)
        (multibondSumCoupling J₁ J₂) =
      multibondIsingPartition ends₁ J₁ *
        multibondIsingPartition ends₂ J₂ := by
  unfold multibondIsingPartition
  rw [← Equiv.sum_comp (Equiv.sumArrowEquivProdArrow V₁ V₂ Bool).symm]
  rw [Fintype.sum_prod_type]
  simp_rw [multibondIsingWeight_sum]
  rw [Finset.sum_mul_sum]



theorem multibondTwistCoupling_sum
    (J₁ : P₁ → Real) (J₂ : P₂ → Real)
    (D₁ : Finset P₁) (D₂ : Finset P₂) :
    multibondTwistCoupling (multibondSumCoupling J₁ J₂)
        (multibondSumSheet D₁ D₂) =
      multibondSumCoupling (multibondTwistCoupling J₁ D₁)
        (multibondTwistCoupling J₂ D₂) := by
  funext p
  cases p <;> simp [multibondTwistCoupling, multibondSumCoupling,
    multibondSumSheet]



theorem multibondDisorderFreeEnergy_sum
    (ends₁ : P₁ → V₁ × V₁) (ends₂ : P₂ → V₂ × V₂)
    (J₁ : P₁ → Real) (J₂ : P₂ → Real)
    (D₁ : Finset P₁) (D₂ : Finset P₂) :
    multibondDisorderFreeEnergy (multibondSumEnds ends₁ ends₂)
        (multibondSumCoupling J₁ J₂) (multibondSumSheet D₁ D₂) =
      multibondDisorderFreeEnergy ends₁ J₁ D₁ +
        multibondDisorderFreeEnergy ends₂ J₂ D₂ := by
  unfold multibondDisorderFreeEnergy
  rw [multibondIsingPartition_sum]
  rw [multibondTwistCoupling_sum]
  rw [multibondIsingPartition_sum]
  rw [Real.log_mul
    (multibondIsingPartition_pos ends₁ J₁).ne'
    (multibondIsingPartition_pos ends₂ J₂).ne']
  rw [Real.log_mul
    (multibondIsingPartition_pos ends₁ (multibondTwistCoupling J₁ D₁)).ne'
    (multibondIsingPartition_pos ends₂ (multibondTwistCoupling J₂ D₂)).ne']
  ring

end DisjointBlocks

section RootedBlocks

variable {P₁ P₂ V₁ V₂ : Type*}
  [Fintype P₁] [DecidableEq P₁] [Fintype P₂] [DecidableEq P₂]
  [Fintype V₁] [DecidableEq V₁] [Fintype V₂] [DecidableEq V₂]



def rootedSumInl : Option V₁ → Option (V₁ ⊕ V₂)
  | none => none
  | some v => some (.inl v)


def rootedSumInr : Option V₂ → Option (V₁ ⊕ V₂)
  | none => none
  | some v => some (.inr v)


def multibondRootedSumEnds
    (ends₁ : P₁ → Option V₁ × Option V₁)
    (ends₂ : P₂ → Option V₂ × Option V₂) :
    P₁ ⊕ P₂ → Option (V₁ ⊕ V₂) × Option (V₁ ⊕ V₂)
  | .inl p => (rootedSumInl (ends₁ p).1, rootedSumInl (ends₁ p).2)
  | .inr p => (rootedSumInr (ends₂ p).1, rootedSumInr (ends₂ p).2)



def rootedSumAnchoredEquiv :
    AnchoredConfig (Option (V₁ ⊕ V₂)) none ≃
      AnchoredConfig (Option V₁) none × AnchoredConfig (Option V₂) none where
  toFun s :=
    (⟨fun q => s.1 (rootedSumInl q), by simpa [rootedSumInl] using s.2⟩,
      ⟨fun q => s.1 (rootedSumInr q), by simpa [rootedSumInr] using s.2⟩)
  invFun st := ⟨fun q => match q with
    | none => false
    | some (.inl v) => st.1.1 (some v)
    | some (.inr v) => st.2.1 (some v), rfl⟩
  left_inv s := by
    apply Subtype.ext
    funext q
    cases q with
    | none => simpa using s.2.symm
    | some q => cases q <;> rfl
  right_inv st := by
    rcases st with ⟨s₁, s₂⟩
    apply Prod.ext
    · apply Subtype.ext
      funext q
      cases q with
      | none => exact s₁.2.symm
      | some v => rfl
    · apply Subtype.ext
      funext q
      cases q with
      | none => exact s₂.2.symm
      | some v => rfl

@[simp] theorem rootedSumAnchoredEquiv_symm_apply_inl
    (s₁ : AnchoredConfig (Option V₁) none)
    (s₂ : AnchoredConfig (Option V₂) none) (q : Option V₁) :
    ((rootedSumAnchoredEquiv (V₁ := V₁) (V₂ := V₂)).symm (s₁, s₂)).1
        (rootedSumInl q) = s₁.1 q := by
  cases q <;> simp [rootedSumAnchoredEquiv, rootedSumInl, s₁.2]

@[simp] theorem rootedSumAnchoredEquiv_symm_apply_inr
    (s₁ : AnchoredConfig (Option V₁) none)
    (s₂ : AnchoredConfig (Option V₂) none) (q : Option V₂) :
    ((rootedSumAnchoredEquiv (V₁ := V₁) (V₂ := V₂)).symm (s₁, s₂)).1
        (rootedSumInr q) = s₂.1 q := by
  cases q <;> simp [rootedSumAnchoredEquiv, rootedSumInr, s₂.2]



theorem multibondIsingAction_rootedSum
    (ends₁ : P₁ → Option V₁ × Option V₁)
    (ends₂ : P₂ → Option V₂ × Option V₂)
    (J₁ : P₁ → Real) (J₂ : P₂ → Real)
    (s₁ : AnchoredConfig (Option V₁) none)
    (s₂ : AnchoredConfig (Option V₂) none) :
    multibondIsingAction (multibondRootedSumEnds ends₁ ends₂)
        (multibondSumCoupling J₁ J₂)
        ((rootedSumAnchoredEquiv (V₁ := V₁) (V₂ := V₂)).symm (s₁, s₂)).1 =
      multibondIsingAction ends₁ J₁ s₁.1 +
        multibondIsingAction ends₂ J₂ s₂.1 := by
  unfold multibondIsingAction
  rw [Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro p _
    simp only [multibondRootedSumEnds, multibondSumCoupling, Sum.elim_inl,
      rootedSumAnchoredEquiv_symm_apply_inl]
  · apply Finset.sum_congr rfl
    intro p _
    simp only [multibondRootedSumEnds, multibondSumCoupling, Sum.elim_inr,
      rootedSumAnchoredEquiv_symm_apply_inr]


theorem multibondIsingWeight_rootedSum
    (ends₁ : P₁ → Option V₁ × Option V₁)
    (ends₂ : P₂ → Option V₂ × Option V₂)
    (J₁ : P₁ → Real) (J₂ : P₂ → Real)
    (s₁ : AnchoredConfig (Option V₁) none)
    (s₂ : AnchoredConfig (Option V₂) none) :
    multibondIsingWeight (multibondRootedSumEnds ends₁ ends₂)
        (multibondSumCoupling J₁ J₂)
        ((rootedSumAnchoredEquiv (V₁ := V₁) (V₂ := V₂)).symm (s₁, s₂)).1 =
      multibondIsingWeight ends₁ J₁ s₁.1 *
        multibondIsingWeight ends₂ J₂ s₂.1 := by
  change Real.exp (multibondIsingAction (multibondRootedSumEnds ends₁ ends₂)
      (multibondSumCoupling J₁ J₂)
      ((rootedSumAnchoredEquiv (V₁ := V₁) (V₂ := V₂)).symm (s₁, s₂)).1) =
    Real.exp (multibondIsingAction ends₁ J₁ s₁.1) *
      Real.exp (multibondIsingAction ends₂ J₂ s₂.1)
  rw [multibondIsingAction_rootedSum, Real.exp_add]


theorem multibondIsingPartition_eq_two_mul_anchoredWeight
    {Q W : Type*} [Fintype Q] [DecidableEq Q] [Fintype W] [DecidableEq W]
    (root : W) (ends : Q → W × W) (J : Q → Real) :
    multibondIsingPartition ends J =
      2 * ∑ s : AnchoredConfig W root, multibondIsingWeight ends J s.1 := by
  rw [multibondIsingPartition_eq_two_mul_anchored]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  exact (multibondIsingWeight_eq_activity ends J s.1).symm



theorem two_mul_multibondIsingPartition_rootedSum
    (ends₁ : P₁ → Option V₁ × Option V₁)
    (ends₂ : P₂ → Option V₂ × Option V₂)
    (J₁ : P₁ → Real) (J₂ : P₂ → Real) :
    2 * multibondIsingPartition (multibondRootedSumEnds ends₁ ends₂)
        (multibondSumCoupling J₁ J₂) =
      multibondIsingPartition ends₁ J₁ *
        multibondIsingPartition ends₂ J₂ := by
  rw [multibondIsingPartition_eq_two_mul_anchoredWeight none]
  rw [← Equiv.sum_comp
    (rootedSumAnchoredEquiv (V₁ := V₁) (V₂ := V₂)).symm]
  rw [Fintype.sum_prod_type]
  simp_rw [multibondIsingWeight_rootedSum]
  rw [← Finset.sum_mul_sum]
  rw [multibondIsingPartition_eq_two_mul_anchoredWeight none,
    multibondIsingPartition_eq_two_mul_anchoredWeight none]
  ring




theorem multibondDisorderFreeEnergy_rootedSum
    (ends₁ : P₁ → Option V₁ × Option V₁)
    (ends₂ : P₂ → Option V₂ × Option V₂)
    (J₁ : P₁ → Real) (J₂ : P₂ → Real)
    (D₁ : Finset P₁) (D₂ : Finset P₂) :
    multibondDisorderFreeEnergy (multibondRootedSumEnds ends₁ ends₂)
        (multibondSumCoupling J₁ J₂) (multibondSumSheet D₁ D₂) =
      multibondDisorderFreeEnergy ends₁ J₁ D₁ +
        multibondDisorderFreeEnergy ends₂ J₂ D₂ := by
  have hordinary := two_mul_multibondIsingPartition_rootedSum
    ends₁ ends₂ J₁ J₂
  have htwisted := two_mul_multibondIsingPartition_rootedSum ends₁ ends₂
    (multibondTwistCoupling J₁ D₁) (multibondTwistCoupling J₂ D₂)
  rw [← multibondTwistCoupling_sum J₁ J₂ D₁ D₂] at htwisted
  have hordLog := congrArg Real.log hordinary
  have htwLog := congrArg Real.log htwisted
  rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0)
      (multibondIsingPartition_pos _ _).ne',
    Real.log_mul (multibondIsingPartition_pos ends₁ J₁).ne'
      (multibondIsingPartition_pos ends₂ J₂).ne'] at hordLog
  rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0)
      (multibondIsingPartition_pos _ _).ne',
    Real.log_mul
      (multibondIsingPartition_pos ends₁ (multibondTwistCoupling J₁ D₁)).ne'
      (multibondIsingPartition_pos ends₂ (multibondTwistCoupling J₂ D₂)).ne'] at htwLog
  unfold multibondDisorderFreeEnergy
  linarith

end RootedBlocks

end

end StatMech.FrontierA
