/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.QuantumIsingAlmostAdditive
import Code.FrontierA.QuantumIsingTrotterCylinder










open scoped BigOperators

namespace StatMech.FrontierA


noncomputable def quantumIsingOpenChainInteraction (L : Nat)
    (sigma : QuantumIsingChainConfig (L + 1)) : Real :=
  ∑ i : Fin L,
    quantumIsingSpinSign (sigma i.castSucc) *
      quantumIsingSpinSign (sigma i.succ)


def quantumIsingLeftBlock {A B : Nat} (sigma : QuantumIsingChainConfig (A + B)) :
    QuantumIsingChainConfig A :=
  fun i => sigma (Fin.castAdd B i)


def quantumIsingRightBlock {A B : Nat} (sigma : QuantumIsingChainConfig (A + B)) :
    QuantumIsingChainConfig B :=
  fun i => sigma (Fin.natAdd A i)

private def quantumIsingLeftSpatialBlock (L M : Nat)
    (sigma : QuantumIsingChainConfig (L + M + 2)) :
    QuantumIsingChainConfig (L + 1) :=
  fun i => sigma ⟨i.val, by omega⟩

private def quantumIsingRightSpatialBlock (L M : Nat)
    (sigma : QuantumIsingChainConfig (L + M + 2)) :
    QuantumIsingChainConfig (M + 1) :=
  fun i => sigma ⟨L + 1 + i.val, by omega⟩

private def quantumIsingSpatialSumEquiv (L M : Nat) :
    Fin (L + 1) ⊕ Fin (M + 1) ≃ Fin (L + M + 2) :=
  finSumFinEquiv.trans (finCongr (by omega))

private def quantumIsingSpatialJoin (L M : Nat)
    (sigma : QuantumIsingChainConfig (L + 1))
    (tau : QuantumIsingChainConfig (M + 1)) :
    QuantumIsingChainConfig (L + M + 2) :=
  fun i => (quantumIsingSpatialSumEquiv L M).symm i |>.elim sigma tau

@[simp] private theorem quantumIsingLeftSpatialBlock_join
    (L M : Nat) (sigma : QuantumIsingChainConfig (L + 1))
    (tau : QuantumIsingChainConfig (M + 1)) :
    quantumIsingLeftSpatialBlock L M
        (quantumIsingSpatialJoin L M sigma tau) = sigma := by
  funext i
  unfold quantumIsingLeftSpatialBlock quantumIsingSpatialJoin
  rw [show (⟨i.val, by omega⟩ : Fin (L + M + 2)) =
      quantumIsingSpatialSumEquiv L M (Sum.inl i) by
    apply Fin.ext
    simp [quantumIsingSpatialSumEquiv]]
  simp

@[simp] private theorem quantumIsingRightSpatialBlock_join
    (L M : Nat) (sigma : QuantumIsingChainConfig (L + 1))
    (tau : QuantumIsingChainConfig (M + 1)) :
    quantumIsingRightSpatialBlock L M
        (quantumIsingSpatialJoin L M sigma tau) = tau := by
  funext i
  unfold quantumIsingRightSpatialBlock quantumIsingSpatialJoin
  rw [show (⟨L + 1 + i.val, by omega⟩ : Fin (L + M + 2)) =
      quantumIsingSpatialSumEquiv L M (Sum.inr i) by
    apply Fin.ext
    simp [quantumIsingSpatialSumEquiv]]
  simp



private def quantumIsingSpatialPathEquiv (n L M : Nat) :
    (Fin n -> QuantumIsingChainConfig (L + M + 2)) ≃
      (Fin n -> QuantumIsingChainConfig (L + 1)) ×
        (Fin n -> QuantumIsingChainConfig (M + 1)) where
  toFun omega :=
    (fun k => quantumIsingLeftSpatialBlock L M (omega k),
      fun k => quantumIsingRightSpatialBlock L M (omega k))
  invFun omega := fun k => quantumIsingSpatialJoin L M (omega.1 k) (omega.2 k)
  left_inv omega := by
    funext k i
    obtain ⟨x, rfl⟩ := (quantumIsingSpatialSumEquiv L M).surjective i
    rcases x with i | j
    · simp only [quantumIsingSpatialJoin, Equiv.symm_apply_apply,
        Sum.elim_inl]
      unfold quantumIsingLeftSpatialBlock
      apply congrArg (omega k)
      apply Fin.ext
      simp [quantumIsingSpatialSumEquiv]
    · simp only [quantumIsingSpatialJoin, Equiv.symm_apply_apply,
        Sum.elim_inr]
      unfold quantumIsingRightSpatialBlock
      apply congrArg (omega k)
      apply Fin.ext
      simp [quantumIsingSpatialSumEquiv]
  right_inv omega := by
    apply Prod.ext
    · funext k
      exact quantumIsingLeftSpatialBlock_join L M (omega.1 k) (omega.2 k)
    · funext k
      exact quantumIsingRightSpatialBlock_join L M (omega.1 k) (omega.2 k)

private theorem quantumIsing_prod_spatial_add
    (L M : Nat) (f : Fin (L + M + 2) -> Real) :
    (∏ i : Fin (L + M + 2), f i) =
      (∏ i : Fin (L + 1), f ⟨i.val, by omega⟩) *
        ∏ j : Fin (M + 1), f ⟨L + 1 + j.val, by omega⟩ := by
  let e := quantumIsingSpatialSumEquiv L M
  calc
    (∏ i : Fin (L + M + 2), f i) =
        ∏ x : Fin (L + 1) ⊕ Fin (M + 1), f (e x) := by
      apply Fintype.prod_equiv e.symm
      intro i
      simp
    _ = (∏ i : Fin (L + 1), f (e (Sum.inl i))) *
          ∏ j : Fin (M + 1), f (e (Sum.inr j)) :=
      Fintype.prod_sum_type _
    _ = _ := by
      apply congrArg₂ (fun x y : Real => x * y)
      · apply Finset.prod_congr rfl
        intro i _
        congr 1
      · apply Finset.prod_congr rfl
        intro j _
        congr 1

private theorem quantumIsingCyclicSucc_castSucc {L : Nat} (i : Fin L) :
    quantumIsingCyclicSucc (i.castSucc : Fin (L + 1)) = i.succ := by
  apply Fin.ext
  simp only [quantumIsingCyclicSucc, Fin.val_castSucc, Fin.val_succ]
  rw [Nat.mod_eq_of_lt]
  omega

private theorem quantumIsingCyclicSucc_last (L : Nat) :
    quantumIsingCyclicSucc (Fin.last L) = (0 : Fin (L + 1)) := by
  apply Fin.ext
  simp [quantumIsingCyclicSucc]


theorem quantumIsingChainInteraction_succ_eq_open_add_seam
    (L : Nat) (sigma : QuantumIsingChainConfig (L + 1)) :
    quantumIsingChainInteraction (L + 1) sigma =
      quantumIsingOpenChainInteraction L sigma +
        quantumIsingSpinSign (sigma (Fin.last L)) *
          quantumIsingSpinSign (sigma 0) := by
  unfold quantumIsingChainInteraction quantumIsingOpenChainInteraction
  rw [Fin.sum_univ_castSucc]
  simp_rw [quantumIsingCyclicSucc_castSucc]
  rw [quantumIsingCyclicSucc_last]


theorem quantumIsingOpenChainInteraction_add
    (L M : Nat) (sigma : QuantumIsingChainConfig (L + M + 2)) :
    quantumIsingOpenChainInteraction (L + M + 1) sigma =
      quantumIsingOpenChainInteraction L
          (quantumIsingLeftSpatialBlock L M sigma) +
        quantumIsingSpinSign
            ((quantumIsingLeftSpatialBlock L M sigma) (Fin.last L)) *
          quantumIsingSpinSign
            ((quantumIsingRightSpatialBlock L M sigma) 0) +
        quantumIsingOpenChainInteraction M
          (quantumIsingRightSpatialBlock L M sigma) := by
  unfold quantumIsingOpenChainInteraction
  change (∑ i : Fin (L + (M + 1)), _) = _
  rw [Fin.sum_univ_add]
  rw [Fin.sum_univ_succ]
  have hleft0 (i : Fin L) :
      (Fin.castAdd (M + 1) i : Fin (L + (M + 1))).castSucc =
        (⟨i.val, by omega⟩ : Fin (L + M + 2)) := by
    apply Fin.ext
    rfl
  have hleft1 (i : Fin L) :
      (Fin.castAdd (M + 1) i : Fin (L + (M + 1))).succ =
        (⟨i.val + 1, by omega⟩ : Fin (L + M + 2)) := by
    apply Fin.ext
    rfl
  have hcross0 :
      (Fin.natAdd L (0 : Fin (M + 1)) : Fin (L + (M + 1))).castSucc =
        (⟨L, by omega⟩ : Fin (L + M + 2)) := by
    apply Fin.ext
    simp
  have hcross1 :
      (Fin.natAdd L (0 : Fin (M + 1)) : Fin (L + (M + 1))).succ =
        (⟨L + 1, by omega⟩ : Fin (L + M + 2)) := by
    apply Fin.ext
    simp
  have hright0 (j : Fin M) :
      (Fin.natAdd L j.succ : Fin (L + (M + 1))).castSucc =
        (⟨L + 1 + j.val, by omega⟩ : Fin (L + M + 2)) := by
    apply Fin.ext
    simp only [Fin.val_castSucc, Fin.val_natAdd, Fin.val_succ]
    omega
  have hright1 (j : Fin M) :
      (Fin.natAdd L j.succ : Fin (L + (M + 1))).succ =
        (⟨L + 2 + j.val, by omega⟩ : Fin (L + M + 2)) := by
    apply Fin.ext
    simp only [Fin.val_natAdd, Fin.val_succ]
    omega
  simp_rw [hleft0, hleft1, hcross0, hcross1, hright0, hright1]
  simp only [quantumIsingLeftSpatialBlock, quantumIsingRightSpatialBlock,
    Fin.val_castSucc, Fin.val_succ, Fin.val_zero, Fin.val_last]
  ring

private theorem quantumIsingSpinSign_mul_abs
    (s t : Bool) : |quantumIsingSpinSign s * quantumIsingSpinSign t| = 1 := by
  cases s <;> cases t <;> norm_num [quantumIsingSpinSign]



theorem abs_quantumIsingChainInteraction_sub_open
    (L : Nat) (sigma : QuantumIsingChainConfig (L + 1)) :
    |quantumIsingChainInteraction (L + 1) sigma -
      quantumIsingOpenChainInteraction L sigma| = 1 := by
  rw [quantumIsingChainInteraction_succ_eq_open_add_seam]
  ring_nf
  exact quantumIsingSpinSign_mul_abs _ _


noncomputable def quantumIsingOpenSpatialTrotterWeight
    (beta : Real) (n L : Nat)
    (sigma : QuantumIsingChainConfig (L + 1)) : Real :=
  Real.exp (beta / (4 * (n : Real)) *
    quantumIsingOpenChainInteraction L sigma)



theorem quantumIsingSpatialTrotterWeight_le_exp_mul_open
    (beta : Real) (n L : Nat) (hn : n ≠ 0) (hbeta : 0 ≤ beta)
    (sigma : QuantumIsingChainConfig (L + 1)) :
    quantumIsingSpatialTrotterWeight beta n (L + 1) sigma ≤
      Real.exp (beta / (4 * (n : Real))) *
        quantumIsingOpenSpatialTrotterWeight beta n L sigma := by
  let J : Real := beta / (4 * (n : Real))
  have hJ : 0 ≤ J := by
    dsimp [J]
    positivity
  have hdiff := abs_quantumIsingChainInteraction_sub_open L sigma
  have hle : J * (quantumIsingChainInteraction (L + 1) sigma -
      quantumIsingOpenChainInteraction L sigma) ≤ J := by
    have := (abs_le.mp (le_of_eq hdiff)).2
    nlinarith
  unfold quantumIsingSpatialTrotterWeight
  change Real.exp (J * quantumIsingChainInteraction (L + 1) sigma) ≤
    Real.exp J * Real.exp
      (J * quantumIsingOpenChainInteraction L sigma)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith



theorem exp_neg_mul_open_le_quantumIsingSpatialTrotterWeight
    (beta : Real) (n L : Nat) (hn : n ≠ 0) (hbeta : 0 ≤ beta)
    (sigma : QuantumIsingChainConfig (L + 1)) :
    Real.exp (-(beta / (4 * (n : Real)))) *
        quantumIsingOpenSpatialTrotterWeight beta n L sigma ≤
      quantumIsingSpatialTrotterWeight beta n (L + 1) sigma := by
  let J : Real := beta / (4 * (n : Real))
  have hJ : 0 ≤ J := by
    dsimp [J]
    positivity
  have hdiff := abs_quantumIsingChainInteraction_sub_open L sigma
  have hle : -J ≤ J * (quantumIsingChainInteraction (L + 1) sigma -
      quantumIsingOpenChainInteraction L sigma) := by
    have := (abs_le.mp (le_of_eq hdiff)).1
    nlinarith
  unfold quantumIsingSpatialTrotterWeight
  change Real.exp (-J) * Real.exp
      (J * quantumIsingOpenChainInteraction L sigma) ≤
    Real.exp (J * quantumIsingChainInteraction (L + 1) sigma)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith


noncomputable def quantumIsingOpenTrotterTransferKernel
    (beta h : Real) (n L : Nat)
    (sigma tau : QuantumIsingChainConfig (L + 1)) : Real :=
  quantumIsingOpenSpatialTrotterWeight beta n L sigma *
    ∏ i : Fin (L + 1), quantumIsingTrotterKernel beta h n (sigma i) (tau i)

theorem quantumIsingTrotterKernel_nonneg
    (beta h : Real) (n : Nat) (hbh : 0 ≤ beta * h)
    (s t : Bool) : 0 ≤ quantumIsingTrotterKernel beta h n s t := by
  unfold quantumIsingTrotterKernel
  by_cases hst : s = t
  · rw [if_pos hst]
    norm_num
  · rw [if_neg hst]
    positivity

theorem quantumIsingOpenTrotterTransferKernel_nonneg
    (beta h : Real) (n L : Nat) (hbh : 0 ≤ beta * h)
    (sigma tau : QuantumIsingChainConfig (L + 1)) :
    0 ≤ quantumIsingOpenTrotterTransferKernel beta h n L sigma tau := by
  unfold quantumIsingOpenTrotterTransferKernel
  exact mul_nonneg (Real.exp_nonneg _) <|
    Finset.prod_nonneg fun i _ =>
      quantumIsingTrotterKernel_nonneg beta h n hbh (sigma i) (tau i)



theorem quantumIsingOpenTrotterTransferKernel_add
    (beta h : Real) (n L M : Nat)
    (sigma tau : QuantumIsingChainConfig (L + M + 2)) :
    quantumIsingOpenTrotterTransferKernel beta h n (L + M + 1) sigma tau =
      Real.exp (beta / (4 * (n : Real)) *
        (quantumIsingSpinSign
            ((quantumIsingLeftSpatialBlock L M sigma) (Fin.last L)) *
          quantumIsingSpinSign
            ((quantumIsingRightSpatialBlock L M sigma) 0))) *
        quantumIsingOpenTrotterTransferKernel beta h n L
          (quantumIsingLeftSpatialBlock L M sigma)
          (quantumIsingLeftSpatialBlock L M tau) *
        quantumIsingOpenTrotterTransferKernel beta h n M
          (quantumIsingRightSpatialBlock L M sigma)
          (quantumIsingRightSpatialBlock L M tau) := by
  unfold quantumIsingOpenTrotterTransferKernel
  unfold quantumIsingOpenSpatialTrotterWeight
  rw [quantumIsingOpenChainInteraction_add]
  rw [show beta / (4 * (n : Real)) *
      (quantumIsingOpenChainInteraction L
          (quantumIsingLeftSpatialBlock L M sigma) +
        quantumIsingSpinSign
            (quantumIsingLeftSpatialBlock L M sigma (Fin.last L)) *
          quantumIsingSpinSign
            (quantumIsingRightSpatialBlock L M sigma 0) +
        quantumIsingOpenChainInteraction M
          (quantumIsingRightSpatialBlock L M sigma)) =
      beta / (4 * (n : Real)) *
          (quantumIsingSpinSign
              (quantumIsingLeftSpatialBlock L M sigma (Fin.last L)) *
            quantumIsingSpinSign
              (quantumIsingRightSpatialBlock L M sigma 0)) +
        beta / (4 * (n : Real)) *
          quantumIsingOpenChainInteraction L
            (quantumIsingLeftSpatialBlock L M sigma) +
        beta / (4 * (n : Real)) *
          quantumIsingOpenChainInteraction M
            (quantumIsingRightSpatialBlock L M sigma) by ring]
  rw [Real.exp_add, Real.exp_add, quantumIsing_prod_spatial_add]
  simp only [quantumIsingLeftSpatialBlock, quantumIsingRightSpatialBlock]
  ring

theorem quantumIsingTrotterTransferKernel_le_exp_mul_open
    (beta h : Real) (n L : Nat) (hn : n ≠ 0)
    (hbeta : 0 ≤ beta) (hbh : 0 ≤ beta * h)
    (sigma tau : QuantumIsingChainConfig (L + 1)) :
    quantumIsingTrotterTransferKernel beta h n (L + 1) sigma tau ≤
      Real.exp (beta / (4 * (n : Real))) *
        quantumIsingOpenTrotterTransferKernel beta h n L sigma tau := by
  unfold quantumIsingTrotterTransferKernel
  unfold quantumIsingOpenTrotterTransferKernel
  have hp : 0 ≤ ∏ i : Fin (L + 1),
      quantumIsingTrotterKernel beta h n (sigma i) (tau i) :=
    Finset.prod_nonneg fun i _ =>
      quantumIsingTrotterKernel_nonneg beta h n hbh (sigma i) (tau i)
  calc
    quantumIsingSpatialTrotterWeight beta n (L + 1) sigma *
        ∏ i : Fin (L + 1), quantumIsingTrotterKernel beta h n (sigma i) (tau i) ≤
      (Real.exp (beta / (4 * (n : Real))) *
        quantumIsingOpenSpatialTrotterWeight beta n L sigma) *
          ∏ i : Fin (L + 1), quantumIsingTrotterKernel beta h n (sigma i) (tau i) :=
      mul_le_mul_of_nonneg_right
        (quantumIsingSpatialTrotterWeight_le_exp_mul_open
          beta n L hn hbeta sigma) hp
    _ = _ := by ring

theorem exp_neg_mul_open_le_quantumIsingTrotterTransferKernel
    (beta h : Real) (n L : Nat) (hn : n ≠ 0)
    (hbeta : 0 ≤ beta) (hbh : 0 ≤ beta * h)
    (sigma tau : QuantumIsingChainConfig (L + 1)) :
    Real.exp (-(beta / (4 * (n : Real)))) *
        quantumIsingOpenTrotterTransferKernel beta h n L sigma tau ≤
      quantumIsingTrotterTransferKernel beta h n (L + 1) sigma tau := by
  unfold quantumIsingTrotterTransferKernel
  unfold quantumIsingOpenTrotterTransferKernel
  calc
    Real.exp (-(beta / (4 * (n : Real)))) *
        (quantumIsingOpenSpatialTrotterWeight beta n L sigma *
          ∏ i : Fin (L + 1), quantumIsingTrotterKernel beta h n (sigma i) (tau i)) =
      (Real.exp (-(beta / (4 * (n : Real)))) *
        quantumIsingOpenSpatialTrotterWeight beta n L sigma) *
          ∏ i : Fin (L + 1), quantumIsingTrotterKernel beta h n (sigma i) (tau i) := by ring
    _ ≤ quantumIsingSpatialTrotterWeight beta n (L + 1) sigma *
          ∏ i : Fin (L + 1), quantumIsingTrotterKernel beta h n (sigma i) (tau i) := by
      apply mul_le_mul_of_nonneg_right
      · exact exp_neg_mul_open_le_quantumIsingSpatialTrotterWeight
          beta n L hn hbeta sigma
      · exact Finset.prod_nonneg fun i _ =>
          quantumIsingTrotterKernel_nonneg beta h n hbh (sigma i) (tau i)


noncomputable def quantumIsingOpenTrotterPathWeight
    (beta h : Real) (n L : Nat)
    (omega : Fin n -> QuantumIsingChainConfig (L + 1)) : Real :=
  ∏ k : Fin n, quantumIsingOpenTrotterTransferKernel beta h n L
      (omega k) (omega (quantumIsingCyclicSucc k))


noncomputable def quantumIsingOpenTrotterPathPartition
    (beta h : Real) (n L : Nat) : Real :=
  ∑ omega : Fin n -> QuantumIsingChainConfig (L + 1),
    quantumIsingOpenTrotterPathWeight beta h n L omega

private theorem exp_trotterSeam_pow
    (beta : Real) (n : Nat) (hn : n ≠ 0) :
    Real.exp (beta / (4 * (n : Real))) ^ n = Real.exp (beta / 4) := by
  rw [← Real.exp_nat_mul]
  congr 1
  field_simp [hn]

private theorem exp_neg_trotterSeam_pow
    (beta : Real) (n : Nat) (hn : n ≠ 0) :
    Real.exp (-(beta / (4 * (n : Real)))) ^ n = Real.exp (-(beta / 4)) := by
  rw [← Real.exp_nat_mul]
  congr 1
  field_simp [hn]

private theorem quantumIsingOpenTrotterPathWeight_join
    (beta h : Real) (n L M : Nat)
    (omegaL : Fin n -> QuantumIsingChainConfig (L + 1))
    (omegaM : Fin n -> QuantumIsingChainConfig (M + 1)) :
    quantumIsingOpenTrotterPathWeight beta h n (L + M + 1)
        (fun k => quantumIsingSpatialJoin L M (omegaL k) (omegaM k)) =
      (∏ k : Fin n, Real.exp (beta / (4 * (n : Real)) *
        (quantumIsingSpinSign (omegaL k (Fin.last L)) *
          quantumIsingSpinSign (omegaM k 0)))) *
        quantumIsingOpenTrotterPathWeight beta h n L omegaL *
        quantumIsingOpenTrotterPathWeight beta h n M omegaM := by
  unfold quantumIsingOpenTrotterPathWeight
  simp_rw [quantumIsingOpenTrotterTransferKernel_add]
  simp only [quantumIsingLeftSpatialBlock_join,
    quantumIsingRightSpatialBlock_join]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]

private theorem quantumIsing_bridgeProduct_le
    (beta : Real) (n L M : Nat) (hn : n ≠ 0) (hbeta : 0 ≤ beta)
    (omegaL : Fin n -> QuantumIsingChainConfig (L + 1))
    (omegaM : Fin n -> QuantumIsingChainConfig (M + 1)) :
    (∏ k : Fin n, Real.exp (beta / (4 * (n : Real)) *
      (quantumIsingSpinSign (omegaL k (Fin.last L)) *
        quantumIsingSpinSign (omegaM k 0)))) ≤ Real.exp (beta / 4) := by
  calc
    (∏ k : Fin n, Real.exp (beta / (4 * (n : Real)) *
        (quantumIsingSpinSign (omegaL k (Fin.last L)) *
          quantumIsingSpinSign (omegaM k 0)))) ≤
      ∏ _k : Fin n, Real.exp (beta / (4 * (n : Real))) := by
        apply Finset.prod_le_prod
        · intro k _
          exact Real.exp_nonneg _
        · intro k _
          apply Real.exp_le_exp.mpr
          have habs := quantumIsingSpinSign_mul_abs
            (omegaL k (Fin.last L)) (omegaM k 0)
          have hsign := (abs_le.mp (le_of_eq habs)).2
          have hJ : 0 ≤ beta / (4 * (n : Real)) := by positivity
          nlinarith
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact exp_trotterSeam_pow beta n hn

private theorem quantumIsing_exp_neg_le_bridgeProduct
    (beta : Real) (n L M : Nat) (hn : n ≠ 0) (hbeta : 0 ≤ beta)
    (omegaL : Fin n -> QuantumIsingChainConfig (L + 1))
    (omegaM : Fin n -> QuantumIsingChainConfig (M + 1)) :
    Real.exp (-(beta / 4)) ≤
      ∏ k : Fin n, Real.exp (beta / (4 * (n : Real)) *
        (quantumIsingSpinSign (omegaL k (Fin.last L)) *
          quantumIsingSpinSign (omegaM k 0))) := by
  calc
    Real.exp (-(beta / 4)) =
        ∏ _k : Fin n, Real.exp (-(beta / (4 * (n : Real)))) := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact (exp_neg_trotterSeam_pow beta n hn).symm
    _ ≤ ∏ k : Fin n, Real.exp (beta / (4 * (n : Real)) *
        (quantumIsingSpinSign (omegaL k (Fin.last L)) *
          quantumIsingSpinSign (omegaM k 0))) := by
      apply Finset.prod_le_prod
      · intro k _
        exact Real.exp_nonneg _
      · intro k _
        apply Real.exp_le_exp.mpr
        have habs := quantumIsingSpinSign_mul_abs
          (omegaL k (Fin.last L)) (omegaM k 0)
        have hsign := (abs_le.mp (le_of_eq habs)).1
        have hJ : 0 ≤ beta / (4 * (n : Real)) := by positivity
        nlinarith

theorem quantumIsingOpenTrotterPathWeight_nonneg
    (beta h : Real) (n L : Nat) (hbh : 0 ≤ beta * h)
    (omega : Fin n -> QuantumIsingChainConfig (L + 1)) :
    0 ≤ quantumIsingOpenTrotterPathWeight beta h n L omega := by
  unfold quantumIsingOpenTrotterPathWeight
  exact Finset.prod_nonneg fun k _ =>
    quantumIsingOpenTrotterTransferKernel_nonneg beta h n L hbh _ _

private theorem quantumIsingOpenTrotterPathWeight_join_le
    (beta h : Real) (n L M : Nat) (hn : n ≠ 0)
    (hbeta : 0 ≤ beta) (hbh : 0 ≤ beta * h)
    (omegaL : Fin n -> QuantumIsingChainConfig (L + 1))
    (omegaM : Fin n -> QuantumIsingChainConfig (M + 1)) :
    quantumIsingOpenTrotterPathWeight beta h n (L + M + 1)
        (fun k => quantumIsingSpatialJoin L M (omegaL k) (omegaM k)) ≤
      Real.exp (beta / 4) *
        (quantumIsingOpenTrotterPathWeight beta h n L omegaL *
          quantumIsingOpenTrotterPathWeight beta h n M omegaM) := by
  rw [quantumIsingOpenTrotterPathWeight_join]
  calc
    (∏ k : Fin n, Real.exp (beta / (4 * (n : Real)) *
          (quantumIsingSpinSign (omegaL k (Fin.last L)) *
            quantumIsingSpinSign (omegaM k 0)))) *
        quantumIsingOpenTrotterPathWeight beta h n L omegaL *
        quantumIsingOpenTrotterPathWeight beta h n M omegaM =
      (∏ k : Fin n, Real.exp (beta / (4 * (n : Real)) *
          (quantumIsingSpinSign (omegaL k (Fin.last L)) *
            quantumIsingSpinSign (omegaM k 0)))) *
        (quantumIsingOpenTrotterPathWeight beta h n L omegaL *
          quantumIsingOpenTrotterPathWeight beta h n M omegaM) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right
      · exact quantumIsing_bridgeProduct_le beta n L M hn hbeta omegaL omegaM
      · exact mul_nonneg
          (quantumIsingOpenTrotterPathWeight_nonneg beta h n L hbh omegaL)
          (quantumIsingOpenTrotterPathWeight_nonneg beta h n M hbh omegaM)

private theorem quantumIsing_exp_mul_openPathWeights_le_join
    (beta h : Real) (n L M : Nat) (hn : n ≠ 0)
    (hbeta : 0 ≤ beta) (hbh : 0 ≤ beta * h)
    (omegaL : Fin n -> QuantumIsingChainConfig (L + 1))
    (omegaM : Fin n -> QuantumIsingChainConfig (M + 1)) :
    Real.exp (-(beta / 4)) *
        (quantumIsingOpenTrotterPathWeight beta h n L omegaL *
          quantumIsingOpenTrotterPathWeight beta h n M omegaM) ≤
      quantumIsingOpenTrotterPathWeight beta h n (L + M + 1)
        (fun k => quantumIsingSpatialJoin L M (omegaL k) (omegaM k)) := by
  rw [quantumIsingOpenTrotterPathWeight_join]
  calc
    Real.exp (-(beta / 4)) *
        (quantumIsingOpenTrotterPathWeight beta h n L omegaL *
          quantumIsingOpenTrotterPathWeight beta h n M omegaM) ≤
      (∏ k : Fin n, Real.exp (beta / (4 * (n : Real)) *
          (quantumIsingSpinSign (omegaL k (Fin.last L)) *
            quantumIsingSpinSign (omegaM k 0)))) *
        (quantumIsingOpenTrotterPathWeight beta h n L omegaL *
          quantumIsingOpenTrotterPathWeight beta h n M omegaM) := by
      apply mul_le_mul_of_nonneg_right
      · exact quantumIsing_exp_neg_le_bridgeProduct
          beta n L M hn hbeta omegaL omegaM
      · exact mul_nonneg
          (quantumIsingOpenTrotterPathWeight_nonneg beta h n L hbh omegaL)
          (quantumIsingOpenTrotterPathWeight_nonneg beta h n M hbh omegaM)
    _ = _ := by ring

private theorem quantumIsing_openPartition_reindex
    (beta h : Real) (n L M : Nat) :
    quantumIsingOpenTrotterPathPartition beta h n (L + M + 1) =
      ∑ omega :
          (Fin n -> QuantumIsingChainConfig (L + 1)) ×
            (Fin n -> QuantumIsingChainConfig (M + 1)),
        quantumIsingOpenTrotterPathWeight beta h n (L + M + 1)
          ((quantumIsingSpatialPathEquiv n L M).symm omega) := by
  unfold quantumIsingOpenTrotterPathPartition
  apply Fintype.sum_equiv (quantumIsingSpatialPathEquiv n L M)
  intro omega
  simp

private theorem quantumIsing_sum_pair_openPathWeights
    (beta h : Real) (n L M : Nat) :
    (∑ omega :
        (Fin n -> QuantumIsingChainConfig (L + 1)) ×
          (Fin n -> QuantumIsingChainConfig (M + 1)),
      quantumIsingOpenTrotterPathWeight beta h n L omega.1 *
        quantumIsingOpenTrotterPathWeight beta h n M omega.2) =
      quantumIsingOpenTrotterPathPartition beta h n L *
        quantumIsingOpenTrotterPathPartition beta h n M := by
  unfold quantumIsingOpenTrotterPathPartition
  calc
    (∑ omega :
        (Fin n -> QuantumIsingChainConfig (L + 1)) ×
          (Fin n -> QuantumIsingChainConfig (M + 1)),
      quantumIsingOpenTrotterPathWeight beta h n L omega.1 *
        quantumIsingOpenTrotterPathWeight beta h n M omega.2) =
      ∑ omegaL : Fin n -> QuantumIsingChainConfig (L + 1),
        ∑ omegaM : Fin n -> QuantumIsingChainConfig (M + 1),
          quantumIsingOpenTrotterPathWeight beta h n L omegaL *
            quantumIsingOpenTrotterPathWeight beta h n M omegaM := by
        exact Fintype.sum_prod_type _
    _ = _ := (Fintype.sum_mul_sum
      (quantumIsingOpenTrotterPathWeight beta h n L)
      (quantumIsingOpenTrotterPathWeight beta h n M)).symm



theorem quantumIsingOpenTrotterPathPartition_add_le
    (beta h : Real) (n L M : Nat) (hn : n ≠ 0)
    (hbeta : 0 ≤ beta) (hbh : 0 ≤ beta * h) :
    quantumIsingOpenTrotterPathPartition beta h n (L + M + 1) ≤
      Real.exp (beta / 4) *
        (quantumIsingOpenTrotterPathPartition beta h n L *
          quantumIsingOpenTrotterPathPartition beta h n M) := by
  rw [quantumIsing_openPartition_reindex]
  rw [← quantumIsing_sum_pair_openPathWeights]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro omega _
  exact quantumIsingOpenTrotterPathWeight_join_le
    beta h n L M hn hbeta hbh omega.1 omega.2

theorem quantumIsing_exp_mul_openPartitions_le_add
    (beta h : Real) (n L M : Nat) (hn : n ≠ 0)
    (hbeta : 0 ≤ beta) (hbh : 0 ≤ beta * h) :
    Real.exp (-(beta / 4)) *
        (quantumIsingOpenTrotterPathPartition beta h n L *
          quantumIsingOpenTrotterPathPartition beta h n M) ≤
      quantumIsingOpenTrotterPathPartition beta h n (L + M + 1) := by
  rw [quantumIsing_openPartition_reindex]
  rw [← quantumIsing_sum_pair_openPathWeights]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro omega _
  exact quantumIsing_exp_mul_openPathWeights_le_join
    beta h n L M hn hbeta hbh omega.1 omega.2



theorem quantumIsingTrotterPathPartition_le_exp_mul_open
    (beta h : Real) (n L : Nat) (hn : n ≠ 0)
    (hbeta : 0 ≤ beta) (hbh : 0 ≤ beta * h) :
    quantumIsingTrotterPathPartition beta h n (L + 1) ≤
      Real.exp (beta / 4) *
        quantumIsingOpenTrotterPathPartition beta h n L := by
  unfold quantumIsingTrotterPathPartition
  unfold quantumIsingOpenTrotterPathPartition
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro omega _
  calc
    ∏ k : Fin n, quantumIsingTrotterTransferKernel beta h n (L + 1)
        (omega k) (omega (quantumIsingCyclicSucc k)) ≤
      ∏ k : Fin n, (Real.exp (beta / (4 * (n : Real))) *
        quantumIsingOpenTrotterTransferKernel beta h n L
          (omega k) (omega (quantumIsingCyclicSucc k))) := by
        apply Finset.prod_le_prod
        · intro k _
          unfold quantumIsingTrotterTransferKernel
          exact mul_nonneg (Real.exp_nonneg _) <|
            Finset.prod_nonneg fun i _ =>
              quantumIsingTrotterKernel_nonneg beta h n hbh _ _
        · intro k _
          exact quantumIsingTrotterTransferKernel_le_exp_mul_open
            beta h n L hn hbeta hbh _ _
    _ = Real.exp (beta / 4) *
        ∏ k : Fin n, quantumIsingOpenTrotterTransferKernel beta h n L
          (omega k) (omega (quantumIsingCyclicSucc k)) := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [exp_trotterSeam_pow beta n hn]

theorem exp_neg_mul_open_le_quantumIsingTrotterPathPartition
    (beta h : Real) (n L : Nat) (hn : n ≠ 0)
    (hbeta : 0 ≤ beta) (hbh : 0 ≤ beta * h) :
    Real.exp (-(beta / 4)) *
        quantumIsingOpenTrotterPathPartition beta h n L ≤
      quantumIsingTrotterPathPartition beta h n (L + 1) := by
  unfold quantumIsingTrotterPathPartition
  unfold quantumIsingOpenTrotterPathPartition
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro omega _
  calc
    Real.exp (-(beta / 4)) *
        ∏ k : Fin n, quantumIsingOpenTrotterTransferKernel beta h n L
          (omega k) (omega (quantumIsingCyclicSucc k)) =
      ∏ k : Fin n, (Real.exp (-(beta / (4 * (n : Real)))) *
        quantumIsingOpenTrotterTransferKernel beta h n L
          (omega k) (omega (quantumIsingCyclicSucc k))) := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [exp_neg_trotterSeam_pow beta n hn]
    _ ≤ ∏ k : Fin n, quantumIsingTrotterTransferKernel beta h n (L + 1)
        (omega k) (omega (quantumIsingCyclicSucc k)) := by
      apply Finset.prod_le_prod
      · intro k _
        exact mul_nonneg (Real.exp_nonneg _)
          (quantumIsingOpenTrotterTransferKernel_nonneg beta h n L hbh _ _)
      · intro k _
        exact exp_neg_mul_open_le_quantumIsingTrotterTransferKernel
          beta h n L hn hbeta hbh _ _

theorem quantumIsingTrotterKernel_pos
    (beta h : Real) (n : Nat) (hn : n ≠ 0) (hbh : 0 < beta * h)
    (s t : Bool) : 0 < quantumIsingTrotterKernel beta h n s t := by
  unfold quantumIsingTrotterKernel
  by_cases hst : s = t
  · simp only [if_pos hst]
    norm_num
  · simp only [if_neg hst]
    positivity

theorem quantumIsingOpenTrotterPathWeight_pos
    (beta h : Real) (n L : Nat) (hn : n ≠ 0) (hbh : 0 < beta * h)
    (omega : Fin n -> QuantumIsingChainConfig (L + 1)) :
    0 < quantumIsingOpenTrotterPathWeight beta h n L omega := by
  unfold quantumIsingOpenTrotterPathWeight
  apply Finset.prod_pos
  intro k _
  unfold quantumIsingOpenTrotterTransferKernel
  apply mul_pos (Real.exp_pos _)
  apply Finset.prod_pos
  intro i _
  exact quantumIsingTrotterKernel_pos beta h n hn hbh _ _

theorem quantumIsingOpenTrotterPathPartition_pos
    (beta h : Real) (n L : Nat) (hn : n ≠ 0) (hbh : 0 < beta * h) :
    0 < quantumIsingOpenTrotterPathPartition beta h n L := by
  unfold quantumIsingOpenTrotterPathPartition
  apply Finset.sum_pos'
  · intro omega _
    exact (quantumIsingOpenTrotterPathWeight_pos beta h n L hn hbh omega).le
  · let omega : Fin n -> QuantumIsingChainConfig (L + 1) := fun _ _ => false
    exact ⟨omega, Finset.mem_univ _,
      quantumIsingOpenTrotterPathWeight_pos beta h n L hn hbh omega⟩



noncomputable def quantumIsingOpenTrotterAction
    (beta h : Real) (n : Nat) : Nat -> Real
  | 0 => 0
  | L + 1 => -Real.log (quantumIsingOpenTrotterPathPartition beta h n L) / beta



theorem quantumIsingOpenTrotterAction_almostAdditive
    (beta h : Real) (n : Nat) (hn : n ≠ 0)
    (hbeta : 0 < beta) (hbh : 0 < beta * h) :
    QuantumIsingAlmostAdditive (quantumIsingOpenTrotterAction beta h n) (1 / 4) := by
  intro a b
  rcases a with _ | L
  · simp [quantumIsingOpenTrotterAction]
  rcases b with _ | M
  · simp [quantumIsingOpenTrotterAction]
  let ZL := quantumIsingOpenTrotterPathPartition beta h n L
  let ZM := quantumIsingOpenTrotterPathPartition beta h n M
  let ZLM := quantumIsingOpenTrotterPathPartition beta h n (L + M + 1)
  have hZL : 0 < ZL := quantumIsingOpenTrotterPathPartition_pos beta h n L hn hbh
  have hZM : 0 < ZM := quantumIsingOpenTrotterPathPartition_pos beta h n M hn hbh
  have hZLM : 0 < ZLM :=
    quantumIsingOpenTrotterPathPartition_pos beta h n (L + M + 1) hn hbh
  have hlower : Real.exp (-(beta / 4)) * (ZL * ZM) ≤ ZLM :=
    quantumIsing_exp_mul_openPartitions_le_add beta h n L M hn hbeta.le hbh.le
  have hupper : ZLM ≤ Real.exp (beta / 4) * (ZL * ZM) :=
    quantumIsingOpenTrotterPathPartition_add_le beta h n L M hn hbeta.le hbh.le
  have hlogLower := Real.log_le_log
    (mul_pos (Real.exp_pos _) (mul_pos hZL hZM)) hlower
  have hlogUpper := Real.log_le_log hZLM hupper
  rw [Real.log_mul (Real.exp_ne_zero _) (mul_ne_zero hZL.ne' hZM.ne'),
    Real.log_exp, Real.log_mul hZL.ne' hZM.ne'] at hlogLower hlogUpper
  have hnum : |Real.log ZL + Real.log ZM - Real.log ZLM| ≤ beta / 4 := by
    rw [abs_le]
    constructor <;> linarith
  rw [show L + 1 + (M + 1) = (L + M + 1) + 1 by omega]
  simp only [quantumIsingOpenTrotterAction]
  change |(-Real.log ZLM / beta) - (-Real.log ZL / beta) -
    (-Real.log ZM / beta)| ≤ 1 / 4
  rw [show -Real.log ZLM / beta - -Real.log ZL / beta -
      -Real.log ZM / beta =
      (Real.log ZL + Real.log ZM - Real.log ZLM) / beta by ring]
  rw [abs_div, abs_of_pos hbeta]
  calc
    |Real.log ZL + Real.log ZM - Real.log ZLM| / beta ≤
        (beta / 4) / beta := by gcongr
    _ = 1 / 4 := by field_simp [hbeta.ne']


theorem quantumIsingOpenTrotterFreeEnergy_tendsto
    (beta h : Real) (n : Nat) (hn : n ≠ 0)
    (hbeta : 0 < beta) (hbh : 0 < beta * h) :
    Filter.Tendsto
      (fun L : Nat => quantumIsingOpenTrotterAction beta h n L / L)
      Filter.atTop
      (nhds ((quantumIsingOpenTrotterAction_almostAdditive
        beta h n hn hbeta hbh).limit)) :=
  (quantumIsingOpenTrotterAction_almostAdditive
    beta h n hn hbeta hbh).tendsto_limit


theorem quantumIsingOpenTrotterFreeEnergy_uniform_bound
    (beta h : Real) (n : Nat) (hn : n ≠ 0)
    (hbeta : 0 < beta) (hbh : 0 < beta * h)
    {L : Nat} (hL : L ≠ 0) :
    |(quantumIsingOpenTrotterAction_almostAdditive
        beta h n hn hbeta hbh).limit -
      quantumIsingOpenTrotterAction beta h n L / L| ≤
        (1 / 4 : Real) / L :=
  (quantumIsingOpenTrotterAction_almostAdditive
    beta h n hn hbeta hbh).abs_limit_sub_div_le hL


noncomputable def quantumIsingPeriodicTrotterAction
    (beta h : Real) (n : Nat) : Nat -> Real
  | 0 => 0
  | L + 1 => -Real.log (quantumIsingTrotterPathPartition beta h n (L + 1)) / beta

theorem quantumIsingTrotterPathPartition_pos
    (beta h : Real) (n L : Nat) (hn : n ≠ 0)
    (hbeta : 0 < beta) (hbh : 0 < beta * h) :
    0 < quantumIsingTrotterPathPartition beta h n (L + 1) := by
  have hopen := quantumIsingOpenTrotterPathPartition_pos beta h n L hn hbh
  have hlower := exp_neg_mul_open_le_quantumIsingTrotterPathPartition
    beta h n L hn hbeta.le hbh.le
  exact (mul_pos (Real.exp_pos _) hopen).trans_le hlower



theorem abs_quantumIsingPeriodicTrotterAction_sub_open
    (beta h : Real) (n L : Nat) (hn : n ≠ 0)
    (hbeta : 0 < beta) (hbh : 0 < beta * h) :
    |quantumIsingPeriodicTrotterAction beta h n L -
      quantumIsingOpenTrotterAction beta h n L| ≤ 1 / 4 := by
  rcases L with _ | L
  · simp [quantumIsingPeriodicTrotterAction, quantumIsingOpenTrotterAction]
  let Zopen := quantumIsingOpenTrotterPathPartition beta h n L
  let Zper := quantumIsingTrotterPathPartition beta h n (L + 1)
  have hopen : 0 < Zopen :=
    quantumIsingOpenTrotterPathPartition_pos beta h n L hn hbh
  have hper : 0 < Zper :=
    quantumIsingTrotterPathPartition_pos beta h n L hn hbeta hbh
  have hlower : Real.exp (-(beta / 4)) * Zopen ≤ Zper :=
    exp_neg_mul_open_le_quantumIsingTrotterPathPartition
      beta h n L hn hbeta.le hbh.le
  have hupper : Zper ≤ Real.exp (beta / 4) * Zopen :=
    quantumIsingTrotterPathPartition_le_exp_mul_open
      beta h n L hn hbeta.le hbh.le
  have hlogLower := Real.log_le_log
    (mul_pos (Real.exp_pos _) hopen) hlower
  have hlogUpper := Real.log_le_log hper hupper
  rw [Real.log_mul (Real.exp_ne_zero _) hopen.ne', Real.log_exp] at hlogLower hlogUpper
  have hnum : |Real.log Zopen - Real.log Zper| ≤ beta / 4 := by
    rw [abs_le]
    constructor <;> linarith
  simp only [quantumIsingPeriodicTrotterAction,
    quantumIsingOpenTrotterAction]
  rw [show -Real.log Zper / beta - -Real.log Zopen / beta =
      (Real.log Zopen - Real.log Zper) / beta by ring]
  rw [abs_div, abs_of_pos hbeta]
  calc
    |Real.log Zopen - Real.log Zper| / beta ≤ (beta / 4) / beta := by gcongr
    _ = 1 / 4 := by field_simp [hbeta.ne']




noncomputable def quantumIsingTrotterThermodynamicFreeEnergy
    (beta h : Real) (n : Nat) : Real :=
  if hp : n ≠ 0 ∧ 0 < beta ∧ 0 < beta * h then
    (quantumIsingOpenTrotterAction_almostAdditive
      beta h n hp.1 hp.2.1 hp.2.2).limit
  else 0

theorem quantumIsingTrotterThermodynamicFreeEnergy_eq_limit
    (beta h : Real) (n : Nat) (hn : n ≠ 0)
    (hbeta : 0 < beta) (hbh : 0 < beta * h) :
    quantumIsingTrotterThermodynamicFreeEnergy beta h n =
      (quantumIsingOpenTrotterAction_almostAdditive
        beta h n hn hbeta hbh).limit := by
  simp [quantumIsingTrotterThermodynamicFreeEnergy, hn, hbeta, hbh]



theorem quantumIsingPeriodicTrotterFreeEnergy_tendsto
    (beta h : Real) (n : Nat) (hn : n ≠ 0)
    (hbeta : 0 < beta) (hbh : 0 < beta * h) :
    Filter.Tendsto
      (fun L : Nat => quantumIsingPeriodicTrotterAction beta h n L / L)
      Filter.atTop
      (nhds (quantumIsingTrotterThermodynamicFreeEnergy beta h n)) := by
  have hopen := quantumIsingOpenTrotterFreeEnergy_tendsto
    beta h n hn hbeta hbh
  rw [← quantumIsingTrotterThermodynamicFreeEnergy_eq_limit
    beta h n hn hbeta hbh] at hopen
  have herr : Filter.Tendsto (fun L : Nat => (1 / 4 : Real) / L)
      Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (1 / 4 : Real)
  have hdiffAbs : Filter.Tendsto
      (fun L : Nat =>
        |quantumIsingPeriodicTrotterAction beta h n L / L -
          quantumIsingOpenTrotterAction beta h n L / L|)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero (fun L => abs_nonneg _)
      (fun L => ?_) herr
    rw [← sub_div, abs_div]
    nth_rewrite 2 [abs_of_nonneg (Nat.cast_nonneg L)]
    gcongr
    exact abs_quantumIsingPeriodicTrotterAction_sub_open
      beta h n L hn hbeta hbh
  have hdiff : Filter.Tendsto
      (fun L : Nat => quantumIsingPeriodicTrotterAction beta h n L / L -
        quantumIsingOpenTrotterAction beta h n L / L)
      Filter.atTop (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [Real.norm_eq_abs] using hdiffAbs
  convert hopen.add hdiff using 1
  · funext L
    ring
  · simp



theorem quantumIsingPeriodicTrotterFreeEnergy_uniform_bound
    (beta h : Real) (n : Nat) (hn : n ≠ 0)
    (hbeta : 0 < beta) (hbh : 0 < beta * h)
    {L : Nat} (hL : L ≠ 0) :
    |quantumIsingTrotterThermodynamicFreeEnergy beta h n -
      quantumIsingPeriodicTrotterAction beta h n L / L| ≤
        1 / (2 * (L : Real)) := by
  rw [quantumIsingTrotterThermodynamicFreeEnergy_eq_limit
    beta h n hn hbeta hbh]
  have hopen := quantumIsingOpenTrotterFreeEnergy_uniform_bound
    beta h n hn hbeta hbh hL
  have hseam := abs_quantumIsingPeriodicTrotterAction_sub_open
    beta h n L hn hbeta hbh
  have hLpos : 0 < (L : Real) := by exact_mod_cast Nat.pos_of_ne_zero hL
  have hseamDiv :
      |quantumIsingOpenTrotterAction beta h n L / L -
        quantumIsingPeriodicTrotterAction beta h n L / L| ≤
          (1 / 4 : Real) / L := by
    rw [← sub_div, abs_div, abs_of_pos hLpos]
    apply div_le_div_of_nonneg_right ?_ hLpos.le
    simpa [abs_sub_comm] using hseam
  calc
    |(quantumIsingOpenTrotterAction_almostAdditive
          beta h n hn hbeta hbh).limit -
        quantumIsingPeriodicTrotterAction beta h n L / L| ≤
      |(quantumIsingOpenTrotterAction_almostAdditive
          beta h n hn hbeta hbh).limit -
        quantumIsingOpenTrotterAction beta h n L / L| +
      |quantumIsingOpenTrotterAction beta h n L / L -
        quantumIsingPeriodicTrotterAction beta h n L / L| :=
      abs_sub_le _ _ _
    _ ≤ (1 / 4 : Real) / L + (1 / 4 : Real) / L :=
      add_le_add hopen hseamDiv
    _ = 1 / (2 * (L : Real)) := by
      field_simp [hL]
      norm_num

end StatMech.FrontierA
