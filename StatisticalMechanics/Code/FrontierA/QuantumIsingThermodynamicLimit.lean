/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.QuantumIsingBoundaryComparison
import Code.FrontierA.QuantumIsingAlmostAdditive










open scoped BigOperators
open Filter

namespace StatMech.FrontierA

abbrev QuantumIsingTwoBlockConfig (A B : Nat) :=
  QuantumIsingChainConfig A × QuantumIsingChainConfig B

def quantumIsingSumBlockEquiv (A B : Nat) :
    QuantumIsingChainConfig (A + B) ≃ QuantumIsingTwoBlockConfig A B where
  toFun sigma :=
    (fun i => sigma (finSumFinEquiv (Sum.inl i)),
      fun j => sigma (finSumFinEquiv (Sum.inr j)))
  invFun pair q :=
    Sum.elim pair.1 pair.2 (finSumFinEquiv.symm q)
  left_inv sigma := by
    funext q
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective q
    cases s <;> simp
  right_inv pair := by
    ext i <;> simp

@[simp] theorem quantumIsingSumBlockEquiv_apply_left
    (A B : Nat) (sigma : QuantumIsingChainConfig (A + B)) (i : Fin A) :
    (quantumIsingSumBlockEquiv A B sigma).1 i =
      sigma (finSumFinEquiv (Sum.inl i)) := rfl

@[simp] theorem quantumIsingSumBlockEquiv_apply_right
    (A B : Nat) (sigma : QuantumIsingChainConfig (A + B)) (j : Fin B) :
    (quantumIsingSumBlockEquiv A B sigma).2 j =
      sigma (finSumFinEquiv (Sum.inr j)) := rfl

@[simp] theorem quantumIsingSumBlockEquiv_symm_left
    (A B : Nat) (pair : QuantumIsingTwoBlockConfig A B) (i : Fin A) :
    (quantumIsingSumBlockEquiv A B).symm pair
        (finSumFinEquiv (Sum.inl i)) = pair.1 i := by
  simp [quantumIsingSumBlockEquiv]

@[simp] theorem quantumIsingSumBlockEquiv_symm_right
    (A B : Nat) (pair : QuantumIsingTwoBlockConfig A B) (j : Fin B) :
    (quantumIsingSumBlockEquiv A B).symm pair
        (finSumFinEquiv (Sum.inr j)) = pair.2 j := by
  simp [quantumIsingSumBlockEquiv]

@[simp] theorem cyclicSucc_finSum_left_castSucc
    (A B : Nat) (i : Fin A) :
    quantumIsingCyclicSucc
        (finSumFinEquiv (Sum.inl i.castSucc) : Fin ((A + 1) + (B + 1))) =
      finSumFinEquiv (Sum.inl i.succ) := by
  apply Fin.ext
  change (i.val + 1) % ((A + 1) + (B + 1)) = i.val + 1
  rw [Nat.mod_eq_of_lt]
  omega

@[simp] theorem cyclicSucc_finSum_left_last
    (A B : Nat) :
    quantumIsingCyclicSucc
        (finSumFinEquiv (Sum.inl (Fin.last A)) : Fin ((A + 1) + (B + 1))) =
      finSumFinEquiv (Sum.inr (0 : Fin (B + 1))) := by
  apply Fin.ext
  change (A + 1) % ((A + 1) + (B + 1)) = A + 1
  rw [Nat.mod_eq_of_lt]
  omega

@[simp] theorem cyclicSucc_finSum_right_castSucc
    (A B : Nat) (j : Fin B) :
    quantumIsingCyclicSucc
        (finSumFinEquiv (Sum.inr j.castSucc) : Fin ((A + 1) + (B + 1))) =
      finSumFinEquiv (Sum.inr j.succ) := by
  apply Fin.ext
  change ((A + 1) + j.val + 1) % ((A + 1) + (B + 1)) =
    (A + 1) + (j.val + 1)
  rw [Nat.mod_eq_of_lt]
  · omega
  · omega

@[simp] theorem cyclicSucc_finSum_right_last
    (A B : Nat) :
    quantumIsingCyclicSucc
        (finSumFinEquiv (Sum.inr (Fin.last B)) : Fin ((A + 1) + (B + 1))) =
      finSumFinEquiv (Sum.inl (0 : Fin (A + 1))) := by
  apply Fin.ext
  change ((A + 1) + B + 1) % ((A + 1) + (B + 1)) = 0
  simp [Nat.add_assoc]

noncomputable def quantumIsingTwoBlockPeriodicInteraction (A B : Nat)
    (pair : QuantumIsingTwoBlockConfig (A + 1) (B + 1)) : Real :=
  quantumIsingChainInteraction (A + 1) pair.1 +
    quantumIsingChainInteraction (B + 1) pair.2

noncomputable def quantumIsingTwoBlockLongInteraction (A B : Nat)
    (pair : QuantumIsingTwoBlockConfig (A + 1) (B + 1)) : Real :=
  quantumIsingChainInteraction ((A + 1) + (B + 1))
    ((quantumIsingSumBlockEquiv (A + 1) (B + 1)).symm pair)

private noncomputable def quantumIsingTwoBlockOpenInteraction (A B : Nat)
    (pair : QuantumIsingTwoBlockConfig (A + 1) (B + 1)) : Real :=
  (∑ i : Fin A,
    quantumIsingSpinSign (pair.1 i.castSucc) *
      quantumIsingSpinSign (pair.1 i.succ)) +
  (∑ j : Fin B,
    quantumIsingSpinSign (pair.2 j.castSucc) *
      quantumIsingSpinSign (pair.2 j.succ))

theorem quantumIsingTwoBlockPeriodicInteraction_eq_open_seams
    (A B : Nat) (pair : QuantumIsingTwoBlockConfig (A + 1) (B + 1)) :
    quantumIsingTwoBlockPeriodicInteraction A B pair =
      quantumIsingTwoBlockOpenInteraction A B pair +
        quantumIsingSpinSign (pair.1 (Fin.last A)) *
          quantumIsingSpinSign (pair.1 0) +
        quantumIsingSpinSign (pair.2 (Fin.last B)) *
          quantumIsingSpinSign (pair.2 0) := by
  unfold quantumIsingTwoBlockPeriodicInteraction
  have hchain (L : Nat) (sigma : QuantumIsingChainConfig (L + 1)) :
      quantumIsingChainInteraction (L + 1) sigma =
        (∑ i : Fin L,
          quantumIsingSpinSign (sigma i.castSucc) *
            quantumIsingSpinSign (sigma i.succ)) +
          quantumIsingSpinSign (sigma (Fin.last L)) *
            quantumIsingSpinSign (sigma 0) := by
    unfold quantumIsingChainInteraction
    rw [Fin.sum_univ_castSucc]
    simp
  rw [hchain A pair.1, hchain B pair.2]
  unfold quantumIsingTwoBlockOpenInteraction
  ring

theorem quantumIsingTwoBlockLongInteraction_eq_open_seams
    (A B : Nat) (pair : QuantumIsingTwoBlockConfig (A + 1) (B + 1)) :
    quantumIsingTwoBlockLongInteraction A B pair =
      quantumIsingTwoBlockOpenInteraction A B pair +
        quantumIsingSpinSign (pair.1 (Fin.last A)) *
          quantumIsingSpinSign (pair.2 0) +
        quantumIsingSpinSign (pair.2 (Fin.last B)) *
          quantumIsingSpinSign (pair.1 0) := by
  unfold quantumIsingTwoBlockLongInteraction quantumIsingChainInteraction
  let flat := (quantumIsingSumBlockEquiv (A + 1) (B + 1)).symm pair
  calc
    (∑ q : Fin ((A + 1) + (B + 1)),
      quantumIsingSpinSign (flat q) *
        quantumIsingSpinSign (flat (quantumIsingCyclicSucc q))) =
      ∑ s : Fin (A + 1) ⊕ Fin (B + 1),
        quantumIsingSpinSign (flat (finSumFinEquiv s)) *
          quantumIsingSpinSign
            (flat (quantumIsingCyclicSucc (finSumFinEquiv s))) := by
      simpa using (Equiv.sum_comp finSumFinEquiv
        (fun q : Fin ((A + 1) + (B + 1)) =>
          quantumIsingSpinSign (flat q) *
            quantumIsingSpinSign (flat (quantumIsingCyclicSucc q)))).symm
    _ = (∑ i : Fin (A + 1),
          quantumIsingSpinSign (flat (finSumFinEquiv (Sum.inl i))) *
            quantumIsingSpinSign
              (flat (quantumIsingCyclicSucc
                (finSumFinEquiv (Sum.inl i))))) +
        ∑ j : Fin (B + 1),
          quantumIsingSpinSign (flat (finSumFinEquiv (Sum.inr j))) *
            quantumIsingSpinSign
              (flat (quantumIsingCyclicSucc
                (finSumFinEquiv (Sum.inr j)))) := by
      rw [Fintype.sum_sum_type]
    _ = _ := by
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      simp_rw [cyclicSucc_finSum_left_castSucc,
        cyclicSucc_finSum_left_last,
        cyclicSucc_finSum_right_castSucc,
        cyclicSucc_finSum_right_last]
      simp only [flat, quantumIsingSumBlockEquiv_symm_left,
        quantumIsingSumBlockEquiv_symm_right]
      simp only [quantumIsingTwoBlockOpenInteraction]
      ring

private theorem abs_quantumIsingBond_le_one (s t : Bool) :
    |quantumIsingSpinSign s * quantumIsingSpinSign t| ≤ 1 := by
  rw [abs_mul, abs_quantumIsingSpinSign, abs_quantumIsingSpinSign]
  norm_num



theorem quantumIsingTwoBlockInteraction_sub_le
    (A B : Nat) (pair : QuantumIsingTwoBlockConfig (A + 1) (B + 1)) :
    |quantumIsingTwoBlockLongInteraction A B pair -
      quantumIsingTwoBlockPeriodicInteraction A B pair| ≤ 4 := by
  rw [quantumIsingTwoBlockLongInteraction_eq_open_seams,
    quantumIsingTwoBlockPeriodicInteraction_eq_open_seams]
  let a : Real := quantumIsingSpinSign (pair.1 (Fin.last A)) *
    quantumIsingSpinSign (pair.2 0)
  let b : Real := quantumIsingSpinSign (pair.2 (Fin.last B)) *
    quantumIsingSpinSign (pair.1 0)
  let c : Real := quantumIsingSpinSign (pair.1 (Fin.last A)) *
    quantumIsingSpinSign (pair.1 0)
  let d : Real := quantumIsingSpinSign (pair.2 (Fin.last B)) *
    quantumIsingSpinSign (pair.2 0)
  change |quantumIsingTwoBlockOpenInteraction A B pair + a + b -
    (quantumIsingTwoBlockOpenInteraction A B pair + c + d)| ≤ 4
  rw [show quantumIsingTwoBlockOpenInteraction A B pair + a + b -
      (quantumIsingTwoBlockOpenInteraction A B pair + c + d) =
      a + b - c - d by ring]
  calc
    |a + b - c - d| ≤ |a + b - c| + |d| := by
      simpa [sub_eq_add_neg] using abs_add_le (a + b - c) (-d)
    _ ≤ (|a + b| + |c|) + |d| := by
      gcongr
      simpa [sub_eq_add_neg] using abs_add_le (a + b) (-c)
    _ ≤ ((|a| + |b|) + |c|) + |d| := by
      gcongr
      exact abs_add_le a b
    _ = 4 := by
      dsimp [a, b, c, d]
      simp [abs_quantumIsingSpinSign]
      norm_num


abbrev QuantumIsingSpaceTimeTwoBlockConfig (n A B : Nat) :=
  Fin n -> QuantumIsingTwoBlockConfig A B

noncomputable def quantumIsingTwoBlockVerticalLayerWeight
    (beta h : Real) (n A B : Nat)
    (omega : QuantumIsingSpaceTimeTwoBlockConfig n A B) (t : Fin n) : Real :=
  (∏ i : Fin A, quantumIsingVerticalBondWeight beta h n
      ((omega t).1 i) ((omega (quantumIsingCyclicSucc t)).1 i)) *
    ∏ j : Fin B, quantumIsingVerticalBondWeight beta h n
      ((omega t).2 j) ((omega (quantumIsingCyclicSucc t)).2 j)

noncomputable def quantumIsingTwoBlockLongCylinderWeight
    (beta h : Real) (n A B : Nat)
    (omega : QuantumIsingSpaceTimeTwoBlockConfig n (A + 1) (B + 1)) : Real :=
  ∏ t : Fin n,
    Real.exp (beta / (4 * n) *
      quantumIsingTwoBlockLongInteraction A B (omega t)) *
      quantumIsingTwoBlockVerticalLayerWeight beta h n (A + 1) (B + 1) omega t

noncomputable def quantumIsingTwoBlockPeriodicCylinderWeight
    (beta h : Real) (n A B : Nat)
    (omega : QuantumIsingSpaceTimeTwoBlockConfig n (A + 1) (B + 1)) : Real :=
  ∏ t : Fin n,
    Real.exp (beta / (4 * n) *
      quantumIsingTwoBlockPeriodicInteraction A B (omega t)) *
      quantumIsingTwoBlockVerticalLayerWeight beta h n (A + 1) (B + 1) omega t

private theorem quantumIsingTwoBlockLongLayer_le
    (beta h : Real) (n A B : Nat) (hbeta : 0 ≤ beta)
    (omega : QuantumIsingSpaceTimeTwoBlockConfig (n + 1) (A + 1) (B + 1))
    (t : Fin (n + 1)) :
    Real.exp (beta / (4 * (n + 1)) *
        quantumIsingTwoBlockLongInteraction A B (omega t)) *
        quantumIsingTwoBlockVerticalLayerWeight beta h (n + 1) (A + 1) (B + 1) omega t ≤
      Real.exp (beta / (n + 1)) *
        (Real.exp (beta / (4 * (n + 1)) *
          quantumIsingTwoBlockPeriodicInteraction A B (omega t)) *
          quantumIsingTwoBlockVerticalLayerWeight beta h (n + 1) (A + 1) (B + 1) omega t) := by
  have hdiff := quantumIsingTwoBlockInteraction_sub_le A B (omega t)
  have hinter : quantumIsingTwoBlockLongInteraction A B (omega t) ≤
      quantumIsingTwoBlockPeriodicInteraction A B (omega t) + 4 := by
    rw [abs_le] at hdiff
    linarith
  have hc : 0 ≤ beta / (4 * (n + 1 : Real)) := by positivity
  have hexp : Real.exp (beta / (4 * (n + 1)) *
      quantumIsingTwoBlockLongInteraction A B (omega t)) ≤
      Real.exp (beta / (n + 1)) *
        Real.exp (beta / (4 * (n + 1)) *
          quantumIsingTwoBlockPeriodicInteraction A B (omega t)) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    calc
      _ ≤ beta / (4 * (n + 1 : Real)) *
          (quantumIsingTwoBlockPeriodicInteraction A B (omega t) + 4) :=
        mul_le_mul_of_nonneg_left hinter hc
      _ = _ := by field_simp; ring
  have hv : 0 ≤ quantumIsingTwoBlockVerticalLayerWeight beta h
      (n + 1) (A + 1) (B + 1) omega t := by
    unfold quantumIsingTwoBlockVerticalLayerWeight quantumIsingVerticalBondWeight
    positivity
  calc
    _ ≤ (Real.exp (beta / (n + 1)) *
        Real.exp (beta / (4 * (n + 1)) *
          quantumIsingTwoBlockPeriodicInteraction A B (omega t))) *
        quantumIsingTwoBlockVerticalLayerWeight beta h (n + 1) (A + 1) (B + 1) omega t :=
      mul_le_mul_of_nonneg_right hexp hv
    _ = _ := by ring

private theorem quantumIsingTwoBlockPeriodicLayer_le
    (beta h : Real) (n A B : Nat) (hbeta : 0 ≤ beta)
    (omega : QuantumIsingSpaceTimeTwoBlockConfig (n + 1) (A + 1) (B + 1))
    (t : Fin (n + 1)) :
    Real.exp (beta / (4 * (n + 1)) *
        quantumIsingTwoBlockPeriodicInteraction A B (omega t)) *
        quantumIsingTwoBlockVerticalLayerWeight beta h (n + 1) (A + 1) (B + 1) omega t ≤
      Real.exp (beta / (n + 1)) *
        (Real.exp (beta / (4 * (n + 1)) *
          quantumIsingTwoBlockLongInteraction A B (omega t)) *
          quantumIsingTwoBlockVerticalLayerWeight beta h (n + 1) (A + 1) (B + 1) omega t) := by
  have hdiff := quantumIsingTwoBlockInteraction_sub_le A B (omega t)
  have hinter : quantumIsingTwoBlockPeriodicInteraction A B (omega t) ≤
      quantumIsingTwoBlockLongInteraction A B (omega t) + 4 := by
    rw [abs_le] at hdiff
    linarith
  have hc : 0 ≤ beta / (4 * (n + 1 : Real)) := by positivity
  have hexp : Real.exp (beta / (4 * (n + 1)) *
      quantumIsingTwoBlockPeriodicInteraction A B (omega t)) ≤
      Real.exp (beta / (n + 1)) *
        Real.exp (beta / (4 * (n + 1)) *
          quantumIsingTwoBlockLongInteraction A B (omega t)) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    calc
      _ ≤ beta / (4 * (n + 1 : Real)) *
          (quantumIsingTwoBlockLongInteraction A B (omega t) + 4) :=
        mul_le_mul_of_nonneg_left hinter hc
      _ = _ := by field_simp; ring
  have hv : 0 ≤ quantumIsingTwoBlockVerticalLayerWeight beta h
      (n + 1) (A + 1) (B + 1) omega t := by
    unfold quantumIsingTwoBlockVerticalLayerWeight quantumIsingVerticalBondWeight
    positivity
  calc
    _ ≤ (Real.exp (beta / (n + 1)) *
        Real.exp (beta / (4 * (n + 1)) *
          quantumIsingTwoBlockLongInteraction A B (omega t))) *
        quantumIsingTwoBlockVerticalLayerWeight beta h (n + 1) (A + 1) (B + 1) omega t :=
      mul_le_mul_of_nonneg_right hexp hv
    _ = _ := by ring

theorem quantumIsingTwoBlockLongCylinderWeight_le
    (beta h : Real) (n A B : Nat) (hbeta : 0 ≤ beta)
    (omega : QuantumIsingSpaceTimeTwoBlockConfig (n + 1) (A + 1) (B + 1)) :
    quantumIsingTwoBlockLongCylinderWeight beta h (n + 1) A B omega ≤
      Real.exp beta *
        quantumIsingTwoBlockPeriodicCylinderWeight beta h (n + 1) A B omega := by
  unfold quantumIsingTwoBlockLongCylinderWeight quantumIsingTwoBlockPeriodicCylinderWeight
  norm_num only [Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ ∏ t : Fin (n + 1), Real.exp (beta / (n + 1)) *
        (Real.exp (beta / (4 * (n + 1)) *
          quantumIsingTwoBlockPeriodicInteraction A B (omega t)) *
          quantumIsingTwoBlockVerticalLayerWeight beta h (n + 1) (A + 1) (B + 1) omega t) := by
      apply Finset.prod_le_prod
      · intro t _
        unfold quantumIsingTwoBlockVerticalLayerWeight quantumIsingVerticalBondWeight
        positivity
      · intro t _
        exact quantumIsingTwoBlockLongLayer_le beta h n A B hbeta omega t
    _ = Real.exp beta * ∏ t : Fin (n + 1),
        Real.exp (beta / (4 * (n + 1)) *
          quantumIsingTwoBlockPeriodicInteraction A B (omega t)) *
          quantumIsingTwoBlockVerticalLayerWeight beta h (n + 1) (A + 1) (B + 1) omega t := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← Real.exp_nat_mul]
      congr 2
      push_cast
      field_simp

theorem quantumIsingTwoBlockPeriodicCylinderWeight_le
    (beta h : Real) (n A B : Nat) (hbeta : 0 ≤ beta)
    (omega : QuantumIsingSpaceTimeTwoBlockConfig (n + 1) (A + 1) (B + 1)) :
    quantumIsingTwoBlockPeriodicCylinderWeight beta h (n + 1) A B omega ≤
      Real.exp beta *
        quantumIsingTwoBlockLongCylinderWeight beta h (n + 1) A B omega := by
  unfold quantumIsingTwoBlockLongCylinderWeight quantumIsingTwoBlockPeriodicCylinderWeight
  norm_num only [Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ ∏ t : Fin (n + 1), Real.exp (beta / (n + 1)) *
        (Real.exp (beta / (4 * (n + 1)) *
          quantumIsingTwoBlockLongInteraction A B (omega t)) *
          quantumIsingTwoBlockVerticalLayerWeight beta h (n + 1) (A + 1) (B + 1) omega t) := by
      apply Finset.prod_le_prod
      · intro t _
        unfold quantumIsingTwoBlockVerticalLayerWeight quantumIsingVerticalBondWeight
        positivity
      · intro t _
        exact quantumIsingTwoBlockPeriodicLayer_le beta h n A B hbeta omega t
    _ = Real.exp beta * ∏ t : Fin (n + 1),
        Real.exp (beta / (4 * (n + 1)) *
          quantumIsingTwoBlockLongInteraction A B (omega t)) *
          quantumIsingTwoBlockVerticalLayerWeight beta h (n + 1) (A + 1) (B + 1) omega t := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← Real.exp_nat_mul]
      congr 2
      push_cast
      field_simp


def quantumIsingSpaceTimeSumBlockEquiv (n A B : Nat) :
    (Fin n -> QuantumIsingChainConfig (A + B)) ≃
      QuantumIsingSpaceTimeTwoBlockConfig n A B :=
  Equiv.piCongrRight (fun _ : Fin n => quantumIsingSumBlockEquiv A B)

@[simp] theorem quantumIsingSpaceTimeSumBlockEquiv_symm_left
    (n A B : Nat) (omega : QuantumIsingSpaceTimeTwoBlockConfig n A B)
    (t : Fin n) (i : Fin A) :
    (quantumIsingSpaceTimeSumBlockEquiv n A B).symm omega t
        (finSumFinEquiv (Sum.inl i)) = (omega t).1 i := by
  change (quantumIsingSumBlockEquiv A B).symm (omega t)
    (finSumFinEquiv (Sum.inl i)) = (omega t).1 i
  exact quantumIsingSumBlockEquiv_symm_left A B (omega t) i

@[simp] theorem quantumIsingSpaceTimeSumBlockEquiv_symm_right
    (n A B : Nat) (omega : QuantumIsingSpaceTimeTwoBlockConfig n A B)
    (t : Fin n) (j : Fin B) :
    (quantumIsingSpaceTimeSumBlockEquiv n A B).symm omega t
        (finSumFinEquiv (Sum.inr j)) = (omega t).2 j := by
  change (quantumIsingSumBlockEquiv A B).symm (omega t)
    (finSumFinEquiv (Sum.inr j)) = (omega t).2 j
  exact quantumIsingSumBlockEquiv_symm_right A B (omega t) j

@[simp] theorem quantumIsingSpaceTimeSumBlockEquiv_symm_castAdd
    (n A B : Nat) (omega : QuantumIsingSpaceTimeTwoBlockConfig n A B)
    (t : Fin n) (i : Fin A) :
    (quantumIsingSpaceTimeSumBlockEquiv n A B).symm omega t
        (Fin.castAdd B i) = (omega t).1 i := by
  change (quantumIsingSpaceTimeSumBlockEquiv n A B).symm omega t
    (finSumFinEquiv (Sum.inl i)) = (omega t).1 i
  exact quantumIsingSpaceTimeSumBlockEquiv_symm_left n A B omega t i

@[simp] theorem quantumIsingSpaceTimeSumBlockEquiv_symm_natAdd
    (n A B : Nat) (omega : QuantumIsingSpaceTimeTwoBlockConfig n A B)
    (t : Fin n) (j : Fin B) :
    (quantumIsingSpaceTimeSumBlockEquiv n A B).symm omega t
        (Fin.natAdd A j) = (omega t).2 j := by
  change (quantumIsingSpaceTimeSumBlockEquiv n A B).symm omega t
    (finSumFinEquiv (Sum.inr j)) = (omega t).2 j
  exact quantumIsingSpaceTimeSumBlockEquiv_symm_right n A B omega t j

theorem quantumIsingClassicalCylinderWeight_sumBlockEquiv
    (beta h : Real) (n A B : Nat)
    (omega : QuantumIsingSpaceTimeTwoBlockConfig n (A + 1) (B + 1)) :
    quantumIsingClassicalCylinderWeight beta h n ((A + 1) + (B + 1))
        ((quantumIsingSpaceTimeSumBlockEquiv n (A + 1) (B + 1)).symm omega) =
      quantumIsingTwoBlockLongCylinderWeight beta h n A B omega := by
  unfold quantumIsingClassicalCylinderWeight
  unfold quantumIsingTwoBlockLongCylinderWeight
  apply Finset.prod_congr rfl
  intro t _
  unfold quantumIsingSpatialTrotterWeight
  rw [show quantumIsingChainInteraction ((A + 1) + (B + 1))
      ((quantumIsingSpaceTimeSumBlockEquiv n (A + 1) (B + 1)).symm omega t) =
        quantumIsingTwoBlockLongInteraction A B (omega t) by rfl]
  congr 1
  unfold quantumIsingTwoBlockVerticalLayerWeight
  calc
    (∏ q : Fin ((A + 1) + (B + 1)),
      quantumIsingVerticalBondWeight beta h n
        ((quantumIsingSpaceTimeSumBlockEquiv n (A + 1) (B + 1)).symm omega t q)
        ((quantumIsingSpaceTimeSumBlockEquiv n (A + 1) (B + 1)).symm omega
          (quantumIsingCyclicSucc t) q)) =
      ∏ s : Fin (A + 1) ⊕ Fin (B + 1),
        quantumIsingVerticalBondWeight beta h n
          ((quantumIsingSpaceTimeSumBlockEquiv n (A + 1) (B + 1)).symm omega t
            (finSumFinEquiv s))
          ((quantumIsingSpaceTimeSumBlockEquiv n (A + 1) (B + 1)).symm omega
            (quantumIsingCyclicSucc t) (finSumFinEquiv s)) := by
      simpa using (Equiv.prod_comp finSumFinEquiv
        (fun q : Fin ((A + 1) + (B + 1)) =>
          quantumIsingVerticalBondWeight beta h n
            ((quantumIsingSpaceTimeSumBlockEquiv n (A + 1) (B + 1)).symm omega t q)
            ((quantumIsingSpaceTimeSumBlockEquiv n (A + 1) (B + 1)).symm omega
              (quantumIsingCyclicSucc t) q))).symm
    _ = (∏ i : Fin (A + 1), quantumIsingVerticalBondWeight beta h n
          ((omega t).1 i) ((omega (quantumIsingCyclicSucc t)).1 i)) *
        ∏ j : Fin (B + 1), quantumIsingVerticalBondWeight beta h n
          ((omega t).2 j) ((omega (quantumIsingCyclicSucc t)).2 j) := by
      rw [Fintype.prod_sum_type]
      congr 1 <;> apply Finset.prod_congr rfl <;> intro x _ <;> simp

theorem quantumIsingTwoBlockPeriodicCylinderWeight_eq_mul
    (beta h : Real) (n A B : Nat)
    (omega : QuantumIsingSpaceTimeTwoBlockConfig n (A + 1) (B + 1)) :
    quantumIsingTwoBlockPeriodicCylinderWeight beta h n A B omega =
      quantumIsingClassicalCylinderWeight beta h n (A + 1) (fun t => (omega t).1) *
        quantumIsingClassicalCylinderWeight beta h n (B + 1) (fun t => (omega t).2) := by
  unfold quantumIsingTwoBlockPeriodicCylinderWeight
  unfold quantumIsingClassicalCylinderWeight
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro t _
  unfold quantumIsingTwoBlockPeriodicInteraction
  unfold quantumIsingTwoBlockVerticalLayerWeight
  unfold quantumIsingSpatialTrotterWeight
  rw [show beta / (4 * (n : Real)) *
      (quantumIsingChainInteraction (A + 1) (omega t).1 +
        quantumIsingChainInteraction (B + 1) (omega t).2) =
      beta / (4 * (n : Real)) * quantumIsingChainInteraction (A + 1) (omega t).1 +
        beta / (4 * (n : Real)) * quantumIsingChainInteraction (B + 1) (omega t).2 by ring,
    Real.exp_add]
  ring

def quantumIsingSpaceTimeTwoBlockSplitEquiv (n A B : Nat) :
    QuantumIsingSpaceTimeTwoBlockConfig n A B ≃
      (Fin n -> QuantumIsingChainConfig A) ×
        (Fin n -> QuantumIsingChainConfig B) where
  toFun omega := (fun t => (omega t).1, fun t => (omega t).2)
  invFun pair t := (pair.1 t, pair.2 t)
  left_inv _ := rfl
  right_inv _ := rfl

theorem quantumIsingTwoBlockPeriodicCylinderWeight_sum
    (beta h : Real) (n A B : Nat) :
    (∑ omega : QuantumIsingSpaceTimeTwoBlockConfig n (A + 1) (B + 1),
      quantumIsingTwoBlockPeriodicCylinderWeight beta h n A B omega) =
      quantumIsingClassicalCylinderPartition beta h n (A + 1) *
        quantumIsingClassicalCylinderPartition beta h n (B + 1) := by
  let e := quantumIsingSpaceTimeTwoBlockSplitEquiv n (A + 1) (B + 1)
  calc
    (∑ omega : QuantumIsingSpaceTimeTwoBlockConfig n (A + 1) (B + 1),
      quantumIsingTwoBlockPeriodicCylinderWeight beta h n A B omega) =
      ∑ pair : (Fin n -> QuantumIsingChainConfig (A + 1)) ×
          (Fin n -> QuantumIsingChainConfig (B + 1)),
        quantumIsingTwoBlockPeriodicCylinderWeight beta h n A B (e.symm pair) := by
      simpa using (Equiv.sum_comp e
        (fun pair : (Fin n -> QuantumIsingChainConfig (A + 1)) ×
            (Fin n -> QuantumIsingChainConfig (B + 1)) =>
          quantumIsingTwoBlockPeriodicCylinderWeight beta h n A B (e.symm pair)))
    _ = ∑ pair : (Fin n -> QuantumIsingChainConfig (A + 1)) ×
          (Fin n -> QuantumIsingChainConfig (B + 1)),
        quantumIsingClassicalCylinderWeight beta h n (A + 1) pair.1 *
          quantumIsingClassicalCylinderWeight beta h n (B + 1) pair.2 := by
      apply Finset.sum_congr rfl
      intro pair _
      rw [quantumIsingTwoBlockPeriodicCylinderWeight_eq_mul]
      rfl
    _ = (∑ left : Fin n -> QuantumIsingChainConfig (A + 1),
          quantumIsingClassicalCylinderWeight beta h n (A + 1) left) *
        ∑ right : Fin n -> QuantumIsingChainConfig (B + 1),
          quantumIsingClassicalCylinderWeight beta h n (B + 1) right := by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
    _ = _ := by rfl

private theorem quantumIsingClassicalCylinderPartition_twoBlock_sum
    (beta h : Real) (n A B : Nat) :
    quantumIsingClassicalCylinderPartition beta h n ((A + 1) + (B + 1)) =
      ∑ omega : QuantumIsingSpaceTimeTwoBlockConfig n (A + 1) (B + 1),
        quantumIsingTwoBlockLongCylinderWeight beta h n A B omega := by
  unfold quantumIsingClassicalCylinderPartition
  let e := quantumIsingSpaceTimeSumBlockEquiv n (A + 1) (B + 1)
  calc
    (∑ omega : Fin n -> QuantumIsingChainConfig ((A + 1) + (B + 1)),
      quantumIsingClassicalCylinderWeight beta h n ((A + 1) + (B + 1)) omega) =
      ∑ pair : QuantumIsingSpaceTimeTwoBlockConfig n (A + 1) (B + 1),
        quantumIsingClassicalCylinderWeight beta h n ((A + 1) + (B + 1))
          (e.symm pair) := by
      simpa using (Equiv.sum_comp e
        (fun pair : QuantumIsingSpaceTimeTwoBlockConfig n (A + 1) (B + 1) =>
          quantumIsingClassicalCylinderWeight beta h n ((A + 1) + (B + 1))
            (e.symm pair)))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro pair _
      exact quantumIsingClassicalCylinderWeight_sumBlockEquiv beta h n A B pair



theorem quantumIsingClassicalCylinderPartition_add_upper
    (beta h : Real) (n A B : Nat) (hbeta : 0 ≤ beta) :
    quantumIsingClassicalCylinderPartition beta h (n + 1) ((A + 1) + (B + 1)) ≤
      Real.exp beta *
        (quantumIsingClassicalCylinderPartition beta h (n + 1) (A + 1) *
          quantumIsingClassicalCylinderPartition beta h (n + 1) (B + 1)) := by
  rw [quantumIsingClassicalCylinderPartition_twoBlock_sum]
  calc
    _ ≤ ∑ omega : QuantumIsingSpaceTimeTwoBlockConfig (n + 1) (A + 1) (B + 1),
        Real.exp beta * quantumIsingTwoBlockPeriodicCylinderWeight beta h (n + 1) A B omega := by
      apply Finset.sum_le_sum
      intro omega _
      exact quantumIsingTwoBlockLongCylinderWeight_le beta h n A B hbeta omega
    _ = Real.exp beta *
        ∑ omega : QuantumIsingSpaceTimeTwoBlockConfig (n + 1) (A + 1) (B + 1),
          quantumIsingTwoBlockPeriodicCylinderWeight beta h (n + 1) A B omega := by
      rw [Finset.mul_sum]
    _ = _ := by rw [quantumIsingTwoBlockPeriodicCylinderWeight_sum]


theorem quantumIsingClassicalCylinderPartition_add_lower
    (beta h : Real) (n A B : Nat) (hbeta : 0 ≤ beta) :
    Real.exp (-beta) *
        (quantumIsingClassicalCylinderPartition beta h (n + 1) (A + 1) *
          quantumIsingClassicalCylinderPartition beta h (n + 1) (B + 1)) ≤
      quantumIsingClassicalCylinderPartition beta h (n + 1) ((A + 1) + (B + 1)) := by
  have hsum :
      quantumIsingClassicalCylinderPartition beta h (n + 1) (A + 1) *
          quantumIsingClassicalCylinderPartition beta h (n + 1) (B + 1) ≤
        Real.exp beta *
          quantumIsingClassicalCylinderPartition beta h (n + 1) ((A + 1) + (B + 1)) := by
    rw [quantumIsingClassicalCylinderPartition_twoBlock_sum,
      ← quantumIsingTwoBlockPeriodicCylinderWeight_sum]
    calc
      _ ≤ ∑ omega : QuantumIsingSpaceTimeTwoBlockConfig (n + 1) (A + 1) (B + 1),
          Real.exp beta * quantumIsingTwoBlockLongCylinderWeight beta h (n + 1) A B omega := by
        apply Finset.sum_le_sum
        intro omega _
        exact quantumIsingTwoBlockPeriodicCylinderWeight_le beta h n A B hbeta omega
      _ = _ := by rw [Finset.mul_sum]
  calc
    _ ≤ Real.exp (-beta) *
        (Real.exp beta *
          quantumIsingClassicalCylinderPartition beta h (n + 1) ((A + 1) + (B + 1))) :=
      mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
    _ = _ := by
      rw [← mul_assoc, ← Real.exp_add]
      simp


theorem quantumIsingClassicalCylinderPartition_pos
    (beta h : Real) (n L : Nat) :
    0 < quantumIsingClassicalCylinderPartition beta h n L := by
  unfold quantumIsingClassicalCylinderPartition
  apply Finset.sum_pos
  · intro omega _
    unfold quantumIsingClassicalCylinderWeight
    apply Finset.prod_pos
    intro t _
    unfold quantumIsingSpatialTrotterWeight quantumIsingVerticalBondWeight
    positivity
  · exact Finset.univ_nonempty



noncomputable def quantumIsingClassicalLogPartitionSequence
    (beta h : Real) (n : Nat) (L : Nat) : Real :=
  if L = 0 then 0 else
    Real.log (quantumIsingClassicalCylinderPartition beta h (n + 1) L)



theorem quantumIsingClassicalLogPartitionSequence_almostAdditive
    (beta h : Real) (n : Nat) (hbeta : 0 ≤ beta) :
    QuantumIsingAlmostAdditive
      (quantumIsingClassicalLogPartitionSequence beta h n) beta := by
  intro m l
  rcases m.eq_zero_or_pos with rfl | hm
  · simpa [quantumIsingClassicalLogPartitionSequence] using hbeta
  rcases l.eq_zero_or_pos with rfl | hl
  · simpa [quantumIsingClassicalLogPartitionSequence] using hbeta
  obtain ⟨A, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  obtain ⟨B, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne'
  simp only [quantumIsingClassicalLogPartitionSequence, Nat.add_eq_zero_iff,
    Nat.succ_ne_zero, false_and, ↓reduceIte]
  let ZA := quantumIsingClassicalCylinderPartition beta h (n + 1) (A + 1)
  let ZB := quantumIsingClassicalCylinderPartition beta h (n + 1) (B + 1)
  let ZAB := quantumIsingClassicalCylinderPartition beta h (n + 1) ((A + 1) + (B + 1))
  have hZA : 0 < ZA := quantumIsingClassicalCylinderPartition_pos _ _ _ _
  have hZB : 0 < ZB := quantumIsingClassicalCylinderPartition_pos _ _ _ _
  have hZAB : 0 < ZAB := quantumIsingClassicalCylinderPartition_pos _ _ _ _
  have hu := quantumIsingClassicalCylinderPartition_add_upper beta h n A B hbeta
  have hlower := quantumIsingClassicalCylinderPartition_add_lower beta h n A B hbeta
  change |Real.log ZAB - Real.log ZA - Real.log ZB| ≤ beta
  rw [abs_le]
  constructor
  · have hlog := Real.strictMonoOn_log.monotoneOn
        (mul_pos (Real.exp_pos _) (mul_pos hZA hZB)) hZAB hlower
    rw [Real.log_mul (Real.exp_ne_zero _) (mul_ne_zero hZA.ne' hZB.ne'),
      Real.log_exp, Real.log_mul hZA.ne' hZB.ne'] at hlog
    linarith
  · have hlog := Real.strictMonoOn_log.monotoneOn hZAB
        (mul_pos (Real.exp_pos _) (mul_pos hZA hZB)) hu
    rw [Real.log_mul (Real.exp_ne_zero _) (mul_ne_zero hZA.ne' hZB.ne'),
      Real.log_exp, Real.log_mul hZA.ne' hZB.ne'] at hlog
    linarith


noncomputable def quantumIsingClassicalLogPressureLimit
    (beta h : Real) (n : Nat) (hbeta : 0 ≤ beta) : Real :=
  (quantumIsingClassicalLogPartitionSequence_almostAdditive beta h n hbeta).limit


theorem quantumIsingClassicalLogPressure_tendsto
    (beta h : Real) (n : Nat) (hbeta : 0 ≤ beta) :
    Tendsto
      (fun L : Nat => quantumIsingClassicalLogPartitionSequence beta h n L / L)
      atTop (nhds (quantumIsingClassicalLogPressureLimit beta h n hbeta)) :=
  (quantumIsingClassicalLogPartitionSequence_almostAdditive beta h n hbeta).tendsto_limit



theorem quantumIsingClassicalLogPressureLimit_sub_finite_le
    (beta h : Real) (n L : Nat) (hbeta : 0 ≤ beta) (hL : L ≠ 0) :
    |quantumIsingClassicalLogPressureLimit beta h n hbeta -
      Real.log (quantumIsingClassicalCylinderPartition beta h (n + 1) L) / L| ≤
        beta / L := by
  have h := (quantumIsingClassicalLogPartitionSequence_almostAdditive
    beta h n hbeta).abs_limit_sub_div_le hL
  simpa [quantumIsingClassicalLogPressureLimit,
    quantumIsingClassicalLogPartitionSequence, hL] using h



theorem quantumIsingClassicalLogPressureLimit_sub_finite_le_sharp
    (beta h : Real) (n L : Nat) (hbeta : 0 ≤ beta) (hL : L ≠ 0) :
    |quantumIsingClassicalLogPressureLimit beta h n hbeta -
      Real.log (quantumIsingClassicalCylinderPartition beta h (n + 1) L) / L| ≤
        beta / (2 * L) := by
  obtain ⟨A, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hL
  let Z := fun W => quantumIsingClassicalCylinderPartition beta h (n + 1) W
  have hZ (W : Nat) : 0 < Z W :=
    quantumIsingClassicalCylinderPartition_pos _ _ _ _
  have hfinite (k : Nat) :
      |quantumIsingClassicalLogPartitionSequence beta h n ((k + 1) * (A + 1)) /
          (((k + 1) * (A + 1) : Nat) : Real) -
        Real.log (Z (A + 1)) / (A + 1 : Real)| ≤
          beta / (2 * (A + 1 : Real)) := by
    have hu :=
      quantumIsingClassicalCylinderPartition_block_upper beta h n k A hbeta
    have hl :=
      quantumIsingClassicalCylinderPartition_block_lower beta h n k A hbeta
    have hrep : 0 < Z ((k + 1) * (A + 1)) := hZ _
    have hbase : 0 < Z (A + 1) := hZ _
    have huLog := Real.strictMonoOn_log.monotoneOn hrep
      (mul_pos (pow_pos hbase _) (Real.exp_pos _)) hu
    have hlLog := Real.strictMonoOn_log.monotoneOn
      (mul_pos (pow_pos hbase _) (Real.exp_pos _)) hrep hl
    rw [Real.log_mul (pow_ne_zero _ hbase.ne') (Real.exp_ne_zero _),
      Real.log_pow, Real.log_exp] at huLog hlLog
    have hwidth : (k + 1) * (A + 1) ≠ 0 :=
      Nat.mul_ne_zero (by omega) (by omega)
    simp only [quantumIsingClassicalLogPartitionSequence, hwidth, ↓reduceIte]
    rw [abs_le]
    constructor <;> push_cast at * <;>
      field_simp [show (k : Real) + 1 ≠ 0 by positivity,
        show (A : Real) + 1 ≠ 0 by positivity] at * <;> nlinarith
  have hindex : Tendsto (fun k : Nat => (k + 1) * (A + 1)) atTop atTop := by
    rw [tendsto_atTop]
    intro W
    filter_upwards [eventually_ge_atTop W] with k hk
    nlinarith
  have hpressure := quantumIsingClassicalLogPressure_tendsto beta h n hbeta
  have hsubseq := hpressure.comp hindex
  have hdiff := hsubseq.sub (tendsto_const_nhds : Tendsto
    (fun _ : Nat => Real.log (Z (A + 1)) / (A + 1 : Real)) atTop
      (nhds (Real.log (Z (A + 1)) / (A + 1 : Real))))
  have habs := hdiff.abs
  have hfinal := le_of_tendsto habs (Filter.Eventually.of_forall hfinite)
  simpa [Z, Nat.cast_add, Nat.cast_one] using hfinal

end StatMech.FrontierA
