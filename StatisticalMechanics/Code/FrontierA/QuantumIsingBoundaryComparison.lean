/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.QuantumIsingTrotterCylinder











open scoped BigOperators

namespace StatMech.FrontierA

abbrev QuantumIsingBlockConfig (k L : Nat) :=
  Fin k -> QuantumIsingChainConfig L

def quantumIsingBlockEquiv (k L : Nat) :
    QuantumIsingChainConfig (k * L) ≃ QuantumIsingBlockConfig k L where
  toFun sigma b i := sigma (finProdFinEquiv (b, i))
  invFun sigma j :=
    sigma (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  left_inv sigma := by
    funext j
    change sigma (finProdFinEquiv (finProdFinEquiv.symm j)) = sigma j
    rw [Equiv.apply_symm_apply]
  right_inv sigma := by
    funext b i
    change sigma (finProdFinEquiv.symm (finProdFinEquiv (b, i))).1
      (finProdFinEquiv.symm (finProdFinEquiv (b, i))).2 = sigma b i
    rw [Equiv.symm_apply_apply]

@[simp] theorem quantumIsingBlockEquiv_apply (k L : Nat)
    (sigma : QuantumIsingChainConfig (k * L)) (b : Fin k) (i : Fin L) :
    quantumIsingBlockEquiv k L sigma b i = sigma (finProdFinEquiv (b, i)) := by
  rfl

@[simp] theorem cyclicSucc_finProd_castSucc
    (k L : Nat) (b : Fin (k + 1)) (i : Fin L) :
    quantumIsingCyclicSucc (finProdFinEquiv (b, i.castSucc)) =
      finProdFinEquiv (b, i.succ) := by
  apply Fin.ext
  change (i.val + (L + 1) * b.val + 1) % ((k + 1) * (L + 1)) =
    i.val + 1 + (L + 1) * b.val
  rw [Nat.mod_eq_of_lt]
  · ring
  · have hi : i.val + 1 ≤ L := by omega
    have hb0 : b.val + 1 ≤ k + 1 := by omega
    have hb := Nat.mul_le_mul_left (L + 1) hb0
    nlinarith

@[simp] theorem cyclicSucc_finProd_last_castSucc
    (k L : Nat) (b : Fin k) :
    quantumIsingCyclicSucc
        (finProdFinEquiv (b.castSucc, Fin.last L)) =
      finProdFinEquiv (b.succ, (0 : Fin (L + 1))) := by
  apply Fin.ext
  simp [quantumIsingCyclicSucc, finProdFinEquiv]
  have hb : b.val + 1 < k + 1 := by omega
  rw [Nat.mod_eq_of_lt]
  · ring
  · nlinarith [b.isLt]

@[simp] theorem cyclicSucc_finProd_last_last
    (k L : Nat) :
    quantumIsingCyclicSucc
        (finProdFinEquiv (Fin.last k, Fin.last L)) =
      finProdFinEquiv ((0 : Fin (k + 1)), (0 : Fin (L + 1))) := by
  apply Fin.ext
  change (L + (L + 1) * k + 1) % ((k + 1) * (L + 1)) = 0
  convert Nat.mod_self ((k + 1) * (L + 1)) using 2; ring

noncomputable def quantumIsingBlockOpenInteraction (k L : Nat)
    (sigma : QuantumIsingBlockConfig (k + 1) (L + 1)) : Real :=
  ∑ b : Fin (k + 1), ∑ i : Fin L,
    quantumIsingSpinSign (sigma b i.castSucc) *
      quantumIsingSpinSign (sigma b i.succ)

noncomputable def quantumIsingBlockPeriodicInteraction (k L : Nat)
    (sigma : QuantumIsingBlockConfig (k + 1) (L + 1)) : Real :=
  ∑ b : Fin (k + 1), quantumIsingChainInteraction (L + 1) (sigma b)

noncomputable def quantumIsingBlockLongInteraction (k L : Nat)
    (sigma : QuantumIsingBlockConfig (k + 1) (L + 1)) : Real :=
  quantumIsingChainInteraction ((k + 1) * (L + 1))
    ((quantumIsingBlockEquiv (k + 1) (L + 1)).symm sigma)

@[simp] theorem quantumIsingBlockEquiv_symm_apply (k L : Nat)
    (sigma : QuantumIsingBlockConfig k L) (b : Fin k) (i : Fin L) :
    (quantumIsingBlockEquiv k L).symm sigma (finProdFinEquiv (b, i)) =
      sigma b i := by
  change sigma (finProdFinEquiv.symm (finProdFinEquiv (b, i))).1
    (finProdFinEquiv.symm (finProdFinEquiv (b, i))).2 = sigma b i
  rw [Equiv.symm_apply_apply]

@[simp] theorem quantumIsingCyclicSucc_castSucc
    (L : Nat) (i : Fin L) :
    quantumIsingCyclicSucc i.castSucc = i.succ := by
  apply Fin.ext
  change (i.val + 1) % (L + 1) = i.val + 1
  rw [Nat.mod_eq_of_lt]
  omega

@[simp] theorem quantumIsingCyclicSucc_last (L : Nat) :
    quantumIsingCyclicSucc (Fin.last L) = (0 : Fin (L + 1)) := by
  apply Fin.ext
  change (L + 1) % (L + 1) = 0
  exact Nat.mod_self _

theorem quantumIsingBlockPeriodicInteraction_eq_open_add
    (k L : Nat) (sigma : QuantumIsingBlockConfig (k + 1) (L + 1)) :
    quantumIsingBlockPeriodicInteraction k L sigma =
      quantumIsingBlockOpenInteraction k L sigma +
        ∑ b : Fin (k + 1),
          quantumIsingSpinSign (sigma b (Fin.last L)) *
            quantumIsingSpinSign (sigma b 0) := by 
  unfold quantumIsingBlockPeriodicInteraction quantumIsingBlockOpenInteraction
  have hblock (b : Fin (k + 1)) :
      quantumIsingChainInteraction (L + 1) (sigma b) =
        (∑ i : Fin L,
          quantumIsingSpinSign (sigma b i.castSucc) *
            quantumIsingSpinSign (sigma b i.succ)) +
          quantumIsingSpinSign (sigma b (Fin.last L)) *
            quantumIsingSpinSign (sigma b 0) := by
    unfold quantumIsingChainInteraction
    rw [Fin.sum_univ_castSucc]
    simp
  simp_rw [hblock]
  rw [Finset.sum_add_distrib]

noncomputable def quantumIsingBlockLongSeamInteraction (k L : Nat)
    (sigma : QuantumIsingBlockConfig (k + 1) (L + 1)) : Real :=
  (∑ b : Fin k,
    quantumIsingSpinSign (sigma b.castSucc (Fin.last L)) *
      quantumIsingSpinSign (sigma b.succ 0)) +
    quantumIsingSpinSign (sigma (Fin.last k) (Fin.last L)) *
      quantumIsingSpinSign (sigma 0 0)

theorem quantumIsingBlockLongInteraction_eq_open_add
    (k L : Nat) (sigma : QuantumIsingBlockConfig (k + 1) (L + 1)) :
    quantumIsingBlockLongInteraction k L sigma =
      quantumIsingBlockOpenInteraction k L sigma +
        quantumIsingBlockLongSeamInteraction k L sigma := by
  unfold quantumIsingBlockLongInteraction quantumIsingChainInteraction
  let flat := (quantumIsingBlockEquiv (k + 1) (L + 1)).symm sigma
  calc
    (∑ j : Fin ((k + 1) * (L + 1)),
        quantumIsingSpinSign (flat j) *
          quantumIsingSpinSign (flat (quantumIsingCyclicSucc j))) =
      ∑ p : Fin (k + 1) × Fin (L + 1),
        quantumIsingSpinSign (flat (finProdFinEquiv p)) *
          quantumIsingSpinSign
            (flat (quantumIsingCyclicSucc (finProdFinEquiv p))) := by
      exact (Equiv.sum_comp finProdFinEquiv _).symm
    _ = ∑ b : Fin (k + 1), ∑ i : Fin (L + 1),
        quantumIsingSpinSign (flat (finProdFinEquiv (b, i))) *
          quantumIsingSpinSign
            (flat (quantumIsingCyclicSucc (finProdFinEquiv (b, i)))) := by
      rw [Fintype.sum_prod_type]
    _ = quantumIsingBlockOpenInteraction k L sigma +
        quantumIsingBlockLongSeamInteraction k L sigma := by
      rw [Fin.sum_univ_castSucc]
      have hblocks :
          (∑ b : Fin k, ∑ i : Fin (L + 1),
            quantumIsingSpinSign (flat (finProdFinEquiv (b.castSucc, i))) *
              quantumIsingSpinSign
                (flat (quantumIsingCyclicSucc
                  (finProdFinEquiv (b.castSucc, i))))) =
            ∑ b : Fin k,
              ((∑ i : Fin L,
                quantumIsingSpinSign (sigma b.castSucc i.castSucc) *
                  quantumIsingSpinSign (sigma b.castSucc i.succ)) +
                quantumIsingSpinSign (sigma b.castSucc (Fin.last L)) *
                  quantumIsingSpinSign (sigma b.succ 0)) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [Fin.sum_univ_castSucc]
        congr 1
        · apply Finset.sum_congr rfl
          intro i _
          rw [cyclicSucc_finProd_castSucc]
          simp [flat]
        · rw [cyclicSucc_finProd_last_castSucc]
          simp [flat]
      have hlast :
          (∑ i : Fin (L + 1),
            quantumIsingSpinSign (flat (finProdFinEquiv (Fin.last k, i))) *
              quantumIsingSpinSign
                (flat (quantumIsingCyclicSucc
                  (finProdFinEquiv (Fin.last k, i))))) =
            (∑ i : Fin L,
              quantumIsingSpinSign (sigma (Fin.last k) i.castSucc) *
                quantumIsingSpinSign (sigma (Fin.last k) i.succ)) +
              quantumIsingSpinSign (sigma (Fin.last k) (Fin.last L)) *
                quantumIsingSpinSign (sigma 0 0) := by
        rw [Fin.sum_univ_castSucc]
        congr 1
        · apply Finset.sum_congr rfl
          intro i _
          rw [cyclicSucc_finProd_castSucc]
          simp [flat]
        · rw [cyclicSucc_finProd_last_last]
          simp [flat]
      rw [hblocks, hlast]
      simp only [quantumIsingBlockOpenInteraction,
        quantumIsingBlockLongSeamInteraction]
      rw [Fin.sum_univ_castSucc, Finset.sum_add_distrib]
      ring

@[simp] theorem abs_quantumIsingSpinSign (s : Bool) :
    |quantumIsingSpinSign s| = 1 := by
  cases s <;> norm_num [quantumIsingSpinSign]

private theorem abs_quantumIsingBond (s t : Bool) :
    |quantumIsingSpinSign s * quantumIsingSpinSign t| = 1 := by
  rw [abs_mul, abs_quantumIsingSpinSign, abs_quantumIsingSpinSign, mul_one]

private theorem abs_blockPeriodicSeam_le
    (k L : Nat) (sigma : QuantumIsingBlockConfig (k + 1) (L + 1)) :
    |∑ b : Fin (k + 1),
      quantumIsingSpinSign (sigma b (Fin.last L)) *
        quantumIsingSpinSign (sigma b 0)| ≤ (k + 1 : Real) := by
  calc
    |_|
        ≤ ∑ b : Fin (k + 1),
            |quantumIsingSpinSign (sigma b (Fin.last L)) *
              quantumIsingSpinSign (sigma b 0)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ _b : Fin (k + 1), (1 : Real) := by
      apply Finset.sum_congr rfl
      intro b _
      exact abs_quantumIsingBond _ _
    _ = (k + 1 : Real) := by simp

private theorem abs_blockLongSeam_le
    (k L : Nat) (sigma : QuantumIsingBlockConfig (k + 1) (L + 1)) :
    |quantumIsingBlockLongSeamInteraction k L sigma| ≤ (k + 1 : Real) := by
  unfold quantumIsingBlockLongSeamInteraction
  calc
    |(∑ b : Fin k,
        quantumIsingSpinSign (sigma b.castSucc (Fin.last L)) *
          quantumIsingSpinSign (sigma b.succ 0)) +
        quantumIsingSpinSign (sigma (Fin.last k) (Fin.last L)) *
          quantumIsingSpinSign (sigma 0 0)| ≤
      |∑ b : Fin k,
        quantumIsingSpinSign (sigma b.castSucc (Fin.last L)) *
          quantumIsingSpinSign (sigma b.succ 0)| +
        |quantumIsingSpinSign (sigma (Fin.last k) (Fin.last L)) *
          quantumIsingSpinSign (sigma 0 0)| := abs_add_le _ _
    _ ≤ (∑ b : Fin k,
        |quantumIsingSpinSign (sigma b.castSucc (Fin.last L)) *
          quantumIsingSpinSign (sigma b.succ 0)|) + 1 := by
      gcongr
      · exact Finset.abs_sum_le_sum_abs _ _
      · exact le_of_eq (abs_quantumIsingBond _ _)
    _ = (k + 1 : Real) := by
      simp



theorem quantumIsingBlockInteraction_sub_le
    (k L : Nat) (sigma : QuantumIsingBlockConfig (k + 1) (L + 1)) :
    |quantumIsingBlockLongInteraction k L sigma -
      quantumIsingBlockPeriodicInteraction k L sigma| ≤
        2 * (k + 1 : Real) := by
  rw [quantumIsingBlockLongInteraction_eq_open_add,
    quantumIsingBlockPeriodicInteraction_eq_open_add]
  have hlong := abs_blockLongSeam_le k L sigma
  have hperiodic := abs_blockPeriodicSeam_le k L sigma
  calc
    |quantumIsingBlockOpenInteraction k L sigma +
          quantumIsingBlockLongSeamInteraction k L sigma -
        (quantumIsingBlockOpenInteraction k L sigma +
          ∑ b : Fin (k + 1),
            quantumIsingSpinSign (sigma b (Fin.last L)) *
              quantumIsingSpinSign (sigma b 0))| =
      |quantumIsingBlockLongSeamInteraction k L sigma -
        ∑ b : Fin (k + 1),
          quantumIsingSpinSign (sigma b (Fin.last L)) *
            quantumIsingSpinSign (sigma b 0)| := by ring_nf
    _ ≤ |quantumIsingBlockLongSeamInteraction k L sigma| +
        |∑ b : Fin (k + 1),
          quantumIsingSpinSign (sigma b (Fin.last L)) *
            quantumIsingSpinSign (sigma b 0)| := abs_sub _ _
    _ ≤ (k + 1 : Real) + (k + 1 : Real) := add_le_add hlong hperiodic
    _ = 2 * (k + 1 : Real) := by ring

abbrev QuantumIsingSpaceTimeBlockConfig (n k L : Nat) :=
  Fin n -> QuantumIsingBlockConfig k L

noncomputable def quantumIsingBlockVerticalLayerWeight
    (beta h : Real) (n k L : Nat)
    (omega : QuantumIsingSpaceTimeBlockConfig n k L) (t : Fin n) : Real :=
  ∏ b : Fin k, ∏ i : Fin L,
    quantumIsingVerticalBondWeight beta h n
      (omega t b i) (omega (quantumIsingCyclicSucc t) b i)

noncomputable def quantumIsingBlockLongCylinderWeight
    (beta h : Real) (n k L : Nat)
    (omega : QuantumIsingSpaceTimeBlockConfig n (k + 1) (L + 1)) : Real :=
  ∏ t : Fin n,
    Real.exp (beta / (4 * n) *
      quantumIsingBlockLongInteraction k L (omega t)) *
      quantumIsingBlockVerticalLayerWeight beta h n (k + 1) (L + 1) omega t

noncomputable def quantumIsingBlockPeriodicCylinderWeight
    (beta h : Real) (n k L : Nat)
    (omega : QuantumIsingSpaceTimeBlockConfig n (k + 1) (L + 1)) : Real :=
  ∏ t : Fin n,
    Real.exp (beta / (4 * n) *
      quantumIsingBlockPeriodicInteraction k L (omega t)) *
      quantumIsingBlockVerticalLayerWeight beta h n (k + 1) (L + 1) omega t

private theorem quantumIsingBlockLongLayer_le
    (beta h : Real) (n k L : Nat) (hbeta : 0 ≤ beta)
    (omega : QuantumIsingSpaceTimeBlockConfig (n + 1) (k + 1) (L + 1))
    (t : Fin (n + 1)) :
    Real.exp (beta / (4 * (n + 1)) *
        quantumIsingBlockLongInteraction k L (omega t)) *
        quantumIsingBlockVerticalLayerWeight beta h (n + 1) (k + 1) (L + 1) omega t ≤
      Real.exp (beta * (k + 1) / (2 * (n + 1))) *
        (Real.exp (beta / (4 * (n + 1)) *
          quantumIsingBlockPeriodicInteraction k L (omega t)) *
          quantumIsingBlockVerticalLayerWeight beta h (n + 1) (k + 1) (L + 1) omega t) := by
  have hdiff := quantumIsingBlockInteraction_sub_le k L (omega t)
  have hinter : quantumIsingBlockLongInteraction k L (omega t) ≤
      quantumIsingBlockPeriodicInteraction k L (omega t) +
        2 * (k + 1 : Real) := by
    rw [abs_le] at hdiff
    linarith
  have hcoeff : 0 ≤ beta / (4 * (n + 1 : Real)) := by positivity
  have hexp : Real.exp (beta / (4 * (n + 1)) *
        quantumIsingBlockLongInteraction k L (omega t)) ≤
      Real.exp (beta * (k + 1) / (2 * (n + 1))) *
        Real.exp (beta / (4 * (n + 1)) *
          quantumIsingBlockPeriodicInteraction k L (omega t)) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    calc
      beta / (4 * (n + 1 : Real)) *
          quantumIsingBlockLongInteraction k L (omega t) ≤
        beta / (4 * (n + 1 : Real)) *
          (quantumIsingBlockPeriodicInteraction k L (omega t) +
            2 * (k + 1 : Real)) :=
        mul_le_mul_of_nonneg_left hinter hcoeff
      _ = beta * (k + 1) / (2 * (n + 1 : Real)) +
          beta / (4 * (n + 1 : Real)) *
            quantumIsingBlockPeriodicInteraction k L (omega t) := by
        field_simp
        ring
  have hvertical : 0 ≤ quantumIsingBlockVerticalLayerWeight beta h
      (n + 1) (k + 1) (L + 1) omega t := by
    unfold quantumIsingBlockVerticalLayerWeight quantumIsingVerticalBondWeight
    positivity
  calc
    _ ≤ (Real.exp (beta * (k + 1) / (2 * (n + 1))) *
        Real.exp (beta / (4 * (n + 1)) *
          quantumIsingBlockPeriodicInteraction k L (omega t))) *
        quantumIsingBlockVerticalLayerWeight beta h (n + 1) (k + 1) (L + 1) omega t :=
      mul_le_mul_of_nonneg_right hexp hvertical
    _ = _ := by ring

private theorem quantumIsingBlockPeriodicLayer_le
    (beta h : Real) (n k L : Nat) (hbeta : 0 ≤ beta)
    (omega : QuantumIsingSpaceTimeBlockConfig (n + 1) (k + 1) (L + 1))
    (t : Fin (n + 1)) :
    Real.exp (beta / (4 * (n + 1)) *
        quantumIsingBlockPeriodicInteraction k L (omega t)) *
        quantumIsingBlockVerticalLayerWeight beta h (n + 1) (k + 1) (L + 1) omega t ≤
      Real.exp (beta * (k + 1) / (2 * (n + 1))) *
        (Real.exp (beta / (4 * (n + 1)) *
          quantumIsingBlockLongInteraction k L (omega t)) *
          quantumIsingBlockVerticalLayerWeight beta h (n + 1) (k + 1) (L + 1) omega t) := by
  have hdiff := quantumIsingBlockInteraction_sub_le k L (omega t)
  have hinter : quantumIsingBlockPeriodicInteraction k L (omega t) ≤
      quantumIsingBlockLongInteraction k L (omega t) +
        2 * (k + 1 : Real) := by
    rw [abs_le] at hdiff
    linarith
  have hcoeff : 0 ≤ beta / (4 * (n + 1 : Real)) := by positivity
  have hexp : Real.exp (beta / (4 * (n + 1)) *
        quantumIsingBlockPeriodicInteraction k L (omega t)) ≤
      Real.exp (beta * (k + 1) / (2 * (n + 1))) *
        Real.exp (beta / (4 * (n + 1)) *
          quantumIsingBlockLongInteraction k L (omega t)) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    calc
      beta / (4 * (n + 1 : Real)) *
          quantumIsingBlockPeriodicInteraction k L (omega t) ≤
        beta / (4 * (n + 1 : Real)) *
          (quantumIsingBlockLongInteraction k L (omega t) +
            2 * (k + 1 : Real)) :=
        mul_le_mul_of_nonneg_left hinter hcoeff
      _ = beta * (k + 1) / (2 * (n + 1 : Real)) +
          beta / (4 * (n + 1 : Real)) *
            quantumIsingBlockLongInteraction k L (omega t) := by
        field_simp
        ring
  have hvertical : 0 ≤ quantumIsingBlockVerticalLayerWeight beta h
      (n + 1) (k + 1) (L + 1) omega t := by
    unfold quantumIsingBlockVerticalLayerWeight quantumIsingVerticalBondWeight
    positivity
  calc
    _ ≤ (Real.exp (beta * (k + 1) / (2 * (n + 1))) *
        Real.exp (beta / (4 * (n + 1)) *
          quantumIsingBlockLongInteraction k L (omega t))) *
        quantumIsingBlockVerticalLayerWeight beta h (n + 1) (k + 1) (L + 1) omega t :=
      mul_le_mul_of_nonneg_right hexp hvertical
    _ = _ := by ring



theorem quantumIsingBlockLongCylinderWeight_le
    (beta h : Real) (n k L : Nat) (hbeta : 0 ≤ beta)
    (omega : QuantumIsingSpaceTimeBlockConfig (n + 1) (k + 1) (L + 1)) :
    quantumIsingBlockLongCylinderWeight beta h (n + 1) k L omega ≤
      Real.exp (beta * (k + 1) / 2) *
        quantumIsingBlockPeriodicCylinderWeight beta h (n + 1) k L omega := by
  unfold quantumIsingBlockLongCylinderWeight quantumIsingBlockPeriodicCylinderWeight
  norm_num only [Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ ∏ t : Fin (n + 1),
        Real.exp (beta * (k + 1) / (2 * (n + 1))) *
          (Real.exp (beta / (4 * (n + 1)) *
            quantumIsingBlockPeriodicInteraction k L (omega t)) *
            quantumIsingBlockVerticalLayerWeight beta h (n + 1) (k + 1) (L + 1) omega t) := by
      apply Finset.prod_le_prod
      · intro t _
        unfold quantumIsingBlockVerticalLayerWeight quantumIsingVerticalBondWeight
        positivity
      · intro t _
        exact quantumIsingBlockLongLayer_le beta h n k L hbeta omega t
    _ = Real.exp (beta * (k + 1) / 2) *
        ∏ t : Fin (n + 1),
          Real.exp (beta / (4 * (n + 1)) *
            quantumIsingBlockPeriodicInteraction k L (omega t)) *
            quantumIsingBlockVerticalLayerWeight beta h (n + 1) (k + 1) (L + 1) omega t := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← Real.exp_nat_mul]
      congr 2
      push_cast
      field_simp


theorem quantumIsingBlockPeriodicCylinderWeight_le
    (beta h : Real) (n k L : Nat) (hbeta : 0 ≤ beta)
    (omega : QuantumIsingSpaceTimeBlockConfig (n + 1) (k + 1) (L + 1)) :
    quantumIsingBlockPeriodicCylinderWeight beta h (n + 1) k L omega ≤
      Real.exp (beta * (k + 1) / 2) *
        quantumIsingBlockLongCylinderWeight beta h (n + 1) k L omega := by
  unfold quantumIsingBlockLongCylinderWeight quantumIsingBlockPeriodicCylinderWeight
  norm_num only [Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ ∏ t : Fin (n + 1),
        Real.exp (beta * (k + 1) / (2 * (n + 1))) *
          (Real.exp (beta / (4 * (n + 1)) *
            quantumIsingBlockLongInteraction k L (omega t)) *
            quantumIsingBlockVerticalLayerWeight beta h (n + 1) (k + 1) (L + 1) omega t) := by
      apply Finset.prod_le_prod
      · intro t _
        unfold quantumIsingBlockVerticalLayerWeight quantumIsingVerticalBondWeight
        positivity
      · intro t _
        exact quantumIsingBlockPeriodicLayer_le beta h n k L hbeta omega t
    _ = Real.exp (beta * (k + 1) / 2) *
        ∏ t : Fin (n + 1),
          Real.exp (beta / (4 * (n + 1)) *
            quantumIsingBlockLongInteraction k L (omega t)) *
            quantumIsingBlockVerticalLayerWeight beta h (n + 1) (k + 1) (L + 1) omega t := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← Real.exp_nat_mul]
      congr 2
      push_cast
      field_simp

def quantumIsingSpaceTimeBlockEquiv (n k L : Nat) :
    (Fin n -> QuantumIsingChainConfig (k * L)) ≃
      QuantumIsingSpaceTimeBlockConfig n k L :=
  Equiv.piCongrRight (fun _ : Fin n => quantumIsingBlockEquiv k L)

@[simp] theorem quantumIsingSpaceTimeBlockEquiv_apply
    (n k L : Nat) (omega : Fin n -> QuantumIsingChainConfig (k * L))
    (t : Fin n) (b : Fin k) (i : Fin L) :
    quantumIsingSpaceTimeBlockEquiv n k L omega t b i =
      omega t (finProdFinEquiv (b, i)) := by
  rfl

@[simp] theorem quantumIsingSpaceTimeBlockEquiv_symm_apply
    (n k L : Nat) (omega : QuantumIsingSpaceTimeBlockConfig n k L)
    (t : Fin n) (b : Fin k) (i : Fin L) :
    (quantumIsingSpaceTimeBlockEquiv n k L).symm omega t
        (finProdFinEquiv (b, i)) = omega t b i := by
  simp [quantumIsingSpaceTimeBlockEquiv]



theorem quantumIsingClassicalCylinderWeight_blockEquiv
    (beta h : Real) (n k L : Nat)
    (omega : QuantumIsingSpaceTimeBlockConfig n (k + 1) (L + 1)) :
    quantumIsingClassicalCylinderWeight beta h n
        ((k + 1) * (L + 1))
        ((quantumIsingSpaceTimeBlockEquiv n (k + 1) (L + 1)).symm omega) =
      quantumIsingBlockLongCylinderWeight beta h n k L omega := by
  unfold quantumIsingClassicalCylinderWeight
  unfold quantumIsingBlockLongCylinderWeight
  apply Finset.prod_congr rfl
  intro t _
  unfold quantumIsingSpatialTrotterWeight
  rw [show quantumIsingChainInteraction ((k + 1) * (L + 1))
      ((quantumIsingSpaceTimeBlockEquiv n (k + 1) (L + 1)).symm omega t) =
        quantumIsingBlockLongInteraction k L (omega t) by rfl]
  congr 1
  unfold quantumIsingBlockVerticalLayerWeight
  calc
      (∏ i : Fin ((k + 1) * (L + 1)),
        quantumIsingVerticalBondWeight beta h n
          ((quantumIsingSpaceTimeBlockEquiv n (k + 1) (L + 1)).symm omega t i)
          ((quantumIsingSpaceTimeBlockEquiv n (k + 1) (L + 1)).symm omega
            (quantumIsingCyclicSucc t) i)) =
        ∏ p : Fin (k + 1) × Fin (L + 1),
          quantumIsingVerticalBondWeight beta h n
            ((quantumIsingSpaceTimeBlockEquiv n (k + 1) (L + 1)).symm omega t
              (finProdFinEquiv p))
            ((quantumIsingSpaceTimeBlockEquiv n (k + 1) (L + 1)).symm omega
              (quantumIsingCyclicSucc t) (finProdFinEquiv p)) := by
        exact (Equiv.prod_comp finProdFinEquiv _).symm
      _ = ∏ b : Fin (k + 1), ∏ i : Fin (L + 1),
          quantumIsingVerticalBondWeight beta h n
            (omega t b i) (omega (quantumIsingCyclicSucc t) b i) := by
        rw [Fintype.prod_prod_type]
        simp



theorem quantumIsingBlockPeriodicCylinderWeight_eq_prod
    (beta h : Real) (n k L : Nat)
    (omega : QuantumIsingSpaceTimeBlockConfig n (k + 1) (L + 1)) :
    quantumIsingBlockPeriodicCylinderWeight beta h n k L omega =
      ∏ b : Fin (k + 1),
        quantumIsingClassicalCylinderWeight beta h n (L + 1)
          (fun t => omega t b) := by
  unfold quantumIsingBlockPeriodicCylinderWeight
  calc
    (∏ t : Fin n,
      Real.exp (beta / (4 * n) *
        quantumIsingBlockPeriodicInteraction k L (omega t)) *
        quantumIsingBlockVerticalLayerWeight beta h n (k + 1) (L + 1) omega t) =
      ∏ t : Fin n, ∏ b : Fin (k + 1),
        quantumIsingSpatialTrotterWeight beta n (L + 1) (omega t b) *
          (∏ i : Fin (L + 1),
            quantumIsingVerticalBondWeight beta h n
              (omega t b i) (omega (quantumIsingCyclicSucc t) b i)) := by
      apply Finset.prod_congr rfl
      intro t _
      unfold quantumIsingBlockPeriodicInteraction
      unfold quantumIsingBlockVerticalLayerWeight
      have hexp : Real.exp (beta / (4 * (n : Real)) *
            ∑ b : Fin (k + 1), quantumIsingChainInteraction (L + 1) (omega t b)) =
          ∏ b : Fin (k + 1),
            Real.exp (beta / (4 * (n : Real)) *
              quantumIsingChainInteraction (L + 1) (omega t b)) := by
        rw [Finset.mul_sum]
        exact Real.exp_sum Finset.univ _
      rw [hexp, Finset.prod_mul_distrib]
      rfl
    _ = ∏ b : Fin (k + 1), ∏ t : Fin n,
        quantumIsingSpatialTrotterWeight beta n (L + 1) (omega t b) *
          (∏ i : Fin (L + 1),
            quantumIsingVerticalBondWeight beta h n
              (omega t b i) (omega (quantumIsingCyclicSucc t) b i)) := by
      rw [← Fintype.prod_prod_type']
      exact Fintype.prod_prod_type_right'
        (γ := Real) (α₁ := Fin n) (α₂ := Fin (k + 1))
        (fun t b =>
          quantumIsingSpatialTrotterWeight beta n (L + 1) (omega t b) *
            ∏ i : Fin (L + 1),
              quantumIsingVerticalBondWeight beta h n
                (omega t b i) (omega (quantumIsingCyclicSucc t) b i))
    _ = ∏ b : Fin (k + 1),
        quantumIsingClassicalCylinderWeight beta h n (L + 1)
          (fun t => omega t b) := by
      rfl

def quantumIsingSpaceTimeBlockSwapEquiv (n k L : Nat) :
    QuantumIsingSpaceTimeBlockConfig n k L ≃
      (Fin k -> Fin n -> QuantumIsingChainConfig L) where
  toFun omega b t := omega t b
  invFun omega t b := omega b t
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem quantumIsingSpaceTimeBlockSwapEquiv_apply
    (n k L : Nat) (omega : QuantumIsingSpaceTimeBlockConfig n k L)
    (b : Fin k) (t : Fin n) :
    quantumIsingSpaceTimeBlockSwapEquiv n k L omega b t = omega t b := rfl

@[simp] theorem quantumIsingSpaceTimeBlockSwapEquiv_symm_apply
    (n k L : Nat) (omega : Fin k -> Fin n -> QuantumIsingChainConfig L)
    (t : Fin n) (b : Fin k) :
    (quantumIsingSpaceTimeBlockSwapEquiv n k L).symm omega t b = omega b t := rfl



theorem quantumIsingBlockPeriodicCylinderWeight_sum
    (beta h : Real) (n k L : Nat) :
    (∑ omega : QuantumIsingSpaceTimeBlockConfig n (k + 1) (L + 1),
      quantumIsingBlockPeriodicCylinderWeight beta h n k L omega) =
      quantumIsingClassicalCylinderPartition beta h n (L + 1) ^ (k + 1) := by
  let e := quantumIsingSpaceTimeBlockSwapEquiv n (k + 1) (L + 1)
  calc
    (∑ omega : QuantumIsingSpaceTimeBlockConfig n (k + 1) (L + 1),
      quantumIsingBlockPeriodicCylinderWeight beta h n k L omega) =
      ∑ blocks : Fin (k + 1) -> Fin n -> QuantumIsingChainConfig (L + 1),
        quantumIsingBlockPeriodicCylinderWeight beta h n k L (e.symm blocks) := by
      simpa using (Equiv.sum_comp e
        (fun blocks : Fin (k + 1) -> Fin n -> QuantumIsingChainConfig (L + 1) =>
          quantumIsingBlockPeriodicCylinderWeight beta h n k L (e.symm blocks)))
    _ = ∑ blocks : Fin (k + 1) -> Fin n -> QuantumIsingChainConfig (L + 1),
        ∏ b : Fin (k + 1),
          quantumIsingClassicalCylinderWeight beta h n (L + 1) (blocks b) := by
      apply Finset.sum_congr rfl
      intro blocks _
      rw [quantumIsingBlockPeriodicCylinderWeight_eq_prod]
      rfl
    _ = (∑ cylinder : Fin n -> QuantumIsingChainConfig (L + 1),
        quantumIsingClassicalCylinderWeight beta h n (L + 1) cylinder) ^
          (k + 1) := by
      rw [Finset.sum_pow'
        (Finset.univ : Finset (Fin n -> QuantumIsingChainConfig (L + 1)))
        (quantumIsingClassicalCylinderWeight beta h n (L + 1)) (k + 1)]
      simp
    _ = quantumIsingClassicalCylinderPartition beta h n (L + 1) ^ (k + 1) := by
      rfl

private theorem quantumIsingClassicalCylinderPartition_block_sum
    (beta h : Real) (n k L : Nat) :
    quantumIsingClassicalCylinderPartition beta h n ((k + 1) * (L + 1)) =
      ∑ omega : QuantumIsingSpaceTimeBlockConfig n (k + 1) (L + 1),
        quantumIsingBlockLongCylinderWeight beta h n k L omega := by
  unfold quantumIsingClassicalCylinderPartition
  let e := quantumIsingSpaceTimeBlockEquiv n (k + 1) (L + 1)
  calc
    (∑ omega : Fin n -> QuantumIsingChainConfig ((k + 1) * (L + 1)),
      quantumIsingClassicalCylinderWeight beta h n ((k + 1) * (L + 1)) omega) =
      ∑ blocks : QuantumIsingSpaceTimeBlockConfig n (k + 1) (L + 1),
        quantumIsingClassicalCylinderWeight beta h n ((k + 1) * (L + 1))
          (e.symm blocks) := by
      simpa using (Equiv.sum_comp e
        (fun blocks : QuantumIsingSpaceTimeBlockConfig n (k + 1) (L + 1) =>
          quantumIsingClassicalCylinderWeight beta h n ((k + 1) * (L + 1))
            (e.symm blocks)))
    _ = ∑ blocks : QuantumIsingSpaceTimeBlockConfig n (k + 1) (L + 1),
        quantumIsingBlockLongCylinderWeight beta h n k L blocks := by
      apply Finset.sum_congr rfl
      intro blocks _
      exact quantumIsingClassicalCylinderWeight_blockEquiv beta h n k L blocks




theorem quantumIsingClassicalCylinderPartition_block_upper
    (beta h : Real) (n k L : Nat) (hbeta : 0 ≤ beta) :
    quantumIsingClassicalCylinderPartition beta h (n + 1)
        ((k + 1) * (L + 1)) ≤
      quantumIsingClassicalCylinderPartition beta h (n + 1) (L + 1) ^
          (k + 1) *
        Real.exp (beta * (k + 1) / 2) := by
  rw [quantumIsingClassicalCylinderPartition_block_sum]
  calc
    (∑ omega : QuantumIsingSpaceTimeBlockConfig (n + 1) (k + 1) (L + 1),
      quantumIsingBlockLongCylinderWeight beta h (n + 1) k L omega) ≤
      ∑ omega : QuantumIsingSpaceTimeBlockConfig (n + 1) (k + 1) (L + 1),
        Real.exp (beta * (k + 1) / 2) *
          quantumIsingBlockPeriodicCylinderWeight beta h (n + 1) k L omega := by
      apply Finset.sum_le_sum
      intro omega _
      exact quantumIsingBlockLongCylinderWeight_le beta h n k L hbeta omega
    _ = Real.exp (beta * (k + 1) / 2) *
        (∑ omega : QuantumIsingSpaceTimeBlockConfig (n + 1) (k + 1) (L + 1),
          quantumIsingBlockPeriodicCylinderWeight beta h (n + 1) k L omega) := by
      rw [Finset.mul_sum]
    _ = Real.exp (beta * (k + 1) / 2) *
        quantumIsingClassicalCylinderPartition beta h (n + 1) (L + 1) ^
          (k + 1) := by
      rw [quantumIsingBlockPeriodicCylinderWeight_sum]
    _ = _ := by ring



theorem quantumIsingClassicalCylinderPartition_block_lower
    (beta h : Real) (n k L : Nat) (hbeta : 0 ≤ beta) :
    quantumIsingClassicalCylinderPartition beta h (n + 1) (L + 1) ^
          (k + 1) *
        Real.exp (-beta * (k + 1) / 2) ≤
      quantumIsingClassicalCylinderPartition beta h (n + 1)
        ((k + 1) * (L + 1)) := by
  have hsum :
      quantumIsingClassicalCylinderPartition beta h (n + 1) (L + 1) ^
          (k + 1) ≤
        Real.exp (beta * (k + 1) / 2) *
          quantumIsingClassicalCylinderPartition beta h (n + 1)
            ((k + 1) * (L + 1)) := by
    rw [quantumIsingClassicalCylinderPartition_block_sum,
      ← quantumIsingBlockPeriodicCylinderWeight_sum]
    calc
      (∑ omega : QuantumIsingSpaceTimeBlockConfig (n + 1) (k + 1) (L + 1),
        quantumIsingBlockPeriodicCylinderWeight beta h (n + 1) k L omega) ≤
        ∑ omega : QuantumIsingSpaceTimeBlockConfig (n + 1) (k + 1) (L + 1),
          Real.exp (beta * (k + 1) / 2) *
            quantumIsingBlockLongCylinderWeight beta h (n + 1) k L omega := by
        apply Finset.sum_le_sum
        intro omega _
        exact quantumIsingBlockPeriodicCylinderWeight_le beta h n k L hbeta omega
      _ = Real.exp (beta * (k + 1) / 2) *
          ∑ omega : QuantumIsingSpaceTimeBlockConfig (n + 1) (k + 1) (L + 1),
            quantumIsingBlockLongCylinderWeight beta h (n + 1) k L omega := by
        rw [Finset.mul_sum]
  calc
    quantumIsingClassicalCylinderPartition beta h (n + 1) (L + 1) ^
          (k + 1) * Real.exp (-beta * (k + 1) / 2) =
      Real.exp (-beta * (k + 1) / 2) *
        quantumIsingClassicalCylinderPartition beta h (n + 1) (L + 1) ^
          (k + 1) := by ring
    _ ≤ Real.exp (-beta * (k + 1) / 2) *
        (Real.exp (beta * (k + 1) / 2) *
          quantumIsingClassicalCylinderPartition beta h (n + 1)
            ((k + 1) * (L + 1))) :=
      mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
    _ = quantumIsingClassicalCylinderPartition beta h (n + 1)
        ((k + 1) * (L + 1)) := by
      rw [← mul_assoc, ← Real.exp_add,
        show -beta * (k + 1 : Real) / 2 + beta * (k + 1 : Real) / 2 = 0 by ring,
        Real.exp_zero, one_mul]

end StatMech.FrontierA
