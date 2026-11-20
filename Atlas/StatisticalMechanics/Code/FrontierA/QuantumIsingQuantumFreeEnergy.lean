/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.QuantumIsingNormalizedPartitionLimit
import Code.FrontierA.QuantumIsingLieTrotter
import Code.FrontierA.QuantumIsingLimitInterchange





open Filter
open scoped Topology BigOperators

namespace StatMech.FrontierA

theorem quantumIsingBoltzmannGenerator_isHermitian
    (beta h : Real) (L : Nat) :
    (quantumIsingBoltzmannGenerator beta h L).IsHermitian := by
  unfold quantumIsingBoltzmannGenerator
  apply (quantumIsingHamiltonian_isHermitian h L).smul
  change star (-(beta : Complex)) = -(beta : Complex)
  simp

theorem quantumIsingChainInteraction_const_false (L : Nat) :
    quantumIsingChainInteraction L (fun _ ↦ false) = L := by
  unfold quantumIsingChainInteraction
  simp only [quantumIsingSpinSign_false, neg_mul_neg, one_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_id]
  ring

theorem quantumIsingTrotterTransferKernel_const_false
    (beta h : Real) (n L : Nat) :
    quantumIsingTrotterTransferKernel beta h n L
        (fun _ ↦ false) (fun _ ↦ false) =
      Real.exp (beta / (4 * n) * L) := by
  unfold quantumIsingTrotterTransferKernel quantumIsingSpatialTrotterWeight
  rw [quantumIsingChainInteraction_const_false]
  simp [quantumIsingTrotterKernel]

theorem quantumIsingTrotterPathPartition_lower
    (beta h : Real) (n L : Nat) (hn : n ≠ 0)
    (hbeta : 0 ≤ beta) (hbh : 0 ≤ beta * h) :
    Real.exp (beta * L / 4) ≤
      quantumIsingTrotterPathPartition beta h n L := by
  classical
  let sigma : QuantumIsingChainConfig L := fun _ ↦ false
  let omega : Fin n → QuantumIsingChainConfig L := fun _ ↦ sigma
  let W : (Fin n → QuantumIsingChainConfig L) → Real := fun eta ↦
    ∏ k : Fin n, quantumIsingTrotterTransferKernel beta h n L
      (eta k) (eta (quantumIsingCyclicSucc k))
  have hkernel (k : Fin n) :
      quantumIsingTrotterTransferKernel beta h n L
        (omega k) (omega (quantumIsingCyclicSucc k)) =
          Real.exp (beta / (4 * n) * L) := by
    exact quantumIsingTrotterTransferKernel_const_false beta h n L
  have hterm : W omega = Real.exp (beta * L / 4) := by
    dsimp only [W]
    simp_rw [hkernel]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.exp_nat_mul]
    congr 1
    have hnR : (n : Real) ≠ 0 := by exact_mod_cast hn
    field_simp [hnR]
  have hWnonneg (eta : Fin n → QuantumIsingChainConfig L) : 0 ≤ W eta := by
    dsimp only [W]
    apply Finset.prod_nonneg
    intro k hk
    unfold quantumIsingTrotterTransferKernel
    exact mul_nonneg (Real.exp_nonneg _) <|
      Finset.prod_nonneg fun i hi ↦
        quantumIsingTrotterKernel_nonneg beta h n hbh _ _
  calc
    Real.exp (beta * L / 4) = W omega := hterm.symm
    _ ≤ ∑ eta, W eta := Finset.single_le_sum
      (fun eta _ ↦ hWnonneg eta) (Finset.mem_univ omega)
    _ = quantumIsingTrotterPathPartition beta h n L := rfl

theorem quantumIsingQuantumPartition_re_pos
    (beta h : Real) (L : Nat) (hbeta : 0 < beta) (hh : 0 < h) :
    0 < (quantumIsingQuantumPartition beta h L).re := by
  have htrace := quantumIsingTrotterTrace_tendsto_quantumPartition beta h L
  have hpath : Tendsto (fun n : Nat ↦
      (quantumIsingTrotterPathPartition beta h (n + 1) L : Complex))
      atTop (nhds (quantumIsingQuantumPartition beta h L)) := by
    apply htrace.congr'
    filter_upwards with n
    rw [quantumIsingTrotterTrace_eq_pathPartition beta h (n + 1) L
      (by omega)]
  have hre := (Complex.continuous_re.tendsto
    (quantumIsingQuantumPartition beta h L)).comp hpath
  have hlower : Real.exp (beta * L / 4) ≤
      (quantumIsingQuantumPartition beta h L).re := by
    apply ge_of_tendsto hre
    filter_upwards with n
    simpa using quantumIsingTrotterPathPartition_lower beta h (n + 1) L
      (by omega) hbeta.le (mul_pos hbeta hh).le
  exact (Real.exp_pos _).trans_le hlower

theorem quantumIsingQuantumPartition_norm_pos
    (beta h : Real) (L : Nat) (hbeta : 0 < beta) (hh : 0 < h) :
    0 < ‖quantumIsingQuantumPartition beta h L‖ := by
  rw [norm_pos_iff]
  intro hzero
  have hre := congrArg Complex.re hzero
  simp only [Complex.zero_re] at hre
  linarith [quantumIsingQuantumPartition_re_pos beta h L hbeta hh]

end StatMech.FrontierA
