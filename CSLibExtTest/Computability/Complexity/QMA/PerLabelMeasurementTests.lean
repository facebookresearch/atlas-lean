/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QMA.PerLabelMeasurement
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Group.Semigroup

/-!
# Tests: per-label measurement circuits
-/

@[expose] public section

namespace Cslib.Complexity.Classes.Tests

set_option autoImplicit false

open Cslib.Complexity.Classes Cslib.Complexity.Classes.QuantumGates
open Cslib.Complexity.Classes.QMA

#print axioms embedLocal_add
#print axioms embedLocal_smul
#print axioms pauliEmb_isHermitian
#print axioms pauliEmb_zero_zero
#print axioms abs_pauliExpect_le
#print axioms perLabelCircuit_wellFormed
#print axioms perLabelCircuit_length_le
#print axioms acceptProb_outputSwap
#print axioms ancProb_perLabelCore
#print axioms acceptProb_perLabelCircuit
#print axioms acceptProb_perLabelCircuit_signOne
#print axioms acceptProb_perLabelCircuit_single_zString
#print axioms perLabelCore_preserves_qBit

private theorem sqNorm_piSingle_one {m : ℕ} (s₀ : Fin (2 ^ m)) :
    sqNorm (Pi.single s₀ 1) = 1 := by
  unfold sqNorm
  rw [Finset.sum_eq_single_of_mem s₀ (Finset.mem_univ s₀) (fun s _ hs => by
    simp only [Pi.single_eq_of_ne hs, map_zero, zero_mul, Complex.zero_re])]
  rw [Pi.single_eq_same]
  norm_num

private theorem acceptProb_piSingle_one {N : ℕ} (s₀ : Fin (2 ^ N))
    (h : qBit 0 s₀.val = 1) : acceptProb (Pi.single s₀ 1) = 1 := by
  unfold acceptProb
  rw [Finset.sum_eq_single_of_mem s₀ (Finset.mem_univ s₀) (fun s _ hs => by
    simp only [Pi.single_eq_of_ne hs, map_zero, zero_mul, Complex.zero_re]
    split <;> rfl)]
  rw [ite_eq_left h, Pi.single_eq_same]
  norm_num

private theorem acceptProb_piSingle_zero {N : ℕ} (s₀ : Fin (2 ^ N))
    (h : qBit 0 s₀.val ≠ 1) : acceptProb (Pi.single s₀ 1) = 0 := by
  unfold acceptProb
  rw [Finset.sum_eq_single_of_mem s₀ (Finset.mem_univ s₀) (fun s _ hs => by
    simp only [Pi.single_eq_of_ne hs, map_zero, zero_mul, Complex.zero_re]
    split <;> rfl)]
  rw [ite_eq_right h]

private theorem pauliExpect_zero_label {N : ℕ} (ψ : Fin (2 ^ N) → ℂ) :
    pauliExpect (fun i : Fin 0 => i.elim0) 0 0 ψ = sqNorm ψ := by
  unfold pauliExpect
  rw [pauliEmb_zero_zero, Matrix.one_mulVec]
  unfold sqNorm dotProduct
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Pi.star_apply, starRingEnd_apply]

private theorem pauliExpect_piSingle_of_a_ne {N k : ℕ} (addr : Fin k → ℕ)
    (a b : Fin k → ZMod 2) (s₀ : Fin (2 ^ N)) (j : Fin k) (hj : a j ≠ 0) :
    pauliExpect addr a b (Pi.single s₀ 1) = 0 := by
  unfold pauliExpect dotProduct
  rw [Finset.sum_eq_single_of_mem s₀ (Finset.mem_univ s₀) (fun s _ hs => by
    simp only [Pi.star_apply, Pi.single_eq_of_ne hs, star_zero, zero_mul])]
  simp only [Pi.star_apply, Pi.single_eq_same, star_one, one_mul]
  unfold Matrix.mulVec dotProduct
  rw [Finset.sum_eq_single_of_mem s₀ (Finset.mem_univ s₀) (fun t _ ht => by
    simp only [Pi.single_eq_of_ne ht, mul_zero])]
  rw [Pi.single_eq_same, mul_one]
  simp only [pauliEmb, embedLocal]
  rw [ite_eq_left (fun _ _ => rfl)]
  simp only [MathlibExt.Quantum.PauliExpansion.hermPauli]
  rw [Matrix.smul_apply, smul_eq_mul, MathlibExt.Quantum.PauliXZ.pauliXZ_apply]
  have hne : localBits addr s₀.val ≠ localBits addr s₀.val + a := by
    intro hcon
    have h0 := congrFun hcon j
    simp only [Pi.add_apply] at h0
    have h3 : localBits addr s₀.val j + a j = localBits addr s₀.val j + 0 := by
      rw [add_zero]
      exact h0.symm
    exact hj (add_left_cancel_iff.mp h3)
  rw [ite_eq_right hne, mul_zero]
  exact Complex.zero_re

private def swapIdx (N i j : ℕ) (s : Fin (2 ^ N)) : Fin (2 ^ N) :=
  setQBit N i (qBit j s.val) (setQBit N j (qBit i s.val) s)

private theorem swapIdx_swapIdx {N i j : ℕ} (hiN : i < N) (hjN : j < N)
    (hij : i ≠ j) (s : Fin (2 ^ N)) : swapIdx N i j (swapIdx N i j s) = s := by
  have hswap_i : ∀ t : Fin (2 ^ N), qBit i (swapIdx N i j t).val = qBit j t.val := by
    intro t
    unfold swapIdx
    rw [qBit_setQBit_self hiN]
  have hswap_j : ∀ t : Fin (2 ^ N), qBit j (swapIdx N i j t).val = qBit i t.val := by
    intro t
    unfold swapIdx
    rw [qBit_setQBit_of_ne (Ne.symm hij), qBit_setQBit_self hjN]
  have hswap_k : ∀ (t : Fin (2 ^ N)) (k : ℕ), k ≠ i → k ≠ j →
      qBit k (swapIdx N i j t).val = qBit k t.val := by
    intro t k hki hkj
    unfold swapIdx
    rw [qBit_setQBit_of_ne hki, qBit_setQBit_of_ne hkj]
  apply fin_eq_of_qBit_eq
  intro k hkN
  by_cases hki : k = i
  · subst hki
    exact (hswap_i _).trans (hswap_j _)
  · by_cases hkj : k = j
    · subst hkj
      exact (hswap_j _).trans (hswap_i _)
    · exact (hswap_k _ _ hki hkj).trans (hswap_k _ _ hki hkj)

private theorem applyCircuit_outputSwap_single {N : ℕ} (anc : ℕ)
    (hanc0 : 0 < anc) (hanc : anc < N)
    (t s : Fin (2 ^ N)) (h : swapIdx N 0 anc t = s) :
    applyCircuit N [outputSwap anc] (Pi.single t 1) = Pi.single s 1 := by
  have h0N : 0 < N := hanc0.trans_le hanc.le
  have h01 : (0 : ℕ) ≠ anc := ne_of_lt hanc0
  have hinv : ∀ u : Fin (2 ^ N), swapIdx N 0 anc (swapIdx N 0 anc u) = u :=
    fun u => swapIdx_swapIdx h0N hanc h01 u
  simp only [applyCircuit, List.foldl_cons, List.foldl_nil]
  show applyGate N (0, anc, swapEntries) (Pi.single t 1) = Pi.single s 1
  funext s'
  rw [applyGate_swap hanc0 hanc]
  have hfold : setQBit N 0 (qBit anc s'.val) (setQBit N anc (qBit 0 s'.val) s') =
      swapIdx N 0 anc s' := rfl
  rw [hfold]
  have hiff : swapIdx N 0 anc s' = t ↔ s' = s := by
    constructor
    · intro hcon
      have h2 := congrArg (swapIdx N 0 anc) hcon
      rw [hinv] at h2
      rw [h] at h2
      exact h2
    · intro hs
      have h2 := congrArg (swapIdx N 0 anc) h
      rw [hinv] at h2
      rw [hs]
      exact h2.symm
  simp only [Pi.single_apply, hiff]

private theorem perLabelCircuit_k0_false (anc : ℕ) :
    perLabelCircuit (k := 0) (fun i => i.elim0) 0 0 false anc = [outputSwap anc] := by
  simp only [perLabelCircuit, perLabelCore, List.finRange_zero, List.flatMap_nil]
  rw [ite_eq_right (by decide : ¬(false = true))]
  simp only [List.nil_append]

/-- Identity label at `k = 0` and the zero-coefficient sign convention:
acceptance follows the sign alone, and `c = 0` selects `neg = false`. -/
theorem perLabel_identity_and_zero_coeff
    (ψ : Fin (2 ^ 2) → ℂ) (hψ : sqNorm ψ = 1)
    (hclean : ∀ s : Fin (2 ^ 2), qBit 1 s.val = 1 → ψ s = 0) :
    acceptProb (applyCircuit 2
        (perLabelCircuit (k := 0) (fun i => i.elim0) 0 0 false 1) ψ) = 0 ∧
      acceptProb (applyCircuit 2
        (perLabelCircuit (k := 0) (fun i => i.elim0) 0 0 true 1) ψ) = 1 ∧
      acceptProb (applyCircuit 2
        (perLabelCircuit (k := 0) (fun i => i.elim0) 0 0 (decide ((0 : ℝ) < 0)) 1) ψ) = 0 := by
  have hexp : pauliExpect (fun i : Fin 0 => i.elim0) 0 0 ψ = sqNorm ψ :=
    pauliExpect_zero_label ψ
  have hmain : ∀ neg : Bool, acceptProb (applyCircuit 2
        (perLabelCircuit (k := 0) (fun i => i.elim0) 0 0 neg 1) ψ) =
        (sqNorm ψ - (if neg then -1 else 1) *
          pauliExpect (fun i : Fin 0 => i.elim0) 0 0 ψ) / 2 := by
    intro neg
    exact acceptProb_perLabelCircuit (N := 2) (k := 0) (anc := 1)
      (addr := (fun i : Fin 0 => (i.elim0 : ℕ)))
      (0 : Fin 0 → ZMod 2) (0 : Fin 0 → ZMod 2) neg
      (fun a _ _ => a.elim0) (fun i => i.elim0)
      (by decide) (by decide) (fun i => i.elim0) (ψ := ψ) hclean
  have hiff : (if (false : Bool) then (-1 : ℝ) else 1) = 1 := rfl
  have hift : (if (true : Bool) then (-1 : ℝ) else 1) = -1 := rfl
  have hdec : decide ((0 : ℝ) < 0) = false := decide_eq_false (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · have h := hmain false
    rw [hexp, hψ, hiff] at h
    norm_num at h
    exact h
  · have h := hmain true
    rw [hexp, hψ, hift] at h
    norm_num at h
    exact h
  · rw [hdec]
    have h := hmain false
    rw [hexp, hψ, hiff] at h
    norm_num at h
    exact h

/-- One-local `Z` at `N = 3`, ancilla `1`, address `![2]`, basis input
with qubit `2` set (index `4`): acceptance `1` for positive sign, `0` for
negative. And one-local `X` on a basis state is the fair coin. -/
theorem perLabel_one_local_checks :
    acceptProb (applyCircuit 3 (perLabelCircuit ![2] 0 ![1] false 1)
        (Pi.single 4 1)) = 1 ∧
      acceptProb (applyCircuit 3 (perLabelCircuit ![2] 0 ![1] true 1)
        (Pi.single 4 1)) = 0 ∧
      acceptProb (applyCircuit 3 (perLabelCircuit ![2] ![1] 0 false 1)
        (Pi.single 0 1)) = 1 / 2 := by
  have hexp : (dotProduct (![1] : Fin 1 → ZMod 2)
      (localBits (![2] : Fin 1 → ℕ) (4 : Fin (2 ^ 3)).val)).val = 1 := by decide
  have hz : ∀ neg : Bool, acceptProb (applyCircuit 3
      (perLabelCircuit ![2] 0 ![1] neg 1) (Pi.single 4 1)) =
      if (if neg then (-1 : ℝ) else 1) *
          (-1) ^ (dotProduct ![1] (localBits ![2] (4 : Fin (2 ^ 3)).val)).val = -1
        then 1 else 0 := by
    intro neg
    exact acceptProb_perLabelCircuit_single_zString (N := 3) (k := 1) (anc := 1)
      (addr := (![2] : Fin 1 → ℕ)) (![1] : Fin 1 → ZMod 2) neg
      (by decide) (by decide) (by decide) (by decide)
      (4 : Fin (2 ^ 3)) (by decide)
  have hiff : (if (false : Bool) then (-1 : ℝ) else 1) = 1 := rfl
  have hift : (if (true : Bool) then (-1 : ℝ) else 1) = -1 := rfl
  refine ⟨?_, ?_, ?_⟩
  · have h := hz false
    rw [hexp, hiff] at h
    norm_num at h
    exact h
  · have h := hz true
    rw [hexp, hift] at h
    norm_num at h
    exact h
  · have hclean : ∀ s : Fin (2 ^ 3), qBit 1 s.val = 1 →
        (Pi.single (0 : Fin (2 ^ 3)) 1 : Fin (2 ^ 3) → ℂ) s = 0 := by
      intro s hs
      have hne : s ≠ 0 := by
        intro hcon
        subst hcon
        exact absurd hs (by decide)
      exact Pi.single_eq_of_ne hne 1
    have h := acceptProb_perLabelCircuit (N := 3) (k := 1) (anc := 1)
      (addr := (![2] : Fin 1 → ℕ))
      (![1] : Fin 1 → ZMod 2) (0 : Fin 1 → ZMod 2) false
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (ψ := (Pi.single (0 : Fin (2 ^ 3)) 1 : Fin (2 ^ 3) → ℂ)) hclean
    have hexpX : pauliExpect (![2] : Fin 1 → ℕ) (![1] : Fin 1 → ZMod 2)
        (0 : Fin 1 → ZMod 2)
        (Pi.single (0 : Fin (2 ^ 3)) 1 : Fin (2 ^ 3) → ℂ) = 0 :=
      pauliExpect_piSingle_of_a_ne _ (![1] : Fin 1 → ZMod 2) _ _ 0 (by decide)
    rw [sqNorm_piSingle_one, hexpX, hiff] at h
    norm_num at h
    exact h

/-- The main identity instantiated at `N = 4`, ancilla `2`, addresses
`![3, 0]` with an `X` and a `Y` letter, with every side condition discharged
by `decide` (psi remains universally quantified). -/
theorem perLabel_orientation_instance
    (ψ : Fin (2 ^ 4) → ℂ)
    (hclean : ∀ s : Fin (2 ^ 4), qBit 2 s.val = 1 → ψ s = 0) :
    acceptProb (applyCircuit 4 (perLabelCircuit ![3, 0] ![1, 1] ![0, 1] false 2) ψ) =
      (sqNorm ψ - pauliExpect ![3, 0] ![1, 1] ![0, 1] ψ) / 2 := by
  have h := acceptProb_perLabelCircuit (N := 4) (k := 2) (anc := 2)
    (addr := (![3, 0] : Fin 2 → ℕ))
    (![1, 1] : Fin 2 → ZMod 2) (![0, 1] : Fin 2 → ZMod 2) false
    (by decide) (by decide) (by decide) (by decide) (by decide) (ψ := ψ) hclean
  rw [show (if (false : Bool) then (-1 : ℝ) else 1) = 1 from rfl, one_mul] at h
  exact h

/-- Concrete `signOne` instance: coefficient `-2`, one `Z` letter on
qubit `0`, the all-zero basis state; acceptance probability `1`. -/
theorem perLabel_signOne_instance :
    acceptProb (applyCircuit 2
    (perLabelCircuit ![0] ![0] ![1] (decide ((-2 : ℝ) < 0)) 1)
    (Pi.single 0 1)) = 1 := by
  have hψ : sqNorm (Pi.single (0 : Fin (2 ^ 2)) (1 : ℂ) : Fin (2 ^ 2) → ℂ) = 1 :=
    sqNorm_piSingle_one 0
  have hclean : ∀ s : Fin (2 ^ 2), qBit 1 s.val = 1 →
      (Pi.single (0 : Fin (2 ^ 2)) (1 : ℂ) : Fin (2 ^ 2) → ℂ) s = 0 := by
    intro s hs
    have hne : s ≠ 0 := by
      intro h
      subst h
      revert hs
      decide
    exact Pi.single_eq_of_ne hne _
  have hmain := acceptProb_perLabelCircuit_signOne (N := 2) (k := 1) (anc := 1)
    (addr := (![0] : Fin 1 → ℕ))
    (![0] : Fin 1 → ZMod 2) (![1] : Fin 1 → ZMod 2) (-2 : ℝ)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (ψ := Pi.single 0 1) hψ hclean
  have hexp : pauliExpect (![0] : Fin 1 → ℕ) (![0] : Fin 1 → ZMod 2)
      (![1] : Fin 1 → ZMod 2)
      (Pi.single (0 : Fin (2 ^ 2)) (1 : ℂ) : Fin (2 ^ 2) → ℂ) = 1 := by
    have hdot : (![1] : Fin 1 → ZMod 2) ⬝ᵥ (![0] : Fin 1 → ZMod 2) = 0 := by decide
    have hoffset0 : (![0] : Fin 1 → ZMod 2) = ![0] + ![0] := by decide
    have hlocal : localBits (![0] : Fin 1 → ℕ) (0 : Fin (2 ^ 2)).val = ![0] := by decide
    have hagree : (∀ q : ℕ, (∀ i, (![0] : Fin 1 → ℕ) i ≠ q) →
        qBit q ((0 : Fin (2 ^ 2)).val) = qBit q ((0 : Fin (2 ^ 2)).val)) :=
      fun q _h => rfl
    have hexp0 : ∑ i : Fin 1,
        (((![0] : Fin 1 → ZMod 2) i).val * (((![1] : Fin 1 → ZMod 2)) i).val) = 0 := by
      decide
    have hval : (0 : ZMod 2).val = 0 := by decide
    unfold pauliExpect dotProduct
    simp only [Pi.star_apply]
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_univ 0)
      (fun s _ hs => by rw [Pi.single_eq_of_ne hs, star_zero, zero_mul])]
    rw [Pi.single_eq_same, star_one, one_mul]
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_univ 0)
      (fun t _ ht => by rw [Pi.single_eq_of_ne ht, mul_zero])]
    rw [Pi.single_eq_same, mul_one]
    unfold pauliEmb embedLocal
    rw [ite_eq_left hagree, hlocal]
    unfold MathlibExt.Quantum.PauliExpansion.hermPauli
    rw [Matrix.smul_apply, smul_eq_mul, hexp0, pow_zero, one_mul]
    rw [MathlibExt.Quantum.PauliXZ.pauliXZ_apply, ite_eq_left hoffset0, hdot, hval,
      pow_zero]
    exact Complex.one_re
  have hsign : MathlibExt.Quantum.PauliExpansion.signOne (-2 : ℝ) = -1 := by
    norm_num [MathlibExt.Quantum.PauliExpansion.signOne]
  rw [hsign, hexp] at hmain
  norm_num at hmain
  have hd : decide ((-2 : ℝ) < 0) = true := by
    rw [decide_eq_true_eq]
    norm_num
  rw [hd]
  exact hmain

/-- The clean-ancilla hypothesis cannot be dropped: at `k = 0` with the
ancilla bit set, the circuit accepts with probability `1` while the
identity's right side is `0`. -/
theorem perLabel_clean_necessary :
    acceptProb (applyCircuit 2
        (perLabelCircuit (k := 0) (fun i => i.elim0) 0 0 false 1)
        (Pi.single 2 1)) = 1 ∧
      (sqNorm (Pi.single (2 : Fin (2 ^ 2)) (1 : ℂ)) -
        pauliExpect (fun i : Fin 0 => i.elim0) 0 0
          ((Pi.single (2 : Fin (2 ^ 2)) (1 : ℂ)) : Fin (2 ^ 2) → ℂ)) / 2 = 0 := by
  refine ⟨?_, ?_⟩
  · rw [perLabelCircuit_k0_false]
    have h := applyCircuit_outputSwap_single (N := 2) (anc := 1)
      (by decide) (by decide) (2 : Fin (2 ^ 2)) (1 : Fin (2 ^ 2)) (by decide)
    rw [h]
    exact acceptProb_piSingle_one _ (by decide)
  · have hsq : sqNorm ((Pi.single (2 : Fin (2 ^ 2)) (1 : ℂ)) : Fin (2 ^ 2) → ℂ) = 1 :=
      sqNorm_piSingle_one _
    have hexp : pauliExpect (fun i : Fin 0 => i.elim0) 0 0
        ((Pi.single (2 : Fin (2 ^ 2)) (1 : ℂ)) : Fin (2 ^ 2) → ℂ) =
        sqNorm ((Pi.single (2 : Fin (2 ^ 2)) (1 : ℂ)) : Fin (2 ^ 2) → ℂ) :=
      pauliExpect_zero_label _
    rw [hexp, hsq]
    norm_num

/-- Without `sqNorm ψ = 1` the identity gives an acceptance weight, not a
probability: at `k = 0` with the negative sign, the state `2|00⟩` has weight
`4`. -/
theorem perLabel_unnormalized_weight :
    acceptProb (applyCircuit 2
        (perLabelCircuit (k := 0) (fun i => i.elim0) 0 0 true 1)
        (Pi.single 0 2)) = 4 := by
  have hclean : ∀ s : Fin (2 ^ 2), qBit 1 s.val = 1 →
      (Pi.single (0 : Fin (2 ^ 2)) (2 : ℂ) : Fin (2 ^ 2) → ℂ) s = 0 := by
    intro s hs
    have hne : s ≠ 0 := by
      rintro rfl
      revert hs
      decide
    exact Pi.single_eq_of_ne hne _
  have h := acceptProb_perLabelCircuit (N := 2) (k := 0) (anc := 1)
    (addr := (fun i : Fin 0 => (i.elim0 : ℕ)))
    (0 : Fin 0 → ZMod 2) (0 : Fin 0 → ZMod 2) true
    (fun a _ _ => a.elim0) (fun i => i.elim0)
    (by decide) (by decide) (fun i => i.elim0)
    (ψ := (Pi.single (0 : Fin (2 ^ 2)) (2 : ℂ) : Fin (2 ^ 2) → ℂ)) hclean
  have hsq : sqNorm (Pi.single (0 : Fin (2 ^ 2)) (2 : ℂ) : Fin (2 ^ 2) → ℂ) = 4 := by
    unfold sqNorm
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_univ 0) (fun s _ hs => by
      simp only [Pi.single_eq_of_ne hs, map_zero, zero_mul, Complex.zero_re])]
    rw [Pi.single_eq_same]
    norm_num
  rw [pauliExpect_zero_label, hsq] at h
  rw [h]
  norm_num

private theorem perLabelCircuit_dupXZ_gateList :
    perLabelCircuit ![0, 0] ![1, 0] ![0, 1] true 1
      = [embeddedGate omegaH 0 1, controlledGate xGate 0 1,
        controlledGate xGate 0 1, embeddedGate xGate 1 0, outputSwap 1] := by
  have hfr : List.finRange 2 = [0, 1] := by decide
  have hb0 : basisChangeGates ((![1, 0] : Fin 2 → ZMod 2) 0) ((![0, 1] : Fin 2 → ZMod 2) 0)
      ((![0, 0] : Fin 2 → ℕ) 0) 1 = [embeddedGate omegaH 0 1] := rfl
  have hp0 : parityGates ((![1, 0] : Fin 2 → ZMod 2) 0) ((![0, 1] : Fin 2 → ZMod 2) 0)
      ((![0, 0] : Fin 2 → ℕ) 0) 1 = [controlledGate xGate 0 1] := rfl
  have hb1 : basisChangeGates ((![1, 0] : Fin 2 → ZMod 2) 1) ((![0, 1] : Fin 2 → ZMod 2) 1)
      ((![0, 0] : Fin 2 → ℕ) 1) 1 = [] := rfl
  have hp1 : parityGates ((![1, 0] : Fin 2 → ZMod 2) 1) ((![0, 1] : Fin 2 → ZMod 2) 1)
      ((![0, 0] : Fin 2 → ℕ) 1) 1 = [controlledGate xGate 0 1] := rfl
  simp only [perLabelCircuit, perLabelCore, hfr, List.flatMap_cons, List.flatMap_nil, hb0, hp0,
    hb1, hp1]
  rw [ite_eq_left True.intro]
  simp only [List.cons_append, List.nil_append, List.append_nil]

private theorem applyGate_omegaH_piSingle_zero_dupXZ :
    applyGate 2 (embeddedGate omegaH 0 1)
        ((Pi.single (0 : Fin (2 ^ 2)) (1 : ℂ)) : Fin (2 ^ 2) → ℂ) =
      (fun s : Fin (2 ^ 2) => if s = 0 then complexOfGRatMatrix omegaH 0 0
        else if s = 1 then complexOfGRatMatrix omegaH 1 0 else 0) := by
  have hg : QGateWellFormed 2 (embeddedGate omegaH 0 1) :=
    embeddedGate_wellFormed omegaH omegaH_unitary (by decide) (by decide) (by decide)
  funext s
  rw [applyGate_embeddedGate hg, Fin.sum_univ_two]
  by_cases hs0 : s = 0
  · subst hs0
    have hq : qBit 0 (0 : Fin (2 ^ 2)).val = 0 := by decide
    have hs00 : setQBit 2 0 0 (0 : Fin (2 ^ 2)) = 0 := by decide
    have hs01 : setQBit 2 0 1 (0 : Fin (2 ^ 2)) = 1 := by decide
    rw [hq, hs00, hs01, Pi.single_eq_same,
      Pi.single_eq_of_ne (by decide : (1 : Fin (2 ^ 2)) ≠ 0) _, ite_eq_left rfl]
    simp
  · by_cases hs1 : s = 1
    · subst hs1
      have hq : qBit 0 (1 : Fin (2 ^ 2)).val = 1 := by decide
      have hs10 : setQBit 2 0 0 (1 : Fin (2 ^ 2)) = 0 := by decide
      have hs11 : setQBit 2 0 1 (1 : Fin (2 ^ 2)) = 1 := by decide
      rw [hq, hs10, hs11, Pi.single_eq_same,
        Pi.single_eq_of_ne (by decide : (1 : Fin (2 ^ 2)) ≠ 0) _,
        ite_eq_right hs0, ite_eq_left rfl]
      simp
    · by_cases hs2 : s = 2
      · subst hs2
        have hq : qBit 0 (2 : Fin (2 ^ 2)).val = 0 := by decide
        have hs20 : setQBit 2 0 0 (2 : Fin (2 ^ 2)) = 2 := by decide
        have hs21 : setQBit 2 0 1 (2 : Fin (2 ^ 2)) = 3 := by decide
        rw [hq, hs20, hs21,
          Pi.single_eq_of_ne (by decide : (2 : Fin (2 ^ 2)) ≠ 0) _,
          Pi.single_eq_of_ne (by decide : (3 : Fin (2 ^ 2)) ≠ 0) _,
          ite_eq_right hs0, ite_eq_right hs1]
        simp
      · have hs3 : s = 3 := by
          have hall : ∀ t : Fin (2 ^ 2), t ≠ 0 → t ≠ 1 → t ≠ 2 → t = 3 := by decide
          exact hall s hs0 hs1 hs2
        subst hs3
        have hq : qBit 0 (3 : Fin (2 ^ 2)).val = 1 := by decide
        have hs30 : setQBit 2 0 0 (3 : Fin (2 ^ 2)) = 2 := by decide
        have hs31 : setQBit 2 0 1 (3 : Fin (2 ^ 2)) = 3 := by decide
        rw [hq, hs30, hs31,
          Pi.single_eq_of_ne (by decide : (2 : Fin (2 ^ 2)) ≠ 0) _,
          Pi.single_eq_of_ne (by decide : (3 : Fin (2 ^ 2)) ≠ 0) _,
          ite_eq_right hs0, ite_eq_right hs1]
        simp

private theorem applyCircuit_cnotPair_id_dupXZ (ψ : Fin (2 ^ 2) → ℂ) :
    applyCircuit 2 [controlledGate xGate 0 1, controlledGate xGate 0 1] ψ = ψ := by
  simp only [applyCircuit, List.foldl_cons, List.foldl_nil]
  funext s
  have hpt : ∀ (φ : Fin (2 ^ 2) → ℂ) (t : Fin (2 ^ 2)),
      applyGate 2 (controlledGate xGate 0 1) φ t = φ (cnotIndex 2 0 1 t) := by
    intro φ t
    rw [applyGate_cnot]
    all_goals decide
  rw [hpt, hpt]
  have hinv : ∀ t : Fin (2 ^ 2), cnotIndex 2 0 1 (cnotIndex 2 0 1 t) = t := by decide
  rw [hinv]

private theorem applyGate_xGate_psi1_dupXZ :
    applyGate 2 (embeddedGate xGate 1 0)
        (fun s : Fin (2 ^ 2) => if s = 0 then complexOfGRatMatrix omegaH 0 0
          else if s = 1 then complexOfGRatMatrix omegaH 1 0 else 0) =
      (fun s : Fin (2 ^ 2) => if s = 2 then complexOfGRatMatrix omegaH 0 0
        else if s = 3 then complexOfGRatMatrix omegaH 1 0 else 0) := by
  have hflip : ∀ t : Fin (2 ^ 2), applyGate 2 (embeddedGate xGate 1 0)
      (fun s : Fin (2 ^ 2) => if s = 0 then complexOfGRatMatrix omegaH 0 0
        else if s = 1 then complexOfGRatMatrix omegaH 1 0 else 0) t =
      (fun s : Fin (2 ^ 2) => if s = 0 then complexOfGRatMatrix omegaH 0 0
        else if s = 1 then complexOfGRatMatrix omegaH 1 0 else 0) (flipBit 2 1 t) := by
    intro t
    rw [applyGate_embeddedGate_xGate]
    all_goals decide
  funext s
  rw [hflip]
  by_cases hs0 : s = 0
  · subst hs0
    have hf : flipBit 2 1 (0 : Fin (2 ^ 2)) = 2 := by decide
    rw [hf]
    split_ifs <;> simp_all
  · by_cases hs1 : s = 1
    · subst hs1
      have hf : flipBit 2 1 (1 : Fin (2 ^ 2)) = 3 := by decide
      rw [hf]
      split_ifs <;> simp_all
    · by_cases hs2 : s = 2
      · subst hs2
        have hf : flipBit 2 1 (2 : Fin (2 ^ 2)) = 0 := by decide
        rw [hf]
        split_ifs <;> simp_all
      · have hs3 : s = 3 := by
          have hall : ∀ t : Fin (2 ^ 2), t ≠ 0 → t ≠ 1 → t ≠ 2 → t = 3 := by decide
          exact hall s hs0 hs1 hs2
        subst hs3
        have hf : flipBit 2 1 (3 : Fin (2 ^ 2)) = 1 := by decide
        rw [hf]
        split_ifs <;> simp_all

private theorem applyGate_swap_psi3_dupXZ :
    applyGate 2 (outputSwap 1)
        (fun s : Fin (2 ^ 2) => if s = 2 then complexOfGRatMatrix omegaH 0 0
          else if s = 3 then complexOfGRatMatrix omegaH 1 0 else 0) =
      (fun s : Fin (2 ^ 2) => if s = 1 then complexOfGRatMatrix omegaH 0 0
        else if s = 3 then complexOfGRatMatrix omegaH 1 0 else 0) := by
  have hswap : outputSwap 1 = (0, 1, swapEntries) := rfl
  rw [hswap]
  funext s
  rw [applyGate_swap (by decide : 0 < 1) (by decide : 1 < 2)]
  by_cases hs0 : s = 0
  · subst hs0
    have hidx : setQBit 2 0 (qBit 1 (0 : Fin (2 ^ 2)).val)
        (setQBit 2 1 (qBit 0 (0 : Fin (2 ^ 2)).val) 0) = 0 := by decide
    rw [hidx]
    split_ifs <;> simp_all
  · by_cases hs1 : s = 1
    · subst hs1
      have hidx : setQBit 2 0 (qBit 1 (1 : Fin (2 ^ 2)).val)
          (setQBit 2 1 (qBit 0 (1 : Fin (2 ^ 2)).val) 1) = 2 := by decide
      rw [hidx]
      split_ifs <;> simp_all
    · by_cases hs2 : s = 2
      · subst hs2
        have hidx : setQBit 2 0 (qBit 1 (2 : Fin (2 ^ 2)).val)
            (setQBit 2 1 (qBit 0 (2 : Fin (2 ^ 2)).val) 2) = 1 := by decide
        rw [hidx]
        split_ifs <;> simp_all
      · have hs3 : s = 3 := by
          have hall : ∀ t : Fin (2 ^ 2), t ≠ 0 → t ≠ 1 → t ≠ 2 → t = 3 := by decide
          exact hall s hs0 hs1 hs2
        subst hs3
        have hidx : setQBit 2 0 (qBit 1 (3 : Fin (2 ^ 2)).val)
            (setQBit 2 1 (qBit 0 (3 : Fin (2 ^ 2)).val) 3) = 3 := by decide
        rw [hidx]
        split_ifs <;> simp_all

private theorem applyCircuit_dupXZ_final :
    applyCircuit 2 [embeddedGate omegaH 0 1, controlledGate xGate 0 1,
        controlledGate xGate 0 1, embeddedGate xGate 1 0, outputSwap 1]
        ((Pi.single (0 : Fin (2 ^ 2)) (1 : ℂ)) : Fin (2 ^ 2) → ℂ) =
      (fun s : Fin (2 ^ 2) => if s = 1 then complexOfGRatMatrix omegaH 0 0
        else if s = 3 then complexOfGRatMatrix omegaH 1 0 else 0) := by
  rw [show [embeddedGate omegaH 0 1, controlledGate xGate 0 1,
      controlledGate xGate 0 1, embeddedGate xGate 1 0, outputSwap 1] =
      [embeddedGate omegaH 0 1] ++ [controlledGate xGate 0 1, controlledGate xGate 0 1] ++
        [embeddedGate xGate 1 0] ++ [outputSwap 1] from rfl]
  rw [applyCircuit_append, applyCircuit_append, applyCircuit_append]
  rw [applyCircuit_cnotPair_id_dupXZ]
  simp only [applyCircuit, List.foldl_cons, List.foldl_nil]
  rw [applyGate_omegaH_piSingle_zero_dupXZ, applyGate_xGate_psi1_dupXZ,
    applyGate_swap_psi3_dupXZ]

private theorem pauliExpect_dupXZ_eq_zero :
    pauliExpect ![0, 0] ![1, 0] ![0, 1]
      ((Pi.single (0 : Fin (2 ^ 2)) (1 : ℂ)) : Fin (2 ^ 2) → ℂ) = 0 := by
  have hlocal : localBits (![0, 0] : Fin 2 → ℕ) ((0 : Fin (2 ^ 2)).val) =
      (0 : Fin 2 → ZMod 2) := by
    funext i
    fin_cases i <;> decide
  have hagree : (∀ q : ℕ, (∀ i, (![0, 0] : Fin 2 → ℕ) i ≠ q) →
      qBit q ((0 : Fin (2 ^ 2)).val) = qBit q ((0 : Fin (2 ^ 2)).val)) :=
    fun q _ => rfl
  have hexp : ∑ i : Fin 2, (((![1, 0] : Fin 2 → ZMod 2) i).val *
      (((![0, 1] : Fin 2 → ZMod 2)) i).val) = 0 := by decide
  have hcond : ¬ ((0 : Fin 2 → ZMod 2) = 0 + ![1, 0]) := by decide
  unfold pauliExpect dotProduct
  simp only [Pi.star_apply]
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_univ 0) (fun s _ hs => by
    rw [Pi.single_eq_of_ne hs, star_zero, zero_mul])]
  rw [Pi.single_eq_same, star_one, one_mul]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_univ 0) (fun t _ ht => by
    rw [Pi.single_eq_of_ne ht, mul_zero])]
  rw [Pi.single_eq_same, mul_one]
  unfold pauliEmb embedLocal
  rw [ite_eq_left hagree, hlocal]
  unfold MathlibExt.Quantum.PauliExpansion.hermPauli
  rw [Matrix.smul_apply, smul_eq_mul, hexp, pow_zero, one_mul]
  rw [MathlibExt.Quantum.PauliXZ.pauliXZ_apply, ite_eq_right hcond]
  exact Complex.zero_re

/-- Injectivity cannot be dropped: with duplicate addresses `![0, 0]`, an `X`
letter and a `Z` letter on qubit `0`, and the ancilla clean, the circuit
accepts the all-zero basis state with probability `1` where the identity would
give `1/2`: the duplicated embedding of this label is the zero operator, so the
expectation vanishes. Every other hypothesis of `acceptProb_perLabelCircuit`
holds here (in range, ancilla unaddressed, clean ancilla). -/
theorem perLabel_injective_necessary :
    acceptProb (applyCircuit 2 (perLabelCircuit ![0, 0] ![1, 0] ![0, 1] true 1)
        (Pi.single 0 1)) = 1 ∧
      (sqNorm (Pi.single (0 : Fin (2 ^ 2)) (1 : ℂ)) -
        (if true then (-1 : ℝ) else 1) * pauliExpect ![0, 0] ![1, 0] ![0, 1]
          ((Pi.single (0 : Fin (2 ^ 2)) (1 : ℂ)) : Fin (2 ^ 2) → ℂ)) / 2 = 1 / 2 ∧
      ∀ s : Fin (2 ^ 2), qBit 1 s.val = 1 →
        (Pi.single (0 : Fin (2 ^ 2)) 1 : Fin (2 ^ 2) → ℂ) s = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [perLabelCircuit_dupXZ_gateList]
    have hfinal := applyCircuit_dupXZ_final
    have hsupp : ∀ s : Fin (2 ^ 2), qBit 0 s.val ≠ 1 →
        applyCircuit 2 [embeddedGate omegaH 0 1, controlledGate xGate 0 1,
          controlledGate xGate 0 1, embeddedGate xGate 1 0, outputSwap 1]
          ((Pi.single (0 : Fin (2 ^ 2)) (1 : ℂ)) : Fin (2 ^ 2) → ℂ) s = 0 := by
      intro s hs
      rw [hfinal]
      have h1 : s ≠ 1 := by
        intro h
        subst h
        exact hs (by decide : qBit 0 (1 : Fin (2 ^ 2)).val = 1)
      have h3 : s ≠ 3 := by
        intro h
        subst h
        exact hs (by decide : qBit 0 (3 : Fin (2 ^ 2)).val = 1)
      change (if s = 1 then complexOfGRatMatrix omegaH 0 0
        else if s = 3 then complexOfGRatMatrix omegaH 1 0 else 0) = 0
      split_ifs <;> simp_all
    have hacc : acceptProb (applyCircuit 2 [embeddedGate omegaH 0 1,
        controlledGate xGate 0 1, controlledGate xGate 0 1,
        embeddedGate xGate 1 0, outputSwap 1]
        ((Pi.single (0 : Fin (2 ^ 2)) (1 : ℂ)) : Fin (2 ^ 2) → ℂ)) =
        sqNorm (applyCircuit 2 [embeddedGate omegaH 0 1, controlledGate xGate 0 1,
          controlledGate xGate 0 1, embeddedGate xGate 1 0, outputSwap 1]
          ((Pi.single (0 : Fin (2 ^ 2)) (1 : ℂ)) : Fin (2 ^ 2) → ℂ)) := by
      unfold acceptProb sqNorm
      apply Finset.sum_congr rfl
      intro s _
      by_cases h : qBit 0 s.val = 1
      · rw [ite_eq_left h]
      · rw [ite_eq_right h, hsupp s h]
        simp
    have hwf : ∀ g ∈ [embeddedGate omegaH 0 1, controlledGate xGate 0 1,
        controlledGate xGate 0 1, embeddedGate xGate 1 0, outputSwap 1],
        QGateWellFormed 2 g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl
      · exact embeddedGate_wellFormed omegaH omegaH_unitary (by decide) (by decide) (by decide)
      · exact controlledGate_wellFormed xGate xGate_unitary (by decide) (by decide) (by decide)
      · exact controlledGate_wellFormed xGate xGate_unitary (by decide) (by decide) (by decide)
      · exact embeddedGate_wellFormed xGate xGate_unitary (by decide) (by decide) (by decide)
      · have hswap : outputSwap 1 = (0, 1, swapEntries) := rfl
        rw [hswap]
        exact qGateWellFormed_swap (by decide) (by decide)
    have hsq : sqNorm (applyCircuit 2 [embeddedGate omegaH 0 1,
        controlledGate xGate 0 1, controlledGate xGate 0 1,
        embeddedGate xGate 1 0, outputSwap 1]
        ((Pi.single (0 : Fin (2 ^ 2)) (1 : ℂ)) : Fin (2 ^ 2) → ℂ)) = 1 := by
      have hpres := sqNorm_applyCircuit hwf
        ((Pi.single (0 : Fin (2 ^ 2)) (1 : ℂ)) : Fin (2 ^ 2) → ℂ)
      rw [hpres]
      exact sqNorm_piSingle_one _
    rw [hacc, hsq]
  · have hsq : sqNorm ((Pi.single (0 : Fin (2 ^ 2)) (1 : ℂ)) : Fin (2 ^ 2) → ℂ) = 1 :=
      sqNorm_piSingle_one _
    rw [hsq, pauliExpect_dupXZ_eq_zero, ite_eq_left rfl]
    norm_num
  · intro s hs
    have hne : s ≠ 0 := by
      rintro rfl
      revert hs
      decide
    exact Pi.single_eq_of_ne hne _

/-- The output is read from the ancilla, not the original qubit `0`. -/
theorem perLabel_output_convention :
    acceptProb (applyCircuit 3 [outputSwap 1] (Pi.single 2 1)) = 1 ∧
      acceptProb (applyCircuit 3 [outputSwap 1] (Pi.single 1 1)) = 0 := by
  refine ⟨?_, ?_⟩
  · have h := applyCircuit_outputSwap_single (N := 3) (anc := 1)
      (by decide) (by decide) (2 : Fin (2 ^ 3)) (1 : Fin (2 ^ 3)) (by decide)
    rw [h]
    exact acceptProb_piSingle_one _ (by decide)
  · have h := applyCircuit_outputSwap_single (N := 3) (anc := 1)
      (by decide) (by decide) (1 : Fin (2 ^ 3)) (2 : Fin (2 ^ 3)) (by decide)
    rw [h]
    exact acceptProb_piSingle_zero _ (by decide)

/-- Expectation range and concrete well-formedness/size instances. -/
theorem perLabel_range_and_concrete
    (ψ : Fin (2 ^ 3) → ℂ) (hψ : sqNorm ψ = 1) :
    |pauliExpect ![2] ![1] ![1] ψ| ≤ 1 ∧
      (∀ g ∈ perLabelCircuit ![2] ![1] ![1] true 1, QGateWellFormed 3 g) ∧
      (perLabelCircuit ![2] ![1] ![1] true 1).length ≤ 5 := by
  refine ⟨?_, ?_, ?_⟩
  · have h := abs_pauliExpect_le (N := 3) (k := 1) (addr := (![2] : Fin 1 → ℕ))
      (by decide) (by decide) (![1] : Fin 1 → ZMod 2) (![1] : Fin 1 → ZMod 2) ψ
    rw [hψ] at h
    exact h
  · exact perLabelCircuit_wellFormed (N := 3) (k := 1) (anc := 1)
      (addr := (![2] : Fin 1 → ℕ)) (![1] : Fin 1 → ZMod 2)
      (![1] : Fin 1 → ZMod 2) true (by decide) (by decide) (by decide) (by decide)
  · have h := perLabelCircuit_length_le (k := 1) (anc := 1)
      (![2] : Fin 1 → ℕ) (![1] : Fin 1 → ZMod 2) (![1] : Fin 1 → ZMod 2) true
    rw [show 3 * 1 + 2 = 5 from rfl] at h
    exact h

end Cslib.Complexity.Classes.Tests
