/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QuantumGates.CircuitSemantics
public import CSLibExt.Computability.Complexity.QMA.BlockEigenbasis
public import CSLibExt.Computability.Complexity.QMA.ThresholdOperator

-- Private Mathlib dependencies of the proofs below.
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Filter
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid

/-!
# Product law for disjoint registers

Measurement factorization for computational-basis events on disjoint
registers prepared in a product state: the Born weight of an arbitrary
block-readout event is the sum over the event of the per-block Born
weights, and the joint law of the per-block output qubits is the product
of the per-block accept/reject weights. For normalized blocks, the
threshold event on output bits has exactly the heterogeneous Bernoulli
tail weight `QMA.tailWeight` (identity only; no tail bound is proved
here). Registers are the contiguous blocks of `QMA.blockProd`, optionally
followed by a trailing register through `tensorProd`; non-contiguous
embeddings are the consumers' relabeling step. No claim is made about
entangled states.

Source: M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum
Information, Cambridge University Press, 2000, Chapter 2 (tensor products
and the Born rule).
-/

@[expose] public section

namespace Cslib.Complexity.Classes

set_option autoImplicit false

open Cslib.Complexity.Classes.QMA

/-- Powers of two are positive. -/
private theorem pos_two_pow (a : ℕ) : 0 < 2 ^ a := by
  have h := @Nat.one_le_two_pow a
  omega

/-- `(star z * z)` is the nonnegative real `Complex.normSq z`. -/
private theorem starSelf_mul_self (z : ℂ) :
    starRingEnd ℂ z * z = ((Complex.normSq z : ℝ) : ℂ) := by
  rw [mul_comm, Complex.mul_conj]

/-- Real part of `star z * z`. -/
private theorem starSelf_mul_self_re (z : ℂ) :
    (starRingEnd ℂ z * z).re = Complex.normSq z := by
  rw [starSelf_mul_self, Complex.ofReal_re]

/-- Born weight of a product state factors over the product. -/
private theorem starProd_re {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    (starRingEnd ℂ (∏ i, z i) * ∏ i, z i).re
      = ∏ i, (starRingEnd ℂ (z i) * z i).re := by
  rw [map_prod (starRingEnd ℂ), ← Finset.prod_mul_distrib]
  have h : ∀ i, starRingEnd ℂ (z i) * z i = ((Complex.normSq (z i) : ℝ) : ℂ) :=
    fun i => starSelf_mul_self (z i)
  rw [Finset.prod_congr rfl (fun i _ => h i), ← Complex.ofReal_prod,
    Complex.ofReal_re]
  simp only [starSelf_mul_self_re]

/-- Born weight of a two-factor product. -/
private theorem starMul_re (a b : ℂ) :
    (starRingEnd ℂ (a * b) * (a * b)).re
      = (starRingEnd ℂ a * a).re * (starRingEnd ℂ b * b).re := by
  rw [map_mul (starRingEnd ℂ), starSelf_mul_self_re, starSelf_mul_self_re]
  have h : (starRingEnd ℂ a * starRingEnd ℂ b) * (a * b)
      = ((Complex.normSq a * Complex.normSq b : ℝ) : ℂ) := by
    rw [show (starRingEnd ℂ a * starRingEnd ℂ b) * (a * b)
        = (starRingEnd ℂ a * a) * (starRingEnd ℂ b * b) by ac_rfl,
      starSelf_mul_self, starSelf_mul_self, ← Complex.ofReal_mul]
  rw [h, Complex.ofReal_re]

/-- The `i`-th digit of `blockEquiv k m j` is `j i`. -/
private theorem blockDigit_blockEquiv_apply {k m : ℕ}
    (j : Fin k → Fin (2 ^ m)) (i : Fin k) :
    blockDigit k m i ((blockEquiv k m) j) = j i := by
  have h2 := congrArg (fun f : Fin k → Fin (2 ^ m) => f i)
    (Equiv.symm_apply_apply (blockEquiv k m) j)
  rw [QMA.blockEquiv_symm_apply] at h2
  exact h2

/-- A product state evaluated on `blockEquiv k m j`. -/
private theorem blockProd_blockEquiv_apply {k m : ℕ}
    (ψ : Fin k → Fin (2 ^ m) → ℂ) (j : Fin k → Fin (2 ^ m)) :
    blockProd ψ ((blockEquiv k m) j) = ∏ i, ψ i (j i) := by
  have hu : blockProd ψ ((blockEquiv k m) j)
      = ∏ i, ψ i (blockDigit k m i ((blockEquiv k m) j)) := rfl
  rw [hu]
  exact Finset.prod_congr rfl (fun i _ => by rw [blockDigit_blockEquiv_apply])

/-- **Product law, readout events.** The Born weight of an arbitrary
block-readout event `E` of a `k`-block product state is the sum over `E`
of the products of per-block Born weights. -/
theorem eventWeight_blockProd {k m : ℕ} (ψ : Fin k → Fin (2 ^ m) → ℂ)
    (E : Finset (Fin k → Fin (2 ^ m))) :
    (∑ s : Fin (2 ^ (k * m)),
        if (fun i => blockDigit k m i s) ∈ E then
          (starRingEnd ℂ (blockProd ψ s) * blockProd ψ s).re else 0) =
      ∑ j ∈ E, ∏ i, (starRingEnd ℂ (ψ i (j i)) * ψ i (j i)).re := by
  trans ∑ j : (Fin k → Fin (2 ^ m)),
      (if (fun i => blockDigit k m i ((blockEquiv k m) j)) ∈ E then
        (starRingEnd ℂ (blockProd ψ ((blockEquiv k m) j)) *
          blockProd ψ ((blockEquiv k m) j)).re else 0)
  · exact (Equiv.sum_comp (blockEquiv k m) _).symm
  · trans ∑ j : (Fin k → Fin (2 ^ m)),
        (if j ∈ E then ∏ i, (starRingEnd ℂ (ψ i (j i)) * ψ i (j i)).re else 0)
    · apply Finset.sum_congr rfl
      intro j _
      have hdig : (fun i => blockDigit k m i ((blockEquiv k m) j)) = j :=
        funext (fun i => blockDigit_blockEquiv_apply j i)
      rw [hdig, blockProd_blockEquiv_apply, starProd_re]
    · rw [← Finset.sum_filter]
      congr 1
      ext j
      simp

/-- Split of `Fin (2 ^ (a + b))` into high and low parts. -/
private def prodSplitEquiv (a b : ℕ) :
    Fin (2 ^ b) × Fin (2 ^ a) ≃ Fin (2 ^ (a + b)) :=
  finProdFinEquiv.trans (finCongr (by rw [pow_add, mul_comm]))

/-- Value computation for `prodSplitEquiv`. -/
private theorem prodSplitEquiv_apply_val (a b : ℕ) (h : Fin (2 ^ b))
    (t : Fin (2 ^ a)) :
    ((prodSplitEquiv a b) (h, t)).val = t.val + 2 ^ a * h.val := by
  rw [prodSplitEquiv, Equiv.trans_apply, finCongr_apply_coe]
  exact finProdFinEquiv_apply_val (h, t)

/-- The low part of `prodSplitEquiv (h, t)` is `t`. -/
private theorem prodSplitEquiv_mod (a b : ℕ) (h : Fin (2 ^ b))
    (t : Fin (2 ^ a)) :
    ((prodSplitEquiv a b) (h, t)).val % 2 ^ a = t.val := by
  rw [prodSplitEquiv_apply_val, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt t.isLt]

/-- The high part of `prodSplitEquiv (h, t)` is `h`. -/
private theorem prodSplitEquiv_div (a b : ℕ) (h : Fin (2 ^ b))
    (t : Fin (2 ^ a)) :
    ((prodSplitEquiv a b) (h, t)).val / 2 ^ a = h.val := by
  have h0 : t.val / 2 ^ a = 0 := Nat.div_eq_zero_iff.mpr (Or.inr t.isLt)
  rw [prodSplitEquiv_apply_val,
    Nat.add_mul_div_left _ _ (pos_two_pow a), h0, zero_add]

/-- Factoring a constant out of a filtered product-sum. -/
private theorem ite_mul_zero_right (c : Prop) [Decidable c] (a b : ℝ) :
    (if c then a * b else 0) = (if c then a else 0) * b := by
  by_cases h : c <;> simp [h]

/-- **Product law with a trailing register.** The same factorization for
`blockProd ψ ⊗ χ`, where the event reads only the low `k * m` qubits; the
trailing register contributes its squared norm. -/
theorem eventWeight_tensorProd_blockProd {k m r : ℕ}
    (ψ : Fin k → Fin (2 ^ m) → ℂ) (χ : Fin (2 ^ r) → ℂ)
    (E : Finset (Fin k → Fin (2 ^ m))) :
    (∑ s : Fin (2 ^ (k * m + r)),
        if (fun i => blockDigit k m i
              ⟨s.val % 2 ^ (k * m), Nat.mod_lt _ (by positivity)⟩) ∈ E then
          (starRingEnd ℂ (tensorProd (blockProd ψ) χ s) *
            tensorProd (blockProd ψ) χ s).re else 0) =
      sqNorm χ * ∑ j ∈ E, ∏ i, (starRingEnd ℂ (ψ i (j i)) * ψ i (j i)).re := by
  trans ∑ x : Fin (2 ^ r) × Fin (2 ^ (k * m)),
      (if (fun i => blockDigit k m i
              ⟨((prodSplitEquiv (k * m) r) x).val % 2 ^ (k * m),
                Nat.mod_lt _ (pos_two_pow (k * m))⟩) ∈ E then
        (starRingEnd ℂ (tensorProd (blockProd ψ) χ ((prodSplitEquiv (k * m) r) x)) *
          tensorProd (blockProd ψ) χ ((prodSplitEquiv (k * m) r) x)).re else 0)
  · exact (Equiv.sum_comp (prodSplitEquiv (k * m) r) _).symm
  · simp only [Fintype.sum_prod_type]
    trans ∑ h : Fin (2 ^ r), ∑ t : Fin (2 ^ (k * m)),
        (if (fun i => blockDigit k m i t) ∈ E then
          (starRingEnd ℂ (blockProd ψ t) * blockProd ψ t).re *
            (starRingEnd ℂ (χ h) * χ h).re else 0)
    · apply Finset.sum_congr rfl
      intro h _
      apply Finset.sum_congr rfl
      intro t _
      have hmod : ((prodSplitEquiv (k * m) r) (h, t)).val % 2 ^ (k * m) = t.val :=
        prodSplitEquiv_mod (k * m) r h t
      have hdiv : ((prodSplitEquiv (k * m) r) (h, t)).val / 2 ^ (k * m) = h.val :=
        prodSplitEquiv_div (k * m) r h t
      have hlow : ∀ hh : ((prodSplitEquiv (k * m) r) (h, t)).val % 2 ^ (k * m)
            < 2 ^ (k * m),
          (⟨((prodSplitEquiv (k * m) r) (h, t)).val % 2 ^ (k * m),
            hh⟩ : Fin (2 ^ (k * m))) = t :=
        fun _ => Fin.ext hmod
      have hhigh : ∀ hh : ((prodSplitEquiv (k * m) r) (h, t)).val / 2 ^ (k * m)
            < 2 ^ r,
          (⟨((prodSplitEquiv (k * m) r) (h, t)).val / 2 ^ (k * m),
            hh⟩ : Fin (2 ^ r)) = h :=
        fun _ => Fin.ext hdiv
      have hten : tensorProd (blockProd ψ) χ ((prodSplitEquiv (k * m) r) (h, t))
          = blockProd ψ ⟨((prodSplitEquiv (k * m) r) (h, t)).val % 2 ^ (k * m),
              Nat.mod_lt _ (pos_two_pow (k * m))⟩
            * χ ⟨((prodSplitEquiv (k * m) r) (h, t)).val / 2 ^ (k * m), by
              rw [hdiv]
              exact h.isLt⟩ := rfl
      rw [hten]
      simp only [hlow, hhigh, starMul_re]
    · trans (∑ t : Fin (2 ^ (k * m)),
          (if (fun i => blockDigit k m i t) ∈ E then
            (starRingEnd ℂ (blockProd ψ t) * blockProd ψ t).re else 0)) *
        (∑ h : Fin (2 ^ r), (starRingEnd ℂ (χ h) * χ h).re)
      · trans ∑ h : Fin (2 ^ r),
            ((∑ t : Fin (2 ^ (k * m)),
              (if (fun i => blockDigit k m i t) ∈ E then
                (starRingEnd ℂ (blockProd ψ t) * blockProd ψ t).re else 0)) *
            (starRingEnd ℂ (χ h) * χ h).re)
        · apply Finset.sum_congr rfl
          intro h _
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl
            (fun t _ => ite_mul_zero_right _ _ _)
        · exact (Finset.mul_sum _ _ _).symm
      · have hsq : (∑ h : Fin (2 ^ r),
            (starRingEnd ℂ (χ h) * χ h).re) = sqNorm χ := rfl
        rw [eventWeight_blockProd ψ E, hsq]
        exact mul_comm _ _

/-- **Product law, output bits.** The joint law of the `k` per-block
output qubits (qubit `0` of each block) of a product state is the product
of the per-block accept/reject weights, for an arbitrary event `B` on
output-bit assignments. -/
theorem outputBitsWeight_blockProd {k m : ℕ} (ψ : Fin k → Fin (2 ^ m) → ℂ)
    (B : Finset (Fin k → Bool)) :
    (∑ s : Fin (2 ^ (k * m)),
        if (fun i => decide (qBit 0 (blockDigit k m i s).val = 1)) ∈ B then
          (starRingEnd ℂ (blockProd ψ s) * blockProd ψ s).re else 0) =
      ∑ b ∈ B, ∏ i, (if b i then acceptProb (ψ i)
                      else sqNorm (ψ i) - acceptProb (ψ i)) := by
  trans ∑ j ∈ Finset.univ.filter (fun j : Fin k → Fin (2 ^ m) =>
      (fun i => decide (qBit 0 (j i).val = 1)) ∈ B),
    ∏ i, (starRingEnd ℂ (ψ i (j i)) * ψ i (j i)).re
  · rw [← eventWeight_blockProd ψ (Finset.univ.filter
      (fun j : Fin k → Fin (2 ^ m) =>
        (fun i => decide (qBit 0 (j i).val = 1)) ∈ B))]
    apply Finset.sum_congr rfl
    intro s _
    have hmem : ((fun i => blockDigit k m i s) ∈ Finset.univ.filter
          (fun j : Fin k → Fin (2 ^ m) =>
            (fun i => decide (qBit 0 (j i).val = 1)) ∈ B))
        ↔ ((fun i => decide (qBit 0 (blockDigit k m i s).val = 1)) ∈ B) := by
      rw [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
    by_cases h : (fun i => decide (qBit 0 (blockDigit k m i s).val = 1)) ∈ B
    · rw [ite_eq_left h, ite_eq_left (hmem.mpr h)]
    · rw [ite_eq_right h, ite_eq_right (fun hh => h (hmem.mp hh))]
  · have hper : ∀ (b : Fin k → Bool) (i : Fin k),
        (if b i then acceptProb (ψ i) else sqNorm (ψ i) - acceptProb (ψ i))
        = ∑ t : Fin (2 ^ m),
          (if decide (qBit 0 t.val = 1) = b i then
            (starRingEnd ℂ (ψ i t) * ψ i t).re else 0) := by
      intro b i
      by_cases hb : b i = true
      · rw [ite_eq_left hb, hb]
        have hunfold : acceptProb (ψ i)
            = ∑ t, if qBit 0 t.val = 1 then
              (starRingEnd ℂ (ψ i t) * ψ i t).re else 0 := rfl
        rw [hunfold]
        apply Finset.sum_congr rfl
        intro t _
        by_cases ht : qBit 0 t.val = 1 <;> simp [ht]
      · rw [ite_eq_right hb]
        have hb' : b i = false := Bool.eq_false_iff.mpr hb
        rw [hb']
        have hsq : sqNorm (ψ i)
            = ∑ t, (starRingEnd ℂ (ψ i t) * ψ i t).re := rfl
        have hac : acceptProb (ψ i)
            = ∑ t, if qBit 0 t.val = 1 then
              (starRingEnd ℂ (ψ i t) * ψ i t).re else 0 := rfl
        rw [hsq, hac, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro t _
        by_cases ht : qBit 0 t.val = 1 <;> simp [ht]
    have hswap : ∀ (b : Fin k → Bool) (j : Fin k → Fin (2 ^ m)),
        (∏ i, (if decide (qBit 0 (j i).val = 1) = b i then
          (starRingEnd ℂ (ψ i (j i)) * ψ i (j i)).re else 0))
        = (if (fun i => decide (qBit 0 (j i).val = 1)) = b then
          ∏ i, (starRingEnd ℂ (ψ i (j i)) * ψ i (j i)).re else 0) := by
      intro b j
      by_cases h : (fun i => decide (qBit 0 (j i).val = 1)) = b
      · rw [ite_eq_left h]
        exact Finset.prod_congr rfl (fun i _ => ite_eq_left (congrFun h i))
      · rw [ite_eq_right h]
        have hex : ∃ i, decide (qBit 0 (j i).val = 1) ≠ b i := by
          by_contra hall
          apply h
          funext i
          by_contra hi
          exact hall ⟨i, hi⟩
        obtain ⟨i, hi⟩ := hex
        exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
    have hbit : ∀ b : Fin k → Bool,
        (∏ i, (if b i then acceptProb (ψ i) else sqNorm (ψ i) - acceptProb (ψ i)))
        = ∑ j : Fin k → Fin (2 ^ m),
          (if (fun i => decide (qBit 0 (j i).val = 1)) = b then
            ∏ i, (starRingEnd ℂ (ψ i (j i)) * ψ i (j i)).re else 0) := by
      intro b
      trans ∏ i, ∑ t : Fin (2 ^ m),
        (if decide (qBit 0 t.val = 1) = b i then
          (starRingEnd ℂ (ψ i t) * ψ i t).re else 0)
      · exact Finset.prod_congr rfl (fun i _ => hper b i)
      · rw [← Finset.sum_prod_piFinset, Fintype.piFinset_univ]
        exact Finset.sum_congr rfl (fun j _ => hswap b j)
    have hcollapse : ∀ j : Fin k → Fin (2 ^ m),
        (∑ b ∈ B, (if (fun i => decide (qBit 0 (j i).val = 1)) = b then
          ∏ i, (starRingEnd ℂ (ψ i (j i)) * ψ i (j i)).re else 0))
        = (if (fun i => decide (qBit 0 (j i).val = 1)) ∈ B then
          ∏ i, (starRingEnd ℂ (ψ i (j i)) * ψ i (j i)).re else 0) :=
      fun j => Finset.sum_ite_eq B _ _
    trans ∑ b ∈ B, ∑ j : Fin k → Fin (2 ^ m),
      (if (fun i => decide (qBit 0 (j i).val = 1)) = b then
        ∏ i, (starRingEnd ℂ (ψ i (j i)) * ψ i (j i)).re else 0)
    · rw [Finset.sum_comm]
      trans ∑ j : Fin k → Fin (2 ^ m),
        (if (fun i => decide (qBit 0 (j i).val = 1)) ∈ B then
          ∏ i, (starRingEnd ℂ (ψ i (j i)) * ψ i (j i)).re else 0)
      · exact Finset.sum_filter _ _
      · exact Finset.sum_congr rfl (fun j _ => (hcollapse j).symm)
    · exact Finset.sum_congr rfl (fun b _ => (hbit b).symm)

/-- **Threshold events on normalized blocks** have the heterogeneous
Bernoulli tail weight of the per-block acceptance probabilities. -/
theorem thresholdWeight_blockProd {k m : ℕ} (ψ : Fin k → Fin (2 ^ m) → ℂ)
    (hψ : ∀ i, sqNorm (ψ i) = 1) (T : ℝ) :
    (∑ s : Fin (2 ^ (k * m)),
        if T ≤ acceptCount
            (fun i => decide (qBit 0 (blockDigit k m i s).val = 1)) then
          (starRingEnd ℂ (blockProd ψ s) * blockProd ψ s).re else 0) =
      tailWeight (fun i => acceptProb (ψ i)) T := by
  trans ∑ s : Fin (2 ^ (k * m)),
    (if (fun i => decide (qBit 0 (blockDigit k m i s).val = 1)) ∈
        Finset.univ.filter (fun b : Fin k → Bool => T ≤ acceptCount b) then
      (starRingEnd ℂ (blockProd ψ s) * blockProd ψ s).re else 0)
  · apply Finset.sum_congr rfl
    intro s _
    have hmem : ((fun i => decide (qBit 0 (blockDigit k m i s).val = 1)) ∈
          Finset.univ.filter (fun b : Fin k → Bool => T ≤ acceptCount b))
        ↔ (T ≤ acceptCount
          (fun i => decide (qBit 0 (blockDigit k m i s).val = 1))) := by
      rw [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
    by_cases h : T ≤ acceptCount
        (fun i => decide (qBit 0 (blockDigit k m i s).val = 1))
    · rw [ite_eq_left h, ite_eq_left (hmem.mpr h)]
    · rw [ite_eq_right h, ite_eq_right (fun hh => h (hmem.mp hh))]
  · have h3 := outputBitsWeight_blockProd ψ
      (Finset.univ.filter (fun b : Fin k → Bool => T ≤ acceptCount b))
    rw [h3]
    have htw : tailWeight (fun i => acceptProb (ψ i)) T
        = ∑ b ∈ Finset.univ.filter (fun b => T ≤ acceptCount b),
          ∏ i, (if b i then acceptProb (ψ i) else 1 - acceptProb (ψ i)) := rfl
    rw [htw]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.prod_congr rfl
    intro i _
    by_cases hb : b i = true
    · simp only [ite_eq_left hb]
    · simp only [ite_eq_right hb, hψ i]

end Cslib.Complexity.Classes
