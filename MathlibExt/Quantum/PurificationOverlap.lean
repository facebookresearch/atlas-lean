/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.ClassicalFuchsVanDeGraaf
public import Mathlib.Analysis.Complex.Basic

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.RCLike.Basic

/-!
# Purification overlap and the Bhattacharyya coefficient

Let `A, B : X → E → ℂ` be the amplitudes of two vectors `∑ x e, A x e |x⟩|e⟩` and
`∑ x e, B x e |x⟩|e⟩` on a finite system `X` and a finite environment `E`, with row weights
`p x = ∑ e, |A x e|²` and `q x = ∑ e, |B x e|²`. Purifications of the diagonal states `diag p`
and `diag q` with environment `E` have these row weights. The overlap
`|∑ x e, conj (A x e) * B x e|` is at most the Bhattacharyya coefficient
`bhattacharyyaCoeff p q = ∑ x, √(p x * q x)`, and the canonical purifications
`∑ x, √(p x) |x⟩|x⟩` and `∑ x, √(q x) |x⟩|x⟩` attain it.

The fidelity of two diagonal states is the Bhattacharyya coefficient of their diagonals
(Nielsen and Chuang, Chapter 9), so these results are the diagonal case of Uhlmann's theorem.
That identification with Physlib's `MState.fidelity`, and Uhlmann's theorem for general mixed
states, are not proved here.

## Main results

* `purification_overlap_le`: the overlap is at most `bhattacharyyaCoeff p q`.
* `exists_purification_overlap_eq`: the canonical purifications satisfy the hypotheses of
  `purification_overlap_le`, have orthogonal rows, and attain the bound.

## References

* M. A. Nielsen and I. L. Chuang, *Quantum Computation and Quantum Information*, Cambridge
  University Press (2000), Chapter 9.
-/

@[expose] public section

namespace MathlibExt.Quantum.PurificationOverlap

open MathlibExt.Quantum.ClassicalFuchsVanDeGraaf

/-- **Purification overlap bound.** If the rows of the amplitude arrays `A` and `B` have squared
norms `p` and `q`, as they do for purifications of the diagonal states `diag p` and `diag q`
with a common environment `E`, then the overlap `|∑ x e, conj (A x e) * B x e|` is at most the
Bhattacharyya coefficient of `p` and `q`. -/
theorem purification_overlap_le {X E : Type*} [Fintype X] [Fintype E]
    (A B : X → E → ℂ) (p q : X → ℝ)
    (hp : ∀ x, ∑ e, Complex.normSq (A x e) = p x)
    (hq : ∀ x, ∑ e, Complex.normSq (B x e) = q x) :
    ‖∑ x, ∑ e, (starRingEnd ℂ) (A x e) * B x e‖ ≤ bhattacharyyaCoeff p q := by
  have key : ∀ x, ‖∑ e, (starRingEnd ℂ) (A x e) * B x e‖ ≤ Real.sqrt (p x * q x) := by
    intro x
    have htri : ‖∑ e, (starRingEnd ℂ) (A x e) * B x e‖ ≤ ∑ e, ‖A x e‖ * ‖B x e‖ :=
      (norm_sum_le _ _).trans_eq
        (Finset.sum_congr rfl fun e _ => by rw [norm_mul, RCLike.norm_conj])
    have hA : ∑ e, ‖A x e‖ ^ 2 = p x := by
      rw [← hp x]
      exact Finset.sum_congr rfl fun e _ => (Complex.normSq_eq_norm_sq (A x e)).symm
    have hB : ∑ e, ‖B x e‖ ^ 2 = q x := by
      rw [← hq x]
      exact Finset.sum_congr rfl fun e _ => (Complex.normSq_eq_norm_sq (B x e)).symm
    have hcs : (∑ e, ‖A x e‖ * ‖B x e‖) ^ 2 ≤ p x * q x := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun e => ‖A x e‖) (fun e => ‖B x e‖)
      rwa [hA, hB] at h
    have hnonneg : 0 ≤ ∑ e, ‖A x e‖ * ‖B x e‖ :=
      Finset.sum_nonneg fun e _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    calc ‖∑ e, (starRingEnd ℂ) (A x e) * B x e‖
        ≤ ∑ e, ‖A x e‖ * ‖B x e‖ := htri
      _ = Real.sqrt ((∑ e, ‖A x e‖ * ‖B x e‖) ^ 2) := (Real.sqrt_sq hnonneg).symm
      _ ≤ Real.sqrt (p x * q x) := Real.sqrt_le_sqrt hcs
  calc ‖∑ x, ∑ e, (starRingEnd ℂ) (A x e) * B x e‖
      ≤ ∑ x, ‖∑ e, (starRingEnd ℂ) (A x e) * B x e‖ := norm_sum_le _ _
    _ ≤ ∑ x, Real.sqrt (p x * q x) := Finset.sum_le_sum fun x _ => key x
    _ = bhattacharyyaCoeff p q := rfl

/-- Amplitudes of the canonical purification `∑ x, √(r x) |x⟩|x⟩`. -/
private noncomputable def canonical {X : Type*} [DecidableEq X] (r : X → ℝ) (x e : X) : ℂ :=
  if x = e then (Real.sqrt (r x) : ℂ) else 0

/-- **The purification overlap bound is attained.** The canonical purifications
`∑ x, √(p x) |x⟩|x⟩` and `∑ x, √(q x) |x⟩|x⟩` of the diagonal states `diag p` and `diag q`,
whose environment is a copy of the system, satisfy the hypotheses of `purification_overlap_le`,
have pairwise orthogonal rows (so their reduced states are exactly `diag p` and `diag q`), and
have overlap of norm exactly `bhattacharyyaCoeff p q`. -/
theorem exists_purification_overlap_eq {X : Type*} [Fintype X] (p q : X → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) :
    ∃ A B : X → X → ℂ,
      (∀ x, ∑ e, Complex.normSq (A x e) = p x) ∧
      (∀ x, ∑ e, Complex.normSq (B x e) = q x) ∧
      (∀ x y, x ≠ y → ∑ e, A x e * (starRingEnd ℂ) (A y e) = 0) ∧
      (∀ x y, x ≠ y → ∑ e, B x e * (starRingEnd ℂ) (B y e) = 0) ∧
      ‖∑ x, ∑ e, (starRingEnd ℂ) (A x e) * B x e‖ = bhattacharyyaCoeff p q := by
  classical
  have rowNorm : ∀ r : X → ℝ, (∀ x, 0 ≤ r x) →
      ∀ x, ∑ e, Complex.normSq (canonical r x e) = r x := by
    intro r hr x
    rw [Finset.sum_eq_single x (fun e _ hex => by simp [canonical, Ne.symm hex])
      (fun h => absurd (Finset.mem_univ x) h)]
    simp [canonical, Complex.normSq_ofReal, Real.mul_self_sqrt (hr x)]
  have orth : ∀ r : X → ℝ, ∀ x y, x ≠ y →
      ∑ e, canonical r x e * (starRingEnd ℂ) (canonical r y e) = 0 := by
    intro r x y hxy
    refine Finset.sum_eq_zero fun e _ => ?_
    by_cases hxe : x = e
    · subst hxe
      simp [canonical, Ne.symm hxy]
    · simp [canonical, hxe]
  refine ⟨canonical p, canonical q, rowNorm p hp0, rowNorm q hq0, orth p, orth q, ?_⟩
  have hsum : ∑ x, ∑ e, (starRingEnd ℂ) (canonical p x e) * canonical q x e
      = ((bhattacharyyaCoeff p q : ℝ) : ℂ) := by
    rw [bhattacharyyaCoeff, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single x (fun e _ hex => by simp [canonical, Ne.symm hex])
      (fun h => absurd (Finset.mem_univ x) h)]
    simp [canonical, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Real.sqrt_mul (hp0 x)]
  have hB0 : 0 ≤ bhattacharyyaCoeff p q :=
    Finset.sum_nonneg fun x _ => Real.sqrt_nonneg _
  rw [hsum, Complex.norm_real, Real.norm_of_nonneg hB0]

end MathlibExt.Quantum.PurificationOverlap

end
