/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.ContinuedFractions.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Śleszyński–Pringsheim convergence criterion

`MetaMathlibExt.contFract_tendsto_of_pringsheim` gives convergence in the closed unit disk when
each partial denominator has norm at least one plus the norm of its partial numerator.
-/

namespace MetaMathlibExt

open Filter Topology

namespace contFract_tendsto_of_pringsheim

private noncomputable def truncation (a b : ℕ → ℂ) (k n : ℕ) : ℂ :=
  GenContFract.convs'Aux (Stream'.Seq.ofStream fun j ↦ ⟨a (j + k), b (j + k)⟩) n

private theorem truncation_succ (a b : ℕ → ℂ) (k n : ℕ) :
    truncation a b k (n + 1) = a k / (b k + truncation a b (k + 1) n) := by
  change a (0 + k) / (b (0 + k) + GenContFract.convs'Aux (Stream'.Seq.ofStream fun j ↦
    ⟨a (j + 1 + k), b (j + 1 + k)⟩) n) = _
  simp [truncation, Nat.succ_add, Nat.add_assoc]

-- Replace each numerator by its norm and take the smallest possible real denominator.
private noncomputable def majorant (a : ℕ → ℂ) (k : ℕ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => ‖a k‖ / (1 + ‖a k‖ - majorant a (k + 1) n)

private theorem majorant_lt_one (a : ℕ → ℂ) (k n : ℕ) : majorant a k n < 1 := by
  induction n generalizing k with
  | zero => exact zero_lt_one
  | succ n ih =>
    have ht := ih (k + 1)
    rw [majorant, div_lt_one (by linarith [norm_nonneg (a k)])]
    linarith

private theorem denominator_bound {a b z : ℂ} {t : ℝ}
    (h : 1 + ‖a‖ ≤ ‖b‖) (hz : ‖z‖ ≤ t) : 1 + ‖a‖ - t ≤ ‖b + z‖ := by
  have ht : ‖b‖ - ‖z‖ ≤ ‖b + z‖ := by simpa using norm_sub_norm_le b (-z)
  linarith

private theorem norm_truncation_le (a b : ℕ → ℂ) (h : ∀ k, 1 + ‖a k‖ ≤ ‖b k‖) (k n : ℕ) :
    ‖truncation a b k n‖ ≤ majorant a k n := by
  induction n generalizing k with
  | zero => exact (norm_zero : ‖(0 : ℂ)‖ = 0).le
  | succ n ih =>
    rw [truncation_succ, norm_div, majorant]
    apply div_le_div_of_nonneg_left (norm_nonneg _) _ (denominator_bound (h k) (ih (k + 1)))
    linarith [majorant_lt_one a (k + 1) n, norm_nonneg (a k)]

-- The increment of the real comparison map bounds the change in the complex fraction.
private theorem step_sub_le {a b z w : ℂ} {s t : ℝ} (h : 1 + ‖a‖ ≤ ‖b‖)
    (hz : ‖z‖ ≤ s) (hw : ‖w‖ ≤ t) (hs : s < 1) (ht : t < 1) (hd : ‖w - z‖ ≤ t - s) :
    ‖a / (b + w) - a / (b + z)‖ ≤ ‖a‖ / (1 + ‖a‖ - t) - ‖a‖ / (1 + ‖a‖ - s) := by
  have hs' : 0 < 1 + ‖a‖ - s := by linarith [norm_nonneg a]
  have ht' : 0 < 1 + ‖a‖ - t := by linarith [norm_nonneg a]
  have hz' := denominator_bound h hz
  have hw' := denominator_bound h hw
  have hz₀ := norm_pos_iff.mp (hs'.trans_le hz')
  have hw₀ := norm_pos_iff.mp (ht'.trans_le hw')
  calc
    _ = ‖a‖ * ‖w - z‖ / (‖b + w‖ * ‖b + z‖) := by
      rw [div_sub_div _ _ hw₀ hz₀, mul_comm (b + w) a, ← mul_sub, add_sub_add_left_eq_sub,
        norm_div, norm_mul, norm_mul, norm_sub_rev z w]
    _ ≤ ‖a‖ * (t - s) / ((1 + ‖a‖ - t) * (1 + ‖a‖ - s)) := by
      refine div_le_div₀ ?_ (mul_le_mul_of_nonneg_left hd (norm_nonneg _)) (mul_pos ht' hs') ?_
      · exact mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans hd)
      · exact mul_le_mul hw' hz' hs'.le (norm_nonneg _)
    _ = _ := by
      rw [div_sub_div _ _ ht'.ne' hs'.ne']
      ring

private theorem truncation_sub_le (a b : ℕ → ℂ) (h : ∀ k, 1 + ‖a k‖ ≤ ‖b k‖)
    (k n m : ℕ) (hnm : n ≤ m) :
    ‖truncation a b k m - truncation a b k n‖ ≤ majorant a k m - majorant a k n := by
  induction n generalizing k m with
  | zero =>
    simpa only [show truncation a b k 0 = 0 from rfl, majorant, sub_zero] using
      norm_truncation_le a b h k m
  | succ n ih =>
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    rw [truncation_succ, truncation_succ, majorant, majorant]
    exact step_sub_le (h k) (norm_truncation_le a b h _ _) (norm_truncation_le a b h _ _)
      (majorant_lt_one a _ _) (majorant_lt_one a _ _) (ih (k + 1) m (by omega))

end contFract_tendsto_of_pringsheim

open contFract_tendsto_of_pringsheim

/-- **Śleszyński–Pringsheim convergence criterion.** Let $a_0, a_1, a_2, \dots$ and
$b_0, b_1, b_2, \dots$ be complex numbers with $1 + |a_k| \le |b_k|$ for every $k$. For $n \ge 0$
let $f_n$ be the $n$-th approximant of the continued fraction $a_0 / (b_0 + a_1 / (b_1 + \cdots))$,
that is $f_0 = 0$ and $f_n = a_0 / (b_0 + a_1 / (b_1 + \cdots + a_{n-1} / b_{n-1}))$ for $n \ge 1$.
Then there is a complex number $v$ with $|v| \le 1$ such that $f_n \to v$ as $n \to \infty$.

Zero partial numerators are admitted.

Source: Carminda M. Mennen, *Möbius Maps and Continued Fractions*, INTEGERS 24 (2024),
Article A52, Theorem 1 (`integers-2024-A52-thm-1`). -/
public theorem contFract_tendsto_of_pringsheim (a b : ℕ → ℂ)
    (h : ∀ k, 1 + ‖a k‖ ≤ ‖b k‖) :
    ∃ v : ℂ, ‖v‖ ≤ 1 ∧
      Tendsto
        (fun n ↦ (⟨0, Stream'.Seq.ofStream fun k ↦ ⟨a k, b k⟩⟩ : GenContFract ℂ).convs' n)
        atTop (𝓝 v) := by
  have hmono : Monotone (majorant a 0) := by
    intro n m hnm
    exact sub_nonneg.mp ((norm_nonneg _).trans (truncation_sub_le a b h 0 n m hnm))
  have hbdd : BddAbove (Set.range (majorant a 0)) := by
    exact ⟨1, Set.forall_mem_range.mpr fun n ↦ (majorant_lt_one a 0 n).le⟩
  have hreal := (tendsto_atTop_ciSup hmono hbdd).cauchySeq
  have hc : CauchySeq (truncation a b 0) := by
    apply Metric.cauchySeq_iff'.2
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hreal ε hε
    refine ⟨N, fun m hm ↦ ?_⟩
    rw [dist_eq_norm]
    apply (truncation_sub_le a b h 0 N m hm).trans_lt
    simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hmono hm))] using hN m hm
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨v, le_of_tendsto' hv.norm (fun n ↦ ?_), ?_⟩
  · exact (norm_truncation_le a b h 0 n).trans (majorant_lt_one a 0 n).le
  · exact hv.congr fun n ↦ (zero_add (truncation a b 0 n)).symm

end MetaMathlibExt
