/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.DoublyExponentialReciprocalSum
import Mathlib.Order.OrderIsoNat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Eventual vanishing of rational pseudo-greedy gaps

The gaps of a positive rational pseudo-greedy expansion eventually vanish under either
the lower-bound hypothesis on the weighted gaps or eventual nonnegativity of the gaps.

Reference: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28 (arXiv:2504.05933), Proposition 1.
-/

open Filter

namespace MetaMathlibExt

private theorem remainder_positive {r : ℝ} (hr : 0 < r) (n : ℕ) :
    0 < pseudoGreedyRemainder r n := by
  induction n with
  | zero => exact hr
  | succ n ih =>
    rw [pseudoGreedyRemainder_succ, sub_pos, one_div]
    apply inv_lt_of_inv_lt₀ ih
    unfold pseudoGreedyExpansion
    linarith [Int.lt_floor_add_one ((pseudoGreedyRemainder r n)⁻¹ + 1 + 1 / 2)]

private theorem exists_integer_numerators {r : ℚ} (hr : 0 < r) :
    ∃ c : ℕ → ℤ, c 0 = r.num ∧ ∀ n, 0 < c n ∧
      pseudoGreedyGap r n * (Int.cast (c n) : ℝ) = ((c n - c (n + 1) : ℤ) : ℝ) := by
  let a := pseudoGreedyExpansion (r : ℝ)
  let d : ℕ → ℤ := fun n => r.den * ∏ k ∈ Finset.range n, a k
  let c : ℕ → ℤ := fun n => Nat.rec r.num (fun k t => t * a k - d k) n
  have hx (n) : 0 < pseudoGreedyRemainder r n := remainder_positive (by exact_mod_cast hr) n
  have ha (n) : 0 < (a n : ℝ) := by
    have hfloor := Int.lt_floor_add_one ((pseudoGreedyRemainder r n)⁻¹ + 1 + 1 / 2)
    have hinv := inv_pos.mpr (hx n)
    change 0 < (pseudoGreedyExpansion r n : ℝ)
    unfold pseudoGreedyExpansion
    linarith
  have hd (n) : 0 < (d n : ℝ) := by
    simp only [d, Int.cast_mul, Int.cast_natCast, Int.cast_prod]
    exact mul_pos (by exact_mod_cast r.den_pos) (Finset.prod_pos fun k _ => ha k)
  have hdstep (n) : d (n + 1) = d n * a n := by
    dsimp [d]
    rw [Finset.prod_range_succ]
    ring
  have hcstep (n) : c (n + 1) = c n * a n - d n := rfl
  have hrep (n : ℕ) : pseudoGreedyRemainder r n = (Int.cast (c n) : ℝ) / (d n : ℝ) := by
    induction n with
    | zero => simpa [pseudoGreedyRemainder, c, d] using Rat.cast_def r
    | succ n ih =>
      rw [pseudoGreedyRemainder_succ, ih, hcstep, hdstep]
      push_cast
      change (Int.cast (c n) : ℝ) / d n - 1 / (a n : ℝ) =
        ((Int.cast (c n) : ℝ) * a n - d n) / ((d n : ℝ) * a n)
      field_simp [(hd n).ne', (ha n).ne']
  have hc (n) : 0 < c n := by
    have hpos := hx n
    rw [hrep n] at hpos
    have hpos' := (div_pos_iff_of_pos_right (hd n)).mp hpos
    exact_mod_cast hpos'
  refine ⟨c, rfl, fun n => ⟨hc n, ?_⟩⟩
  rw [pseudoGreedyGap, hrep, hcstep, inv_div]
  change ((d n : ℝ) / (Int.cast (c n) : ℝ) + 1 - (a n : ℝ)) * (Int.cast (c n) : ℝ) =
    ((c n - (c n * a n - d n) : ℤ) : ℝ)
  push_cast
  have hcn : (Int.cast (c n) : ℝ) ≠ 0 := by exact_mod_cast (hc n).ne'
  field_simp [hcn]
  ring

/-- **Eventual vanishing of the pseudo-greedy gaps of a rational number.** Let $r$ be a positive
rational number and let $(\varepsilon_n)_{n \ge 0}$ be the gap sequence of the pseudo-greedy
expansion of $r$. Suppose that $\liminf_n \varepsilon_n \prod_{k<n} (1 - \varepsilon_k) \ge 0$,
that is, for every $\delta > 0$ we have $\varepsilon_n \prod_{k<n} (1 - \varepsilon_k) \ge -\delta$
for all sufficiently large $n$; or that $\varepsilon_n \ge 0$ for all sufficiently large $n$.
Then $\varepsilon_n = 0$ for all sufficiently large $n$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Proposition 1 (`integers-2026-A28-prop-1`). -/
public theorem eventually_pseudoGreedyGap_eq_zero {r : ℚ} (hr : 0 < r)
    (h : (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
        -δ ≤ pseudoGreedyGap r n * ∏ k ∈ Finset.range n, (1 - pseudoGreedyGap r k)) ∨
      ∀ᶠ n in atTop, 0 ≤ pseudoGreedyGap r n) :
    ∀ᶠ n in atTop, pseudoGreedyGap r n = 0 := by
  obtain ⟨c, hc0, hc⟩ := exists_integer_numerators hr
  have hp : 0 < (r.num : ℝ) := by exact_mod_cast Rat.num_pos.mpr hr
  have hprod (n) :
      (∏ k ∈ Finset.range n, (1 - pseudoGreedyGap r k)) * (r.num : ℝ) = c n := by
    induction n with
    | zero => simp [hc0]
    | succ n ih =>
      rw [Finset.prod_range_succ]
      calc
        _ = (1 - pseudoGreedyGap r n) *
            ((∏ k ∈ Finset.range n, (1 - pseudoGreedyGap r k)) * (r.num : ℝ)) := by ring
        _ = (1 - pseudoGreedyGap r n) * (c n : ℝ) := by rw [ih]
        _ = c (n + 1) := by have hgap := (hc n).2; push_cast at hgap; nlinarith
  have hmono : ∀ᶠ n in atTop, c (n + 1) ≤ c n := by
    rcases h with h | h
    · have hδ : 0 < 1 / (2 * (r.num : ℝ)) := by positivity
      filter_upwards [h _ hδ] with n hn
      have hb := mul_le_mul_of_nonneg_right hn hp.le
      have heq :
          (pseudoGreedyGap r n * ∏ k ∈ Finset.range n, (1 - pseudoGreedyGap r k)) *
            (r.num : ℝ) = ((c n - c (n + 1) : ℤ) : ℝ) := by
        rw [mul_assoc, hprod]
        exact (hc n).2
      rw [heq] at hb
      have hhalf : -(1 / (2 * (r.num : ℝ))) * (r.num : ℝ) = -(1 / 2 : ℝ) := by
        field_simp [hp.ne']
      rw [hhalf] at hb
      by_contra hlt
      have hint : c n - c (n + 1) ≤ -1 := by omega
      have hreal : ((c n - c (n + 1) : ℤ) : ℝ) ≤ -1 := by exact_mod_cast hint
      linarith
    · filter_upwards [h] with n hn
      have hcn : 0 < (c n : ℝ) := by exact_mod_cast (hc n).1
      have hb := mul_nonneg hn hcn.le
      rw [(hc n).2] at hb
      have hint : 0 ≤ c n - c (n + 1) := by exact_mod_cast hb
      omega
  obtain ⟨N, hN⟩ := eventually_atTop.mp hmono
  let f : ℕ → ℕ := fun n => (c (n + N)).toNat
  have hf : Antitone f := by
    apply antitone_nat_of_succ_le
    intro n
    apply Int.toNat_le_toNat
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hN (n + N) (by omega)
  obtain ⟨M, hM⟩ := WellFoundedLT.antitone_chain_condition hf
  refine eventually_atTop.mpr ⟨M + N, fun n hn => ?_⟩
  have h₁ := hM (n - N) (by omega)
  have h₂ := hM (n - N + 1) (by omega)
  dsimp [f] at h₁ h₂
  have hindex : n - N + N = n := by omega
  have hindex' : n - N + 1 + N = n + 1 := by omega
  rw [hindex] at h₁
  rw [hindex'] at h₂
  have hcn := (hc n).1
  have hcn' := (hc (n + 1)).1
  have heq : c n = c (n + 1) := by omega
  have hgap := (hc n).2
  rw [heq, sub_self, Int.cast_zero] at hgap
  exact (mul_eq_zero.mp hgap).resolve_right (by exact_mod_cast hcn'.ne')

end MetaMathlibExt
