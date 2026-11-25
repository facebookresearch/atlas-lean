/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Digits.Defs

/-!
# Sums of Fibternary and Tribternary numbers

Following Chen et al., we distribute each ternary digit between two available summands.
For four summands the available pairs alternate. For three summands the one forced to
take a zero rotates. This bounds the length of each summand's runs of ones.
-/

namespace MetaMathlibExt

namespace exists_fibternary_sum_four_and_tribternary_sum_three

/-- All ternary digits are bits. Runs of ones have length at most `k`, and the initial run
(at the units end) has length at most `r`. -/
private def Bounded (k r x : ℕ) : Prop :=
  ((∀ e ∈ Nat.digits 3 x, e ≤ 1) ∧ ¬ List.replicate (k + 1) 1 <:+: Nat.digits 3 x) ∧
    ∀ m, r < m → ¬ List.replicate m 1 <+: Nat.digits 3 x

private theorem bounded_zero (k r : ℕ) : Bounded k r 0 := by
  simp [Bounded]
  omega

/-- A new units digit can be one only if extending the initial run respects both bounds. -/
private theorem bounded_digit {k r s x d : ℕ} (hx : Bounded k r x) (hd : d ≤ 1)
    (hroom : d = 1 → r < k ∧ r < s) : Bounded k s (d + 3 * x) := by
  by_cases h : d = 0 ∧ x = 0
  · simp [h.1, h.2, bounded_zero]
  obtain ⟨⟨hdigits, hrun⟩, hprefix⟩ := hx
  unfold Bounded
  rw [Nat.digits_add 3 (by decide) d x (by omega) (by omega)]
  refine ⟨⟨by simpa using And.intro hd hdigits, ?_⟩, ?_⟩
  · rw [List.infix_cons_iff]
    rintro (hp | hi)
    · rw [List.replicate_succ, List.cons_prefix_cons] at hp
      exact hprefix k (hroom hp.1.symm).1 hp.2
    · exact hrun hi
  · rintro (_ | m) hm hp
    · omega
    · rw [List.replicate_succ, List.cons_prefix_cons] at hp
      exact hprefix m ((hroom hp.1.symm).2.trans_le (Nat.le_of_lt_succ hm)) hp.2

private theorem bounded_shift {k r x : ℕ} (hx : Bounded k r x) : Bounded k 0 (3 * x) := by
  simpa using bounded_digit (s := 0) (d := 0) hx (by decide) (by simp)

private theorem bounded_extend {k r x d : ℕ} (hx : Bounded k r x) (hd : d ≤ 1) (hr : r < k) :
    Bounded k (r + 1) (d + 3 * x) :=
  bounded_digit hx hd (fun _ => ⟨hr, Nat.lt_succ_self _⟩)

/-- The prefix bounds record which summands can receive the next two units. -/
private theorem decompositions (n : ℕ) :
    (∃ a b c d, Bounded 1 0 a ∧ Bounded 1 0 b ∧ Bounded 1 1 c ∧ Bounded 1 1 d ∧
      n = a + b + c + d) ∧
    (∃ a b c, Bounded 2 0 a ∧ Bounded 2 1 b ∧ Bounded 2 2 c ∧ n = a + b + c) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨⟨0, 0, 0, 0, bounded_zero .., bounded_zero .., bounded_zero .., bounded_zero .., rfl⟩,
        ⟨0, 0, 0, bounded_zero .., bounded_zero .., bounded_zero .., rfl⟩⟩
    obtain ⟨⟨a, b, c, d, ha, hb, hc, hd, hf⟩, ⟨x, y, z, hx, hy, hz, ht⟩⟩ :=
      ih (n / 3) (Nat.div_lt_self hn (by decide))
    -- Split the units digit into two bits, whose sum needs no carry.
    let u := min (n % 3) 1
    let v := n % 3 - u
    have hu : u ≤ 1 := Nat.min_le_right ..
    have hv : v ≤ 1 := by dsimp [v, u]; omega
    have huv : u + v = n % 3 := by dsimp [v, u]; omega
    constructor
    · exact ⟨3 * c, 3 * d, u + 3 * a, v + 3 * b, bounded_shift hc, bounded_shift hd,
        bounded_extend ha hu (by decide), bounded_extend hb hv (by decide), by omega⟩
    · exact ⟨3 * z, u + 3 * x, v + 3 * y, bounded_shift hz,
        bounded_extend hx hu (by decide), bounded_extend hy hv (by decide), by omega⟩

end exists_fibternary_sum_four_and_tribternary_sum_three

/-- **Sums of Fibternary and Tribternary numbers.** Call a natural number Fibternary if its
base-$3$ digits are all $0$ or $1$ with no two consecutive $1$s, and Tribternary if its
base-$3$ digits are all $0$ or $1$ with no three consecutive $1$s. Every natural number is a
sum of four Fibternary numbers and also a sum of three Tribternary numbers (the summands
may be $0$ and need not be distinct).

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Proposition 21 (`jis-2025-25.5.4-prop-21`). -/
public theorem exists_fibternary_sum_four_and_tribternary_sum_three (n : ℕ) :
    (∃ a b c d : ℕ, (∀ x ∈ [a, b, c, d],
        (∀ e ∈ Nat.digits 3 x, e ≤ 1) ∧ ¬ [1, 1] <:+: Nat.digits 3 x) ∧ n = a + b + c + d) ∧
      ∃ a b c : ℕ, (∀ x ∈ [a, b, c],
        (∀ e ∈ Nat.digits 3 x, e ≤ 1) ∧ ¬ [1, 1, 1] <:+: Nat.digits 3 x) ∧ n = a + b + c := by
  obtain ⟨⟨a, b, c, d, ha, hb, hc, hd, hf⟩, ⟨x, y, z, hx, hy, hz, ht⟩⟩ :=
    exists_fibternary_sum_four_and_tribternary_sum_three.decompositions n
  constructor
  · refine ⟨a, b, c, d, ?_, hf⟩
    simpa using And.intro ha.1 ⟨hb.1, hc.1, hd.1⟩
  · refine ⟨x, y, z, ?_, ht⟩
    simpa using And.intro hx.1 ⟨hy.1, hz.1⟩

end MetaMathlibExt
