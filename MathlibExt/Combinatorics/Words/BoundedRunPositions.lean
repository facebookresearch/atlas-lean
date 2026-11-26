/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Words.RelativePositionBinaryWords
import Mathlib.Tactic.Linarith

/-!
# Position bounds for binary words with bounded runs

`letterPosition_le_of_run_le` bounds the positions of the two letters and their signed
difference in a word starting with the first letter.
-/

namespace MetaMathlibExt

/-- **Bounds on position functions for words with bounded runs.** Let $w$ be an infinite binary
word over $\{a, b\}$ that starts with $a$ and in which both letters occur infinitely often, and
let $c \ge 0$ be an integer such that every block of consecutive equal letters of $w$ has length
at most $c$. Write $p_\alpha(n)$ for the position (counted from $0$) of the $n$-th occurrence of
the letter $\alpha$ in $w$, and $r(n) = p_b(n) - p_a(n)$. Then for every $n \ge 1$,
$p_a(n) \le (c+1)(n-1)$, $p_b(n) \le (c+1)n - 1$ and $c(1-n) + 1 \le r(n) \le cn$.

The paper prints the lower bound $(1-c)n + 1 \le r(n)$, which is false: for $w = (abb)^\omega$
and $c = 2$, $r(4) = 5 - 9 = -4 < -3$. The bound $c(1-n) + 1$ is the one derived in the paper's
proof. Stating the result for every bound $c$ of the runs is equivalent to stating it for the
longest run.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 25
(`jis-2025-25.1.5-lem-25`). -/
public theorem letterPosition_le_of_run_le {w : ℕ → Bool} (hw : BothLettersInfinite w)
    (h₀ : w 0 = true) {c : ℕ} (hc : ∀ i k, (∀ j < k, w (i + j) = w i) → k ≤ c) (n : ℕ)
    (hn : 1 ≤ n) :
    (letterPosition w true n : ℤ) ≤ (c + 1) * (n - 1) ∧
      (letterPosition w false n : ℤ) ≤ (c + 1) * n - 1 ∧
      (c : ℤ) * (1 - n) + 1 ≤ relativePosition w n ∧ relativePosition w n ≤ c * n := by
  let pos (α : Bool) := Nat.nth (fun i => w i = α)
  have inf (α : Bool) : {i | w i = α}.Infinite := by
    cases α
    · exact hw.2
    · exact hw.1
  -- A block of length c + 1 cannot consist solely of the opposite letter.
  have window (i : ℕ) (α : Bool) : ∃ j ≤ c, w (i + j) = α := by
    by_contra! h
    have opposite (j : ℕ) (hj : j ≤ c) : w (i + j) = !α := Bool.eq_not_iff.mpr (h j hj)
    have first : w i = !α := by simpa using opposite 0 (Nat.zero_le c)
    have := hc i (c + 1) fun j hj => (opposite j (by omega)).trans first.symm
    omega
  have gap (α : Bool) (k : ℕ) : pos α (k + 1) ≤ pos α k + (c + 1) := by
    obtain ⟨j, hj, h⟩ := window (pos α k + 1) α
    calc
      pos α (k + 1) ≤ pos α k + 1 + j :=
        (Nat.nth_add_one_le_iff (inf α) h).2 (by change pos α k < _; omega)
      _ ≤ pos α k + (c + 1) := by omega
  have bounds (α : Bool) (k : ℕ) :
      pos α 0 + k ≤ pos α k ∧ pos α k ≤ pos α 0 + (c + 1) * k := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hlt : pos α k < pos α (k + 1) := Nat.nth_strictMono (inf α) (Nat.lt_succ_self k)
      have hle := gap α k
      rw [Nat.mul_succ]
      omega
  have a₀ : pos true 0 = 0 := Nat.nth_zero_of_zero (p := fun i => w i = true) h₀
  have b₀ : 0 < pos false 0 := by
    have h : w (pos false 0) = false := Nat.nth_mem_of_infinite (inf false) 0
    exact Nat.pos_of_ne_zero fun hz => by simp [hz, h₀] at h
  have b₀_le : pos false 0 ≤ c := by
    obtain ⟨j, hj, h⟩ := window 0 false
    rw [Nat.zero_add] at h
    exact (Nat.nth_zero (p := fun i => w i = false) ▸ Nat.sInf_le h).trans hj
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨ha_lower, ha_upper⟩ := bounds true k
  obtain ⟨hb_lower, hb_upper⟩ := bounds false k
  simp only [a₀, Nat.zero_add] at ha_lower ha_upper
  simp only [relativePosition, letterPosition, Nat.succ_sub_one, Nat.cast_succ]
  change (pos true k : ℤ) ≤ _ ∧ (pos false k : ℤ) ≤ _ ∧
    _ ≤ (pos false k : ℤ) - pos true k ∧ (pos false k : ℤ) - pos true k ≤ _
  zify at ha_lower ha_upper hb_lower hb_upper b₀ b₀_le
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- **Linear bounds for words with bounded runs.** Let $w$ be an infinite binary word over the
letters $a$ and $b$ in which both letters occur infinitely often, and let $c$ be a natural number
such that every block of consecutive equal letters of $w$ has length at most $c$. Let $p_a(n)$
and $p_b(n)$ be the positions (counting from $0$) of the $n$-th $a$ and the $n$-th $b$ in $w$, and
let $r(n) = p_b(n) - p_a(n)$. Then for every $n \ge 1$, $p_a(n) \le (c+1)n - 1$,
$p_b(n) \le (c+1)n - 1$ and $-cn \le r(n) \le cn$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Corollary 27
(`jis-2025-25.1.5-cor-27`). -/
public theorem letterPosition_le_of_run_le' {w : ℕ → Bool} (hw : BothLettersInfinite w)
    {c : ℕ} (hc : ∀ i k, (∀ j < k, w (i + j) = w i) → k ≤ c) (n : ℕ) (hn : 1 ≤ n) :
    (letterPosition w true n : ℤ) ≤ (c + 1) * n - 1 ∧
      (letterPosition w false n : ℤ) ≤ (c + 1) * n - 1 ∧
      -((c : ℤ) * n) ≤ relativePosition w n ∧ relativePosition w n ≤ c * n := by
  have hc₀ : 0 ≤ (c : ℤ) := Int.natCast_nonneg c
  cases h₀ : w 0 with
  | true =>
    obtain ⟨ha, hb, hlo, hhi⟩ := letterPosition_le_of_run_le hw h₀ hc n hn
    exact ⟨by linarith, hb, by linarith, hhi⟩
  | false =>
    -- Complementing the word swaps the position functions and preserves the run bound.
    let v (i : ℕ) := !(w i)
    have hv : BothLettersInfinite v := ⟨by simpa [v] using hw.2, by simpa [v] using hw.1⟩
    have hv₀ : v 0 = true := by simp [v, h₀]
    have hbnd : ∀ i k, (∀ j < k, v (i + j) = v i) → k ≤ c := by
      intro i k h
      refine hc i k fun j hj => ?_
      have he := congrArg Bool.not (h j hj)
      simpa only [v, Bool.not_not] using he
    have hpos (b : Bool) : letterPosition v b n = letterPosition w (!b) n := by
      have hp : (fun i => v i = b) = (fun i => w i = !b) := by
        funext i
        apply propext
        cases b <;> simp [v]
      simp only [letterPosition, hp]
    obtain ⟨ha, hb, hlo, hhi⟩ := letterPosition_le_of_run_le hv hv₀ hbnd n hn
    simp only [relativePosition, hpos, Bool.not_true, Bool.not_false] at ha hb hlo hhi
    unfold relativePosition
    exact ⟨hb, by linarith, by linarith, by linarith⟩

end MetaMathlibExt
