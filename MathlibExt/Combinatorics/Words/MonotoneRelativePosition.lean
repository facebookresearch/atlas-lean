/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Words.AntitoneRelativePosition

/-!
# Non-decreasing relative positions in binary words

Every positive, non-decreasing sequence of natural numbers from index one onward is realized
as the relative positions of a binary word starting with `a`.
-/

namespace MetaMathlibExt

/-- **Non-decreasing functions as relative position functions.** Let $r$ be a function from the
natural numbers to the natural numbers with $r(n) \ge 1$ and $r(n) \le r(n+1)$ for every
$n \ge 1$. Then there is an infinite word $w$ over the letters $a$ and $b$ that starts with $a$,
in which both letters occur infinitely often, and whose relative position function satisfies
$r_w(n) = r(n)$ for every $n \ge 1$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 8
(`jis-2025-25.1.5-lem-8`). -/
public theorem exists_word_relativePosition_eq_of_monotone (r : ℕ → ℕ)
    (hpos : ∀ n, 1 ≤ n → 1 ≤ r n) (hmono : ∀ n, 1 ≤ n → r n ≤ r (n + 1)) :
    ∃ w, BothLettersInfinite w ∧ w 0 = true ∧ ∀ n, 1 ≤ n → relativePosition w n = r n := by
  obtain ⟨w, hw, hzero, hrel⟩ := exists_word_relativePosition_eq_of_antitone
    (fun n => -(r n : ℤ)) (by have := hpos 1 le_rfl; omega)
    (fun n hn => Int.neg_le_neg (Int.ofNat_le.mpr (hmono n hn)))
  -- Swapping the two letters preserves their multiplicities and reverses the gap.
  have position (α : Bool) (n : ℕ) :
      letterPosition (fun i => !w i) α n = letterPosition w (!α) n := by
    cases α <;> simp [letterPosition]
  refine ⟨fun i => !w i, ?_, by simp [hzero], ?_⟩
  · simpa only [BothLettersInfinite, Bool.not_eq_true', Bool.not_eq_false'] using
      And.intro hw.2 hw.1
  · intro n hn
    calc
      relativePosition (fun i => !w i) n = -relativePosition w n := by
        simp only [relativePosition, position, Bool.not_false, Bool.not_true, neg_sub]
      _ = (r n : ℤ) := by rw [hrel n hn, neg_neg]

end MetaMathlibExt
