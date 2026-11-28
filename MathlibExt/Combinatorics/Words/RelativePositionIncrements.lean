/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import MathlibExt.Combinatorics.Words.RelativePositionBinaryWords

import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int

/-!
# Relative position increments in binary words

Without long runs of `b`, the relative position increments differ from the gaps between
successive occurrences of `b` by a bounded amount.
-/

namespace MetaMathlibExt

-- The initial letter is part of the source statement, but is not needed for these gaps.
set_option linter.unusedVariables false in
/-- **Relative position increments without long runs of b.** Let $w = \ell_0 \ell_1 \ell_2 \cdots$
be an infinite word over the letters $a$ and $b$ in which both letters occur infinitely often and
whose first letter $\ell_0$ is $a$. Let $p_b$ be its position function for the letter $b$, let $r$
be its relative position function, and write $\Delta s(n) = s(n+1) - s(n)$. Let $k$ be a natural
number such that $w$ contains no $k$ consecutive letters $b$, that is, there is no $i$ with
$\ell_{i+j} = b$ for all $j < k$. Then $|\Delta r(n) - \Delta p_b(n)| \le k$ for every $n \ge 1$.
Moreover, $|\Delta r(n)|$ is bounded over $n \ge 1$ if and only if $\Delta p_b(n)$ is bounded over
$n \ge 1$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 15
(`jis-2025-25.1.5-lem-15`). -/
public theorem abs_relativePosition_diff_sub_le {w : ℕ → Bool}
    (hw : BothLettersInfinite w) (h₀ : w 0 = true) {k : ℕ}
    (hk : ¬ ∃ i, ∀ j < k, w (i + j) = false) :
    (∀ n, 1 ≤ n → |(relativePosition w (n + 1) - relativePosition w n) -
        ((letterPosition w false (n + 1) : ℤ) - letterPosition w false n)| ≤ k) ∧
      ((∃ C : ℤ, ∀ n, 1 ≤ n → |relativePosition w (n + 1) - relativePosition w n| ≤ C) ↔
        ∃ C : ℕ, ∀ n, 1 ≤ n → letterPosition w false (n + 1) - letterPosition w false n ≤ C) := by
  have position_mono {α : Bool} (hα : {i | w i = α}.Infinite) (n : ℕ) :
      letterPosition w α n ≤ letterPosition w α (n + 1) :=
    (Nat.nth_strictMono hα).monotone (by omega)
  -- This also handles k = 0: the empty window already satisfies the forbidden-run predicate.
  have window (i : ℕ) : ∃ j < k, w (i + j) = true := by
    by_contra! h
    exact hk ⟨i, fun j hj => Bool.eq_false_of_ne_true (h j hj)⟩
  have gap (n : ℕ) (hn : 1 ≤ n) :
      letterPosition w true (n + 1) ≤ letterPosition w true n + k := by
    obtain ⟨j, hj, htrue⟩ := window (letterPosition w true n + 1)
    have hnext : letterPosition w true (n + 1) ≤ letterPosition w true n + 1 + j := by
      have hlt : letterPosition w true n < letterPosition w true n + 1 + j := by omega
      simpa only [letterPosition, Nat.add_sub_cancel, show n - 1 + 1 = n by omega] using
        (Nat.nth_add_one_le_iff hw.1 (n := n - 1) htrue).mpr hlt
    omega
  let dr (n : ℕ) := relativePosition w (n + 1) - relativePosition w n
  let db (n : ℕ) := (letterPosition w false (n + 1) : ℤ) - letterPosition w false n
  have hdiff (n : ℕ) (hn : 1 ≤ n) : |dr n - db n| ≤ (k : ℤ) := by
    have hgap := gap n hn
    have heq : db n - dr n = (letterPosition w true (n + 1) : ℤ) - letterPosition w true n := by
      dsimp [db, dr, relativePosition]
      omega
    have hle := Int.ofNat_le.mpr (position_mono hw.1 n)
    rw [abs_sub_comm, heq, abs_of_nonneg (sub_nonneg.mpr hle)]
    omega
  have abs_db (n : ℕ) :
      |db n| = ((letterPosition w false (n + 1) - letterPosition w false n : ℕ) : ℤ) := by
    rw [show db n = _ from (Int.ofNat_sub (position_mono hw.2 n)).symm,
      abs_of_nonneg (Int.natCast_nonneg _)]
  refine ⟨hdiff, ⟨?_, ?_⟩⟩
  · rintro ⟨C, hC⟩
    refine ⟨((k : ℤ) + C).toNat, fun n hn => ?_⟩
    have hb : |db n| ≤ (k : ℤ) + C := calc
      |db n| ≤ |db n - dr n| + |dr n| := by
        simpa only [sub_zero] using abs_sub_le (db n) (dr n) 0
      _ ≤ (k : ℤ) + C :=
        Int.add_le_add (abs_sub_comm (dr n) (db n) ▸ hdiff n hn) (hC n hn)
    rw [abs_db] at hb
    simpa only [Int.toNat_natCast] using Int.toNat_le_toNat hb
  · rintro ⟨C, hC⟩
    refine ⟨(k : ℤ) + C, fun n hn => ?_⟩
    have hb : |db n| ≤ (C : ℤ) := abs_db n ▸ Int.ofNat_le.mpr (hC n hn)
    calc
      |dr n| ≤ |dr n - db n| + |db n| := by
        simpa only [sub_zero] using abs_sub_le (dr n) (db n) 0
      _ ≤ (k : ℤ) + C := Int.add_le_add (hdiff n hn) hb

end MetaMathlibExt
