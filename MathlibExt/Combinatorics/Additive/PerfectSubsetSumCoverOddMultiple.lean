/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Ring.Periodic
public import MathlibExt.Combinatorics.Additive.PerfectSubsetSumCover

/-!
# Odd-multiple replacement in perfect subset-sum covers

Replacing the first entry of a perfect cover by an odd multiple preserves the cover.
-/

namespace MetaMathlibExt

open PerfectSubsetSumCover

/-- **Replacing an entry of a perfect $2^k$-cover by an odd multiple.** Let $G$ be an abelian
group, let $k$ and $N$ be natural numbers, and let $a, b, s_1, \dots, s_N \in G$. If the family
$(a, s_1, \dots, s_N)$ is a perfect $2^k$-cover of $G$ and $b = (2j + 1)a$ for some integer $j$,
then the family $(b, s_1, \dots, s_N)$ is also a perfect $2^k$-cover of $G$.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 11
(`jis-2025-25.7.8-lem-11`). The paper's `|G| = 2^n` and length `n + k` are not needed. -/
public theorem isPerfectMCover_cons_oddMultiple {G : Type*} [AddCommGroup G]
    [DecidableEq G] {k N : ℕ} {a b : G} {s : Fin N → G}
    (hs : IsPerfectMCover (2 ^ k) (Fin.cons a s : Fin (N + 1) → G))
    (hab : ∃ j : ℤ, b = (2 * j + 1) • a) :
    IsPerfectMCover (2 ^ k) (Fin.cons b s : Fin (N + 1) → G) := by
  obtain ⟨j, rfl⟩ := hab
  have hstep (x : G) : coverCount s (x + a) + coverCount s x = 2 ^ k := by
    simpa only [coverCount_cons, add_sub_cancel_right] using hs (x + a)
  -- Full counts at successive arguments agree, so their common tail count cancels.
  have hperiod : Function.Periodic (coverCount s) ((2 : ℤ) • a) := by
    intro x
    rw [two_zsmul, ← add_assoc]
    exact Nat.add_right_cancel (calc
      coverCount s (x + a + a) + coverCount s (x + a) = 2 ^ k := hstep (x + a)
      _ = coverCount s (x + a) + coverCount s x := (hstep x).symm
      _ = coverCount s x + coverCount s (x + a) := Nat.add_comm ..)
  intro g
  have hshift : coverCount s (g - a - (2 * j) • a) = coverCount s (g - a) := by
    simpa only [mul_comm (2 : ℤ) j, mul_zsmul] using hperiod.sub_zsmul_eq (x := g - a) j
  rw [coverCount_cons, add_zsmul, one_zsmul, sub_add_eq_sub_sub, sub_right_comm, hshift,
    ← coverCount_cons]
  exact hs g

end MetaMathlibExt
