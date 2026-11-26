/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Ring.Periodic
public import MathlibExt.Combinatorics.Additive.PerfectSubsetSumCover

/-!
# Odd-multiple replacement in perfect subset-sum covers

Replacing the first entry of a perfect cover by an odd multiple preserves the cover.
-/

namespace MetaMathlibExt

open PerfectSubsetSumCover

private theorem coverCount_cons {G : Type*} [AddCommGroup G] [DecidableEq G]
    {N : ℕ} (s : Fin N → G) (a g : G) :
    coverCount (Fin.cons a s) g = coverCount s g + coverCount s (g - a) := by
  let e := Fin.succEmb N
  have hzero (I : Finset (Fin N)) : (0 : Fin (N + 1)) ∉ I.map e := by simp [e]
  have huniv : (Finset.univ : Finset (Fin (N + 1))) = insert 0 (Finset.univ.map e) := by
    rw [Fin.univ_succ, Finset.cons_eq_insert]
    rfl
  have hmap : (Finset.univ.map e).powerset = Finset.univ.image (Finset.map e) := by
    simp only [funext (Finset.map_eq_image e), Finset.powerset_image, Finset.powerset_univ]
  let hit (I : Finset (Fin (N + 1))) : ℕ :=
    if (∑ i ∈ I, Fin.cons a s i) = g then 1 else 0
  -- Partition the index sets by whether they use the first entry.
  have hsplit : (∑ I, hit I) =
      (∑ I : Finset (Fin N), hit (I.map e)) +
        ∑ I : Finset (Fin N), hit (insert 0 (I.map e)) := by
    conv_lhs => rw [← Finset.powerset_univ, huniv, Finset.sum_powerset_insert (hzero _), hmap]
    simp only [Finset.sum_image (Finset.map_injective e).injOn]
  have htail (I : Finset (Fin N)) : (∑ i ∈ I.map e, Fin.cons a s i) = ∑ i ∈ I, s i := by
    simp [Finset.sum_map, e]
  simpa only [coverCount, Finset.card_eq_sum_ones, Finset.sum_filter, hit, htail,
    Finset.sum_insert (hzero _), Fin.cons_zero, add_comm a, ← eq_sub_iff_add_eq] using hsplit

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
