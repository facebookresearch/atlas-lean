/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import MathlibExt.Combinatorics.Additive.PerfectSubsetSumCover

/-!
# Removing the last entry from a perfect subset-sum cover

After removing the last entry of a perfect `2 ^ j`-cover, the prefix counts at an
element and at its translate by that entry sum to `2 ^ j`.
-/

namespace MetaMathlibExt

open PerfectSubsetSumCover

/-- **Removing the last element of a perfect $2^j$-cover.** Let $G$ be an abelian group, let
$s = (x_1, \dots, x_{k+1})$ be a family in $G$ that is a perfect $2^j$-cover of $G$, and let
$S_1 = (x_1, \dots, x_k)$. For every $a \in G$, if $S_1$ covers $a$ exactly $c$ times, then
$S_1$ covers $a + x_{k+1}$ exactly $2^j - c$ times.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 8
(`jis-2025-25.7.8-lem-8`). The paper's `|G| = 2^n` and `k + 1 = j + n` are not needed. -/
public theorem coverCount_init_add_last {G : Type*} [AddCommGroup G] [DecidableEq G]
    {j k : ℕ} {s : Fin (k + 1) → G} (hs : IsPerfectMCover (2 ^ j) s) (a : G) :
    coverCount (s ∘ Fin.castSucc) (a + s (Fin.last k)) =
      2 ^ j - coverCount (s ∘ Fin.castSucc) a := by
  have hlast (I : Finset (Fin k)) : Fin.last k ∉ I.map Fin.castSuccEmb := by
    simp [Finset.mem_map, Fin.castSuccEmb_apply, Fin.castSucc_ne_last]
  have huniv : (Finset.univ : Finset (Fin (k + 1))) =
      insert (Fin.last k) (Finset.univ.map Fin.castSuccEmb) := by
    rw [Fin.univ_castSuccEmb, Finset.cons_eq_insert]
  have hmap : ((Finset.univ : Finset (Fin k)).map Fin.castSuccEmb).powerset =
      Finset.univ.image (Finset.map Fin.castSuccEmb) := by
    simp only [funext (Finset.map_eq_image Fin.castSuccEmb), Finset.powerset_image,
      Finset.powerset_univ]
  let hit (I : Finset (Fin (k + 1))) : ℕ :=
    if (∑ i ∈ I, s i) = a + s (Fin.last k) then 1 else 0
  -- Count the full representations by whether they use the last index.
  have hsplit : (∑ I, hit I) =
      (∑ I : Finset (Fin k), hit (I.map Fin.castSuccEmb)) +
        ∑ I : Finset (Fin k), hit (insert (Fin.last k) (I.map Fin.castSuccEmb)) := by
    conv_lhs => rw [← Finset.powerset_univ, huniv, Finset.sum_powerset_insert (hlast _), hmap]
    simp only [Finset.sum_image (Finset.map_injective Fin.castSuccEmb).injOn]
  have hcount : coverCount s (a + s (Fin.last k)) =
      coverCount (s ∘ Fin.castSucc) (a + s (Fin.last k)) +
        coverCount (s ∘ Fin.castSucc) a := by
    simpa only [coverCount, Finset.card_eq_sum_ones, Finset.sum_filter, hit,
      Finset.sum_insert (hlast _), Finset.sum_map, Fin.castSuccEmb_apply, Function.comp_apply,
      add_comm (s (Fin.last k)), add_right_cancel_iff] using hsplit
  rw [← hs (a + s (Fin.last k)), hcount, Nat.add_sub_cancel_right]

end MetaMathlibExt
