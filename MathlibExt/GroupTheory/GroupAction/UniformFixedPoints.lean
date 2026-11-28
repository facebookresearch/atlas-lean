/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.GroupAction.FixedPoints

/-!
# Burnside's lemma with a uniform fixed-point count

If every nonidentity element of a finite group `G` fixes the same number `c` of points of a
finite `G`-set `X`, Burnside's lemma reads `|X| + c (|G| - 1) = #orbits * |G|`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Burnside's lemma with a uniform fixed-point count.** Let a finite group $G$ act on a finite
set $X$, and let $c$ be a natural number such that every element $g \ne 1$ of $G$ fixes exactly
$c$ points of $X$. Writing $N$ for the number of orbits of $G$ on $X$, we have
$|X| + c\,(|G| - 1) = N \cdot |G|$. -/
theorem _root_.MulAction.card_add_mul_card_sub_one_eq_card_orbits_mul_card
    (G X : Type*) [Group G] [MulAction G X] [Finite G] [Finite X]
    (c : ℕ) (hfixed : ∀ g : G, g ≠ 1 → Nat.card (MulAction.fixedBy X g) = c) :
    Nat.card X + c * (Nat.card G - 1) =
      Nat.card (MulAction.orbitRel.Quotient G X) * Nat.card G := by
  classical
  let _ := Fintype.ofFinite G
  let _ := Fintype.ofFinite X
  let _ (g : G) := Fintype.ofFinite (MulAction.fixedBy X g)
  let _ := Fintype.ofFinite (MulAction.orbitRel.Quotient G X)
  simp only [Nat.card_eq_fintype_card] at hfixed ⊢
  rw [← MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group]
  symm
  have hsum :
      (∑ g ∈ (Finset.univ : Finset G).erase 1,
        Fintype.card (MulAction.fixedBy X g)) =
        ∑ _g ∈ (Finset.univ : Finset G).erase 1, c := by
    apply Finset.sum_congr rfl
    intro g hg
    exact hfixed g (Finset.ne_of_mem_erase hg)
  calc
    (∑ g : G, Fintype.card (MulAction.fixedBy X g)) =
        (∑ g ∈ (Finset.univ : Finset G).erase 1,
          Fintype.card (MulAction.fixedBy X g)) +
          Fintype.card (MulAction.fixedBy X (1 : G)) := by
      simpa using (Finset.sum_erase_add (Finset.univ : Finset G)
        (fun g : G => Fintype.card (MulAction.fixedBy X g)) (Finset.mem_univ 1)).symm
    _ = Fintype.card X + c * (Fintype.card G - 1) := by
      rw [hsum]
      simp [MulAction.fixedBy_one_eq_univ, Nat.mul_comm]
      omega

end

end MetaMathlibExt
