/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.Linarith

/-!
# Move-to-front list update is `2`-competitive, and no deterministic algorithm beats `2 - 2/(ℓ+1)`

The list update problem (Sleator and Tarjan, *Amortized efficiency of list update and paging
rules*, CACM 1985; Borodin and El-Yaniv, *Online Computation and Competitive Analysis*,
Chapter 1): items are kept in a list, accessing the item at position `i` costs `i`
(`accessCost`), and an algorithm may rearrange the list between accesses. Move-to-front (`mtf`)
moves each accessed item to the front, free of charge.

The offline competitor follows Sleator and Tarjan's model (`offlineCostFree`): it serves request
`t` with its list `L t`, may move the accessed item forward for free (`freeMove`), and then pays
one for each pair of items whose relative order it changes to reach `L (t + 1)` (`inv`, Kendall's
tau distance, the number of paid adjacent transpositions). Without free moves this is
`offlineCost`; the static competitor, which never rearranges, is the special case of a constant
`L`.

Main results:

* `inv_triangle`: `inv M L' ≤ inv M L + inv L L'`.
* `mtf_step` (the amortized step): with the potential `Φ = inv` (move-to-front's list against the
  competitor's), accessing an item at position `k` in move-to-front's list and `i` in the
  competitor's costs `k + ΔΦ ≤ 2 i - 1`; `inv_freeMove_le`: the competitor's free moves only
  lower `Φ`.
* `mtfCost_add_inv_le_free`: summed over a request sequence.
* `mtfCost_le_free` (**move-to-front is `2`-competitive**, Sleator and Tarjan): from the same
  initial list, `MTF + m ≤ 2 OFF` on every sequence of `m` requests, free exchanges included;
  `mtfCost_le`: the same without free exchanges.
* `mtfCost_le_static`: against a static list `L`, `MTF + m ≤ 2 STATIC + inv M L`.
* `not_competitive` (**the lower bound**): no deterministic online algorithm (`OnlineListUpdate`,
  even with free rearrangements; `mtfOnline` is one) is `c / d`-competitive for any
  `c / d < 2 ℓ / (ℓ + 1) = 2 - 2 / (ℓ + 1)` on `ℓ` items. The adversary always requests the last
  item (`cost_adversary`: cost `ℓ` per request), while `M` or its reverse serves any sequence at
  average cost `(ℓ + 1) / 2` (`staticCost_add_reverse`).

## Cost model

The cost is the access cost (positions) plus, for the offline competitor, its paid rearrangement
cost `inv`; its free exchanges and move-to-front's own moves cost nothing (the "free exchanges"
of Sleator and Tarjan).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Online.ListUpdate

variable {α : Type*} [DecidableEq α]

/-! ## Costs -/

/-- **Access cost.** The cost of accessing an item $x$ in a list $L$ is its position in $L$,
counting from $1$: one more than the index of the first occurrence of $x$ in $L$. If $x$ does not
occur in $L$, the cost is the length of $L$ plus one. -/
def accessCost (L : List α) (x : α) : ℕ := L.idxOf x + 1

/-- **Move-to-front.** For a list $L$ and an item $x$, moving $x$ to the front gives the list
consisting of $x$ followed by $L$ with its first occurrence of $x$ removed; if $x$ does not
occur in $L$, this is $x$ followed by $L$. -/
def mtf (L : List α) (x : α) : List α := x :: L.erase x

/-- **Cost of move-to-front.** Starting from a list $L$, move-to-front serves a request sequence
$\sigma$ one request at a time: a request $x$ costs the position of $x$ in the current list,
counting from $1$ (an item not in the list costs its length plus one), and then $x$ is moved to
the front (inserted at the front if absent). The cost of move-to-front on $\sigma$ from $L$ is
the sum of these access costs. -/
def mtfCost : List α → List α → ℕ
  | _, [] => 0
  | L, x :: σ => accessCost L x + mtfCost (mtf L x) σ

/-- **Final list of move-to-front.** Starting from a list $L$ and serving a request sequence
$\sigma$, move-to-front moves each request $x$ in turn to the front of the current list
(inserting it at the front if it is absent). The final list of move-to-front on $\sigma$ from
$L$ is the list it ends with. -/
def mtfFinal : List α → List α → List α
  | L, [] => L
  | L, x :: σ => mtfFinal (mtf L x) σ

/-- **Inversion set of two lists.** For lists $M$ and $L$, the inversion set is the set of pairs
$(a, b)$ of items of $M$ with $a$ before $b$ in $M$ and $b$ before $a$ in $L$, that is, the pairs
that $M$ and $L$ order differently. Here the position of an item in a list is the index of its
first occurrence, and an item that does not occur in the list sits at the position equal to the
length of the list. -/
def invSet (M L : List α) : Finset (α × α) :=
  (M.toFinset ×ˢ M.toFinset).filter fun ab => M.idxOf ab.1 < M.idxOf ab.2 ∧
    L.idxOf ab.2 < L.idxOf ab.1

/-- **Number of inversions between two lists.** For lists $M$ and $L$, the number of inversions
of $L$ against $M$ is the size of their inversion set: the number of pairs $(a, b)$ of items of
$M$ with $a$ before $b$ in $M$ and $b$ before $a$ in $L$, where the position of an item in a list
is the index of its first occurrence, or the length of the list if it does not occur.

When $L$ is a rearrangement of a list $M$ without duplicates, this is the Kendall tau distance
between them. -/
def inv (M L : List α) : ℕ := (invSet M L).card

/-- **Offline cost without free exchanges.** Given lists $L_0, L_1, L_2, \dots$, the offline cost
of a request sequence $\sigma = x_0 x_1 \cdots x_{m-1}$ is the sum over $t < m$ of the access cost
of $x_t$ in $L_t$ (its position, counting from $1$) plus the number of inversions between $L_t$
and $L_{t+1}$. That is, the algorithm serves request $t$ with $L_t$ and then rearranges it into
$L_{t+1}$, paying one for each pair of items whose relative order it changes.

Adding free exchanges gives the offline cost with free exchanges. -/
def offlineCost (L : ℕ → List α) : List α → ℕ
  | [] => 0
  | x :: σ => accessCost (L 0) x + inv (L 0) (L 1) + offlineCost (fun t => L (t + 1)) σ

/-- **Free move.** A free exchange (Sleator and Tarjan): right after accessing $x$ in a list $L$,
move $x$ forward to index $j$ (indices counted from $0$), at no charge. If the index of $x$ in
$L$ is at most $j$, the list is unchanged, so $x$ never moves backward for free; otherwise the
result is obtained by erasing the first occurrence of $x$ from $L$ and inserting $x$ back so that
it has index $j$. -/
def freeMove (L : List α) (x : α) (j : ℕ) : List α :=
  if L.idxOf x ≤ j then L else (L.erase x).take j ++ x :: (L.erase x).drop j

/-- **Offline cost with free exchanges.** Given lists $L_0, L_1, L_2, \dots$, target indices
$J_0, J_1, J_2, \dots$ and a request sequence $\sigma = x_0 x_1 \cdots x_{m-1}$, let $L_t'$ be the
list obtained from $L_t$ by the free exchange that moves $x_t$ forward to index $J_t$ (counting
from $0$); it equals $L_t$ if $x_t$ already has index at most $J_t$. The offline cost with free
exchanges of $\sigma$ is the sum over $t < m$ of the access cost of $x_t$ in $L_t$ (its position,
counting from $1$) plus the number of inversions between $L_t'$ and $L_{t+1}$.

This is the model of Sleator and Tarjan: the free exchange costs nothing, and each pair of items
whose relative order changes from $L_t'$ to $L_{t+1}$ costs one. With no free moves it is the
offline cost without free exchanges. -/
def offlineCostFree (L : ℕ → List α) (J : ℕ → ℕ) : List α → ℕ
  | [] => 0
  | x :: σ => accessCost (L 0) x + inv (freeMove (L 0) x (J 0)) (L 1) +
      offlineCostFree (fun t => L (t + 1)) (fun t => J (t + 1)) σ

/-! ## Order facts -/

/-- **Indices after erasing an entry.** Let $M$ be a list with no repeated entries and let
$a \ne x$ be entries of $M$. After erasing $x$ from $M$, the index of $a$ is unchanged if $a$
comes before $x$ in $M$, and is one less if $a$ comes after $x$ (indices counted from $0$). -/
theorem idxOf_erase {x a : α} : ∀ {M : List α}, M.Nodup → a ≠ x → a ∈ M → x ∈ M →
    (M.erase x).idxOf a = if M.idxOf a < M.idxOf x then M.idxOf a else M.idxOf a - 1
  | [], _, _, ha, _ => absurd ha List.not_mem_nil
  | b :: M, hnd, hax, ha, hx => by
      by_cases hbx : b = x
      · subst hbx
        rw [List.erase_cons_head, List.idxOf_cons_self, List.idxOf_cons_ne _ (Ne.symm hax)]
        simp
      · have hb : ¬((b == x) = true) := by simpa using hbx
        rw [List.erase_cons_tail hb]
        have hx' : x ∈ M := (List.mem_cons.1 hx).resolve_left (Ne.symm hbx)
        rw [List.idxOf_cons_ne _ hbx]
        by_cases hba : b = a
        · subst hba
          simp only [List.idxOf_cons_self]
          simp
        · have ha' : a ∈ M := (List.mem_cons.1 ha).resolve_left (Ne.symm hba)
          rw [List.idxOf_cons_ne _ hba, List.idxOf_cons_ne _ hba,
            idxOf_erase (List.nodup_cons.1 hnd).2 hax ha' hx']
          have hne : M.idxOf a ≠ M.idxOf x := fun h => hax ((List.idxOf_inj ha').1 h)
          split_ifs <;> omega

/-- **Move-to-front keeps the relative order of the other items.** Let $M$ be a list without
duplicates, $x$ an item of $M$, and let $M'$ be the list obtained from $M$ by moving $x$ to the
front. For any items $a \ne x$ and $b \ne x$ of $M$, $a$ comes before $b$ in $M'$ if and only if
$a$ comes before $b$ in $M$. -/
theorem idxOf_mtf_lt_iff {M : List α} (hnd : M.Nodup) {x a b : α} (hx : x ∈ M) (ha : a ∈ M)
    (hb : b ∈ M) (hax : a ≠ x) (hbx : b ≠ x) :
    (mtf M x).idxOf a < (mtf M x).idxOf b ↔ M.idxOf a < M.idxOf b := by
  simp only [mtf, List.idxOf_cons_ne _ (Ne.symm hax), List.idxOf_cons_ne _ (Ne.symm hbx),
    Nat.succ_lt_succ_iff, idxOf_erase hnd hax ha hx, idxOf_erase hnd hbx hb hx]
  have hne : M.idxOf a ≠ M.idxOf x := fun h => hax ((List.idxOf_inj ha).1 h)
  have hne' : M.idxOf b ≠ M.idxOf x := fun h => hbx ((List.idxOf_inj hb).1 h)
  split_ifs <;> omega

/-- **Counting the entries before an entry.** If $L$ is a list with no repeated entries and $x$
is an entry of $L$, then the number of entries of $L$ whose index is less than the index of $x$
equals the index of $x$ (indices counted from $0$). -/
theorem card_before {L : List α} (hnd : L.Nodup) {x : α} (hx : x ∈ L) :
    (L.toFinset.filter fun a => L.idxOf a < L.idxOf x).card = L.idxOf x := by
  have : (L.toFinset.filter fun a => L.idxOf a < L.idxOf x) = (L.take (L.idxOf x)).toFinset := by
    ext a
    simp only [Finset.mem_filter, List.mem_toFinset]
    constructor
    · rintro ⟨ha, h⟩; exact (List.mem_take_iff_idxOf_lt ha).2 h
    · intro h
      have ha := List.mem_of_mem_take h
      exact ⟨ha, (List.mem_take_iff_idxOf_lt ha).1 h⟩
  rw [this, List.toFinset_card_of_nodup (hnd.sublist (List.take_sublist _ _)), List.length_take,
    Nat.min_eq_left (List.idxOf_lt_length_of_mem hx).le]

/-! ## The potential: inversions against the offline list -/

/-- **Members of the inversion set.** Let $M$ and $L$ be lists. If a pair $(a, b)$ belongs to the
inversion set of $M$ and $L$, then $a$ and $b$ are items of $M$, $a$ comes before $b$ in $M$, and
$b$ comes before $a$ in $L$. Here the position of an item in a list is the index of its first
occurrence, and an item that does not occur in the list sits at the position equal to the length
of the list. -/
theorem mem_of_mem_invSet {M L : List α} {ab : α × α} (h : ab ∈ invSet M L) :
    ab.1 ∈ M ∧ ab.2 ∈ M ∧ M.idxOf ab.1 < M.idxOf ab.2 ∧ L.idxOf ab.2 < L.idxOf ab.1 := by
  simp only [invSet, Finset.mem_filter, Finset.mem_product, List.mem_toFinset] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem mem_invSet {M L : List α} {a b : α} (ha : a ∈ M) (hb : b ∈ M)
    (h1 : M.idxOf a < M.idxOf b) (h2 : L.idxOf b < L.idxOf a) : (a, b) ∈ invSet M L := by
  simp only [invSet, Finset.mem_filter, Finset.mem_product, List.mem_toFinset]
  exact ⟨⟨ha, hb⟩, h1, h2⟩

theorem inv_self (L : List α) : inv L L = 0 := by
  rw [inv, invSet, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro ab _ h
  omega

/-- **Triangle inequality for inversions.** Let $M$, $L$ and $L'$ be lists with $L$ a
rearrangement of $M$. Then the number of inversions of $L'$ against $M$ is at most the number of
inversions of $L$ against $M$ plus the number of inversions of $L'$ against $L$. -/
theorem inv_triangle {M L L' : List α} (hL : L.Perm M) :
    inv M L' ≤ inv M L + inv L L' := by
  unfold inv
  refine (Finset.card_le_card fun ab hab => ?_).trans (Finset.card_union_le _ _)
  obtain ⟨ha, hb, h1, h2⟩ := mem_of_mem_invSet hab
  have hab' : ab.1 ≠ ab.2 := fun h => by rw [h] at h1; omega
  have haL : ab.1 ∈ L := hL.mem_iff.2 ha
  have hbL : ab.2 ∈ L := hL.mem_iff.2 hb
  have hne : L.idxOf ab.1 ≠ L.idxOf ab.2 := fun h => hab' ((List.idxOf_inj haL).1 h)
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact Finset.mem_union_right _ (mem_invSet haL hbL h h2)
  · exact Finset.mem_union_left _ (mem_invSet ha hb h1 h)

/-- **The amortized cost of a move-to-front step.** Let $M$ be a list of distinct items, $L$ a
rearrangement of $M$ (the offline list), and $x$ an item of $M$ at position $k$ in $M$ and
position $i$ in $L$, counting from $1$. Let $\Phi$ be the number of inversions between $M$ and
$L$ (the pairs of items that the two lists order differently), and $\Phi'$ the number of
inversions between the list obtained from $M$ by moving $x$ to the front and $L$. Then
$k + \Phi' \le \Phi + 2i - 1$.

This is the amortized step of Sleator and Tarjan's analysis, with potential $\Phi$. -/
theorem mtf_step {M L : List α} (hnd : M.Nodup) (hL : L.Perm M) {x : α} (hx : x ∈ M) :
    accessCost M x + inv (mtf M x) L + 1 ≤ inv M L + 2 * accessCost L x := by
  have hndL : L.Nodup := hL.nodup_iff.2 hnd
  have hxL : x ∈ L := hL.mem_iff.2 hx
  have hmtf : (mtf M x).Perm M := (List.perm_cons_erase hx).symm
  set S0 := (invSet M L).filter fun ab => ab.1 ≠ x ∧ ab.2 ≠ x
  set BL := L.toFinset.filter fun a => L.idxOf a < L.idxOf x
  set BM := M.toFinset.filter fun a => M.idxOf a < M.idxOf x
  set A1 := BM.filter fun a => L.idxOf x < L.idxOf a
  -- the new inversions: old ones without `x`, and `x` before everything that precedes it in `L`
  have h1 : inv (mtf M x) L ≤ S0.card + BL.card := by
    unfold inv
    refine (Finset.card_le_card (t := S0 ∪ BL.image fun b => (x, b)) fun ab hab => ?_).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _))
    obtain ⟨ha, hb, hlt, hL'⟩ := mem_of_mem_invSet hab
    have ha' : ab.1 ∈ M := hmtf.mem_iff.1 ha
    have hb' : ab.2 ∈ M := hmtf.mem_iff.1 hb
    by_cases hax : ab.1 = x
    · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨ab.2, ?_, ?_⟩)
      · simp only [BL, Finset.mem_filter, List.mem_toFinset]
        exact ⟨hL.mem_iff.2 hb', hax ▸ hL'⟩
      · ext <;> simp [hax]
    · have hbx : ab.2 ≠ x := by
        rintro hbx
        rw [hbx, mtf, List.idxOf_cons_self] at hlt
        omega
      refine Finset.mem_union_left _ (Finset.mem_filter.2 ⟨?_, hax, hbx⟩)
      exact mem_invSet ha' hb' ((idxOf_mtf_lt_iff hnd hx ha' hb' hax hbx).1 hlt) hL'
  -- the old inversions include those without `x` and the pairs `(a, x)` from `A1`
  have h2 : S0.card + A1.card ≤ inv M L := by
    unfold inv
    rw [← Finset.card_image_of_injective A1 (f := fun a => (a, x))
      (fun a b h => by simpa using h), ← Finset.card_union_of_disjoint]
    · refine Finset.card_le_card fun ab hab => ?_
      rcases Finset.mem_union.1 hab with h | h
      · exact (Finset.mem_filter.1 h).1
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h
        simp only [A1, BM, Finset.mem_filter, List.mem_toFinset] at ha
        exact mem_invSet ha.1.1 hx ha.1.2 ha.2
    · rw [Finset.disjoint_left]
      intro ab h h'
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 h'
      exact (Finset.mem_filter.1 h).2.2 rfl
  -- what precedes `x` in `M` either follows it in `L` or precedes it there too
  have h3 : BM.card ≤ A1.card + BL.card := by
    refine (Finset.card_le_card fun a ha => ?_).trans (Finset.card_union_le _ _)
    simp only [BM, Finset.mem_filter, List.mem_toFinset] at ha
    have hax : a ≠ x := fun h => by rw [h] at ha; omega
    have haL : a ∈ L := hL.mem_iff.2 ha.1
    have hne : L.idxOf a ≠ L.idxOf x := fun h => hax ((List.idxOf_inj haL).1 h)
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · refine Finset.mem_union_right _ ?_
      simp only [BL, Finset.mem_filter, List.mem_toFinset]
      exact ⟨haL, h⟩
    · refine Finset.mem_union_left _ ?_
      simp only [A1, BM, Finset.mem_filter, List.mem_toFinset]
      exact ⟨ha, h⟩
  have hBM : BM.card = M.idxOf x := card_before hnd hx
  have hBL : BL.card = L.idxOf x := card_before hndL hxL
  unfold accessCost
  omega

/-! ## Move-to-front is `2`-competitive -/

/-- **Move-to-front rearranges the list.** If $x$ is an item of a list $M$, then the list
obtained from $M$ by moving $x$ to the front is a rearrangement (permutation) of $M$. -/
theorem mtf_perm {M : List α} {x : α} (hx : x ∈ M) : (mtf M x).Perm M :=
  (List.perm_cons_erase hx).symm

theorem mtf_nodup {M : List α} (hnd : M.Nodup) (x : α) : (mtf M x).Nodup :=
  List.nodup_cons.2 ⟨fun h => (List.Nodup.mem_erase_iff hnd).1 h |>.1 rfl, hnd.erase x⟩

/-! ## Free exchanges -/

/-- **A free move rearranges the list.** If $x$ is an item of a list $L$, then for every index
$j$ (counting from $0$), the list obtained from $L$ by the free move of $x$ to index $j$ is a
rearrangement (permutation) of $L$. -/
theorem freeMove_perm {L : List α} {x : α} (hx : x ∈ L) (j : ℕ) : (freeMove L x j).Perm L := by
  unfold freeMove
  split_ifs
  · exact List.Perm.refl L
  · refine List.perm_middle.trans ?_
    rw [List.take_append_drop]
    exact (List.perm_cons_erase hx).symm

/-- Positions after a free move of `x` to position `j`: `x` lands at `j`, and the other items keep
their order, shifting by one at and after `j`. -/
private theorem idxOf_freeMove {L : List α} (hnd : L.Nodup) {x : α} (hx : x ∈ L) {j : ℕ}
    (hj : j < L.idxOf x) :
    (freeMove L x j).idxOf x = j ∧ ∀ a ∈ L, a ≠ x →
      (freeMove L x j).idxOf a =
        if (L.erase x).idxOf a < j then (L.erase x).idxOf a else (L.erase x).idxOf a + 1 := by
  have hF : freeMove L x j = (L.erase x).take j ++ x :: (L.erase x).drop j := by
    have : ¬ L.idxOf x ≤ j := by omega
    simp only [freeMove, this, ↓reduceIte]
  have hxE : x ∉ L.erase x := hnd.not_mem_erase
  have hlenE : (L.erase x).length = L.length - 1 := List.length_erase_of_mem hx
  have hxlt : L.idxOf x < L.length := List.idxOf_lt_length_of_mem hx
  have htake : ((L.erase x).take j).length = j := by rw [List.length_take]; omega
  refine ⟨?_, fun a ha hax => ?_⟩
  · rw [hF, List.idxOf_append_of_notMem (fun h => hxE (List.mem_of_mem_take h)), htake,
      List.idxOf_cons_self]
    rfl
  · have haE : a ∈ L.erase x := (List.Nodup.mem_erase_iff hnd).2 ⟨hax, ha⟩
    rw [hF]
    by_cases hmem : a ∈ (L.erase x).take j
    · have hlt := (List.mem_take_iff_idxOf_lt haE).1 hmem
      rw [List.idxOf_append_of_mem hmem]
      simp only [hlt, ↓reduceIte]
      exact ((List.take_prefix j _).idxOf_eq_of_mem hmem)
    · have hge : ¬ (L.erase x).idxOf a < j := fun h => hmem ((List.mem_take_iff_idxOf_lt haE).2 h)
      have hE : (L.erase x).idxOf a = j + (L.erase x |>.drop j).idxOf a := by
        conv_lhs => rw [← List.take_append_drop j (L.erase x)]
        rw [List.idxOf_append_of_notMem hmem, htake]
      rw [List.idxOf_append_of_notMem hmem, htake, List.idxOf_cons_ne _ (Ne.symm hax), hE]
      simp only [hE] at hge
      simp only [hge, ↓reduceIte]
      omega

/-- **Free moves never add inversions against a list headed by the moved item.** Let $L$ be a list
without duplicates, $x$ an item of $L$, and $N$ a list that is empty or starts with $x$, all of
whose items occur in $L$. For every $j \in \mathbb{N}$, let $L'$ be the list obtained from $L$ by
moving $x$ forward for free so that exactly $j$ items precede it, where $L' = L$ if at most $j$
items already precede $x$ in $L$. Then the number of inversions of $L'$ against $N$ is at most the
number of inversions of $L$ against $N$.

This applies to move-to-front's list right after accessing $x$. -/
theorem inv_freeMove_le {N L : List α} {x : α} (hN : N.idxOf x = 0) (hNL : ∀ a ∈ N, a ∈ L)
    (hnd : L.Nodup) (hx : x ∈ L) (j : ℕ) : inv N (freeMove L x j) ≤ inv N L := by
  by_cases hj : L.idxOf x ≤ j
  · simp only [freeMove, hj, ↓reduceIte]
    exact le_refl _
  obtain ⟨hFx, hFa⟩ := idxOf_freeMove hnd hx (j := j) (by omega)
  refine Finset.card_le_card fun ab hab => ?_
  obtain ⟨ha, hb, h1, h2⟩ := mem_of_mem_invSet hab
  refine mem_invSet ha hb h1 ?_
  have haL := hNL _ ha
  have hbL := hNL _ hb
  have hbx : ab.2 ≠ x := fun h => by rw [h, hN] at h1; omega
  rw [hFa _ hbL hbx] at h2
  have hneb : L.idxOf ab.2 ≠ L.idxOf x := fun h => hbx ((List.idxOf_inj hbL).1 h)
  have heb := idxOf_erase hnd hbx hbL hx
  by_cases hax : ab.1 = x
  · rw [hax, hFx] at h2
    rw [hax]
    split_ifs at h2 heb <;> omega
  · rw [hFa _ haL hax] at h2
    have hnea : L.idxOf ab.1 ≠ L.idxOf x := fun h => hax ((List.idxOf_inj haL).1 h)
    have hea := idxOf_erase hnd hax haL hx
    split_ifs at h2 hea heb <;> omega

/-- **Amortized bound for move-to-front over a request sequence, with free exchanges.** Let $M$ be
a list without duplicates, $\sigma$ a sequence of $m$ requests, each an item of $M$, $L_0, L_1,
\dots$ lists that are each a rearrangement of $M$, and $J_0, J_1, \dots$ natural numbers.
Accessing the item at position $i$ of a list, counting from $1$, costs $i$. Let $C$ be the total
access cost of move-to-front on $\sigma$ starting from $M$, $F$ the list it ends with, and $D$
the cost on $\sigma$ of the offline algorithm with free exchanges that serves the $t$-th request
(counting from $0$) with list $L_t$, paying its access cost, then moves the accessed item forward
for free so that exactly $J_t$ items precede it (no move if at most $J_t$ items already precede
it), and finally rearranges the resulting list into $L_{t+1}$, paying one for each pair of items
whose relative order changes. Writing $\mathrm{inv}(N, K)$ for the number of inversions of $K$
against $N$,

$$C + \mathrm{inv}(F, L_m) + m \le 2D + \mathrm{inv}(M, L_0).$$
-/
theorem mtfCost_add_inv_le_free : ∀ (σ M : List α) (L : ℕ → List α) (J : ℕ → ℕ), M.Nodup →
    (∀ t, (L t).Perm M) → (∀ x ∈ σ, x ∈ M) →
    mtfCost M σ + inv (mtfFinal M σ) (L σ.length) + σ.length ≤
      2 * offlineCostFree L J σ + inv M (L 0)
  | [], M, L, _, _, _, _ => by simp [mtfCost, mtfFinal, offlineCostFree]
  | x :: σ, M, L, J, hnd, hL, hσ => by
      have hx : x ∈ M := hσ x List.mem_cons_self
      have hpm := mtf_perm hx
      have hxL : x ∈ L 0 := (hL 0).mem_iff.2 hx
      have ih := mtfCost_add_inv_le_free σ (mtf M x) (fun t => L (t + 1)) (fun t => J (t + 1))
        (mtf_nodup hnd x) (fun t => (hL (t + 1)).trans hpm.symm)
        (fun y hy => hpm.symm.mem_iff.1 (hσ y (List.mem_cons_of_mem _ hy)))
      have hstep := mtf_step hnd (hL 0) hx
      have hF : (freeMove (L 0) x (J 0)).Perm (mtf M x) :=
        (freeMove_perm hxL _).trans ((hL 0).trans hpm.symm)
      have htri := inv_triangle (M := mtf M x) (L' := L 1) hF
      have hfree := inv_freeMove_le (N := mtf M x) (by simp [mtf])
        (fun a ha => (hL 0).mem_iff.2 (hpm.mem_iff.1 ha)) ((hL 0).nodup_iff.2 hnd) hxL (J 0)
      simp only [mtfCost, mtfFinal, offlineCostFree, List.length_cons, Nat.zero_add] at ih ⊢
      omega

/-- **Without free moves the two offline costs agree.** Let $K$ be a natural number and let
$L_0, L_1, L_2, \dots$ be lists, each of length at most $K$. Take every free-exchange target to be
$K$; this moves nothing, since every item already has index at most $K$. Then for every request
sequence $\sigma$, the offline cost with free exchanges of serving $\sigma$ with $L_0, L_1, \dots$
equals the offline cost without free exchanges of serving $\sigma$ with $L_0, L_1, \dots$. -/
theorem offlineCostFree_noMove {K : ℕ} : ∀ (σ : List α) (L : ℕ → List α),
    (∀ t, (L t).length ≤ K) → offlineCostFree L (fun _ => K) σ = offlineCost L σ
  | [], _, _ => rfl
  | x :: σ, L, hK => by
      have hmove : freeMove (L 0) x K = L 0 := by
        simp only [freeMove, List.idxOf_le_length.trans (hK 0), ↓reduceIte]
      simp only [offlineCostFree, offlineCost, hmove,
        offlineCostFree_noMove σ (fun t => L (t + 1)) fun t => hK (t + 1)]

/-- **Amortized bound for move-to-front over a request sequence.** Let $M$ be a list without
duplicates, $\sigma$ a sequence of $m$ requests, each an item of $M$, and $L_0, L_1, \dots$ lists
that are each a rearrangement of $M$. Accessing the item at position $i$ of a list, counting from
$1$, costs $i$. Let $C$ be the total access cost of move-to-front on $\sigma$ starting from $M$,
$F$ the list it ends with, and $D$ the cost on $\sigma$ of the offline algorithm without free
exchanges that serves the $t$-th request (counting from $0$) with list $L_t$, paying its access
cost, and then rearranges it into $L_{t+1}$, paying one for each pair of items whose relative
order changes. Writing $\mathrm{inv}(N, K)$ for the number of inversions of $K$ against $N$,

$$C + \mathrm{inv}(F, L_m) + m \le 2D + \mathrm{inv}(M, L_0).$$
-/
theorem mtfCost_add_inv_le (σ M : List α) (L : ℕ → List α) (hnd : M.Nodup)
    (hL : ∀ t, (L t).Perm M) (hσ : ∀ x ∈ σ, x ∈ M) :
    mtfCost M σ + inv (mtfFinal M σ) (L σ.length) + σ.length ≤
      2 * offlineCost L σ + inv M (L 0) := by
  have := mtfCost_add_inv_le_free σ M L (fun _ => M.length) hnd hL hσ
  rwa [offlineCostFree_noMove σ L fun t => (hL t).length_eq.le] at this

/-- **Move-to-front is 2-competitive.** In the model of Sleator and Tarjan (1985) with free
exchanges, let $M$ be a list of distinct items and $\sigma$ a sequence of $m$ requests, each an
item of $M$. Consider an offline algorithm given by lists $L_0, L_1, \ldots$, each a
rearrangement of $M$ with $L_0 = M$, and natural numbers $J_0, J_1, \ldots$. It serves request
$t$ (counting from $0$) with the list $L_t$ and pays the position of the request in $L_t$
(counting from $1$). If more than $J_t$ items precede the request in $L_t$, it then moves the
request forward for free so that exactly $J_t$ items precede it, keeping the order of the other
items. Finally it pays one for each pair of items whose relative order differs between the
resulting list and $L_{t+1}$. Then the access cost of move-to-front on $\sigma$ starting from
$M$, plus $m$, is at most twice the total cost of the offline algorithm. -/
theorem mtfCost_le_free (σ : List α) {M : List α} (hnd : M.Nodup) (L : ℕ → List α)
    (J : ℕ → ℕ) (hL : ∀ t, (L t).Perm M) (h0 : L 0 = M) (hσ : ∀ x ∈ σ, x ∈ M) :
    mtfCost M σ + σ.length ≤ 2 * offlineCostFree L J σ := by
  have := mtfCost_add_inv_le_free σ M L J hnd hL hσ
  rw [h0, inv_self] at this
  omega

/-- **Move-to-front is 2-competitive without free exchanges.** Let $M$ be a list of distinct
items and $\sigma$ a sequence of $m$ requests, each an item of $M$. Consider an offline
algorithm that serves request $t$ with a list $L_t$, where every $L_t$ is a rearrangement of
$M$ and $L_0 = M$: it pays the position of the request in $L_t$ (counting from $1$), and then
one for each pair of items whose relative order differs between $L_t$ and $L_{t+1}$. Then the
access cost of move-to-front on $\sigma$ starting from $M$, plus $m$, is at most twice the
total cost of the offline algorithm.

This is the special case of the model with free exchanges in which no free exchange is made. -/
theorem mtfCost_le (σ : List α) {M : List α} (hnd : M.Nodup) (L : ℕ → List α)
    (hL : ∀ t, (L t).Perm M) (h0 : L 0 = M) (hσ : ∀ x ∈ σ, x ∈ M) :
    mtfCost M σ + σ.length ≤ 2 * offlineCost L σ := by
  have := mtfCost_add_inv_le σ M L hnd hL hσ
  rw [h0, inv_self] at this
  omega

/-- **Move-to-front against a static list.** Let $M$ be a list of distinct items, $L$ a
rearrangement of $M$, and $\sigma$ a sequence of $m$ requests, each an item of $M$. Then the
access cost of move-to-front on $\sigma$ starting from $M$, plus $m$, is at most twice the cost
of serving $\sigma$ with the fixed list $L$ (the sum over the requests of their positions in $L$,
counting from $1$), plus the number of inversions between $M$ and $L$ (the pairs of items that
$M$ and $L$ order differently). -/
theorem mtfCost_le_static (σ : List α) {M L : List α} (hnd : M.Nodup) (hL : L.Perm M)
    (hσ : ∀ x ∈ σ, x ∈ M) :
    mtfCost M σ + σ.length ≤ 2 * (σ.map (accessCost L)).sum + inv M L := by
  have h := mtfCost_add_inv_le σ M (fun _ => L) hnd (fun _ => hL) hσ
  have hstatic : ∀ τ : List α, offlineCost (fun _ => L) τ = (τ.map (accessCost L)).sum := by
    intro τ
    induction τ with
    | nil => rfl
    | cons y τ ih => simp [offlineCost, inv_self, ih]
  rw [hstatic] at h
  omega

/-! ## The lower bound for deterministic online algorithms -/

/-- A deterministic online list-update algorithm on the items of `M`: a state machine whose list
is always a rearrangement of `M`. Its rearrangements are free, which only strengthens the lower
bound. -/
structure OnlineListUpdate.{u, v} (α : Type u) (M : List α) where
  /-- The algorithm's internal state. -/
  State : Type v
  /-- The initial state. -/
  init : State
  /-- The list in each state. -/
  list : State → List α
  /-- The next state after a request. -/
  step : State → α → State
  /-- The list is always a rearrangement of `M`. -/
  perm : ∀ q, (list q).Perm M

namespace OnlineListUpdate

variable {M : List α} (A : OnlineListUpdate α M)

/-- **Cost of an online list-update algorithm.** The cost of a deterministic online list-update
algorithm $A$ on a request sequence $x_1, \dots, x_m$ from a state $q_0$ is
$c_1 + \dots + c_m$, where $q_i$ is the state $A$ moves to from $q_{i-1}$ on request $x_i$ and
$c_i$ is the access cost of $x_i$ in the list of state $q_{i-1}$. The empty sequence costs $0$. -/
def cost : A.State → List α → ℕ
  | _, [] => 0
  | q, x :: σ => accessCost (A.list q) x + cost (A.step q x) σ

/-- **The list-update adversary.** Given a deterministic online list-update algorithm $A$, a
default item $d$, a number $n$ and a state $q$ of $A$, the adversary's sequence is the sequence of
$n$ requests that starts in state $q$, always requests the last item of $A$'s current list, and
then moves $A$ to its next state on that request. If the current list is empty, the default item
$d$ is requested instead. -/
def adversary (d : α) : ℕ → A.State → List α
  | 0, _ => []
  | n + 1, q => (A.list q).getLastD d :: adversary d n (A.step q ((A.list q).getLastD d))

omit [DecidableEq α] in
theorem length_adversary (d : α) : ∀ n q, (A.adversary d n q).length = n
  | 0, _ => rfl
  | n + 1, q => by simp [adversary, length_adversary d n]

omit [DecidableEq α] in
/-- **The list of an algorithm on a nonempty list is never empty.** Let $A$ be a deterministic
online list-update algorithm on the items of a nonempty list $M$. Then in every state of $A$, the
list of $A$ is nonempty. -/
theorem list_ne_nil (hM : M ≠ []) (q : A.State) : A.list q ≠ [] := fun h => by
  have := A.perm q
  rw [h] at this
  exact hM this.symm.eq_nil

omit [DecidableEq α] in
theorem adversary_mem (d : α) (hM : M ≠ []) : ∀ n q, ∀ x ∈ A.adversary d n q, x ∈ M
  | 0, _, _, h => absurd h List.not_mem_nil
  | n + 1, q, x, h => by
      simp only [adversary, List.mem_cons] at h
      rcases h with rfl | h
      · have hne := A.list_ne_nil hM q
        rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne, Option.getD_some]
        exact (A.perm q).subset (List.getLast_mem hne)
      · exact adversary_mem d hM n _ x h

/-- **The adversary makes every access cost the full length of the list.** Let $M$ be a nonempty
list of $\ell$ distinct items and let $A$ be a deterministic online list-update algorithm on the
items of $M$. For every default item $d$, every natural number $n$ and every state $q$ of $A$,
the cost of $A$ from state $q$ on the adversary's sequence of $n$ requests from $q$ with default
item $d$ is $n \ell$. -/
theorem cost_adversary {d : α} (hnd : M.Nodup) (hM : M ≠ []) :
    ∀ n q, A.cost q (A.adversary d n q) = n * M.length
  | 0, _ => by simp [adversary, cost]
  | n + 1, q => by
      simp only [adversary, cost, cost_adversary hnd hM n]
      have hne := A.list_ne_nil hM q
      have hlen := (A.perm q).length_eq
      have hnd' := (A.perm q).nodup_iff.2 hnd
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne, Option.getD_some,
        accessCost, List.getLast_eq_getElem, hnd'.idxOf_getElem, hlen, Nat.add_mul, Nat.one_mul]
      have : 0 < M.length := List.length_pos_iff.2 hM
      omega

end OnlineListUpdate

/-- **Online move-to-front.** For a list $M$, online move-to-front is the online list-update
algorithm on the items of $M$ whose states are the rearrangements of $M$, starting from $M$
itself: on a request $x$ that is in the current list it moves $x$ to the front, and it ignores
requests that are not in the current list. -/
def mtfOnline (M : List α) : OnlineListUpdate α M where
  State := {L : List α // L.Perm M}
  init := ⟨M, List.Perm.refl M⟩
  list q := q.1
  step q x := if hx : x ∈ q.1 then ⟨mtf q.1 x, (mtf_perm hx).trans q.2⟩ else q
  perm q := q.2

/-- **Online move-to-front pays the move-to-front cost.** Let $M$ be a list and $\sigma$ a
request sequence whose requests are all items of $M$. From any state of online move-to-front
on $M$, its access cost on $\sigma$ equals the cost of move-to-front on $\sigma$ starting from
the list of that state. -/
theorem mtfOnline_cost (M : List α) :
    ∀ (σ : List α) (q : (mtfOnline M).State), (∀ x ∈ σ, x ∈ M) →
      (mtfOnline M).cost q σ = mtfCost ((mtfOnline M).list q) σ
  | [], _, _ => rfl
  | x :: σ, q, h => by
      have hx : x ∈ (mtfOnline M).list q :=
        ((mtfOnline M).perm q).mem_iff.2 (h x List.mem_cons_self)
      simp only [OnlineListUpdate.cost, mtfCost]
      rw [mtfOnline_cost M σ _ fun y hy => h y (List.mem_cons_of_mem _ hy)]
      simp only [mtfOnline] at hx ⊢
      simp [hx]

/-- **Static cost.** The static cost of serving a request sequence $\sigma = x_0 x_1 \cdots x_{m-1}$
with a fixed list $L$ is the sum over $t < m$ of the access cost of $x_t$ in $L$, its position in
$L$ counting from $1$. -/
def staticCost (L σ : List α) : ℕ := (σ.map (accessCost L)).sum

/-- **The static cost is the offline cost of a constant list.** For every list $L$ and every
request sequence $\sigma$, the offline cost (without free exchanges) of serving $\sigma$ with the
constant sequence of lists $L, L, L, \dots$ equals the static cost of serving $\sigma$ with $L$. -/
theorem offlineCost_const (L σ : List α) : offlineCost (fun _ => L) σ = staticCost L σ := by
  induction σ with
  | nil => rfl
  | cons y σ ih => simp [offlineCost, inv_self, ih, staticCost]

/-- **Positions in a list and in its reverse.** If $L$ is a list of length $\ell$ with no
repeated entries and $x$ is an entry of $L$, then the access cost of $x$ in $L$ plus the access
cost of $x$ in the reverse of $L$ equals $\ell + 1$: the positions of $x$ in $L$ and in its
reverse, counting from $1$, add up to $\ell + 1$. -/
theorem accessCost_add_reverse {L : List α} (hnd : L.Nodup) {x : α} (hx : x ∈ L) :
    accessCost L x + accessCost L.reverse x = L.length + 1 := by
  have hi : L.idxOf x < L.length := List.idxOf_lt_length_of_mem hx
  have hrev : L.reverse[L.length - 1 - L.idxOf x]'(by simp; omega) = x := by
    rw [List.getElem_reverse]
    conv_rhs => rw [← List.getElem_idxOf hi]
    congr 1
    omega
  have := (List.nodup_reverse.2 hnd).idxOf_getElem (L.length - 1 - L.idxOf x) (by simp; omega)
  rw [hrev] at this
  simp only [accessCost, this]
  omega

/-- **A list or its reverse serves any sequence at average cost at most $(\ell + 1)/2$.** Let $L$
be a list of $\ell$ distinct items. For every request sequence $\sigma$ of $m$ items of $L$, the
static cost of serving $\sigma$ with $L$ plus the static cost of serving $\sigma$ with the reverse
of $L$ equals $m(\ell + 1)$.

In particular, one of the two static costs is at most $m(\ell + 1)/2$. -/
theorem staticCost_add_reverse {L : List α} (hnd : L.Nodup) :
    ∀ σ : List α, (∀ x ∈ σ, x ∈ L) →
      staticCost L σ + staticCost L.reverse σ = σ.length * (L.length + 1)
  | [], _ => by simp [staticCost]
  | x :: σ, h => by
      have ih := staticCost_add_reverse hnd σ fun y hy => h y (List.mem_cons_of_mem _ hy)
      have hx := accessCost_add_reverse hnd (h x List.mem_cons_self)
      simp only [staticCost, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
      rw [Nat.add_mul, Nat.one_mul]
      omega

/-- **Inversions are at most the squared length.** For any lists $M$ and $L$, the number of
inversions of $L$ against $M$ is at most $\ell^2$, where $\ell$ is the length of $M$. -/
theorem inv_le_sq (M L : List α) : inv M L ≤ M.length * M.length := by
  unfold inv invSet
  calc ((M.toFinset ×ˢ M.toFinset).filter _).card ≤ (M.toFinset ×ˢ M.toFinset).card :=
        Finset.card_filter_le _ _
    _ = M.toFinset.card * M.toFinset.card := Finset.card_product _ _
    _ ≤ M.length * M.length := Nat.mul_le_mul (List.toFinset_card_le M) (List.toFinset_card_le M)

/-- **Switching lists after the first request.** Let $M$ be a list of length $\ell$ and $R$ a list,
and write $\mathrm{inv}(M, R)$ for the number of inversions between $M$ and $R$. For every request
sequence $\sigma$ of items of $M$, the offline cost (without free exchanges) of serving $\sigma$
with the lists $M, R, R, R, \dots$ is at most $\ell + \mathrm{inv}(M, R)$ plus the static cost of
serving $\sigma$ with $R$. -/
theorem offlineCost_switch_le {M R : List α} :
    ∀ σ : List α, (∀ x ∈ σ, x ∈ M) →
      offlineCost (fun t => if t = 0 then M else R) σ ≤ M.length + inv M R + staticCost R σ
  | [], _ => by simp [offlineCost]
  | x :: σ, h => by
      have hconst : (fun t => if t + 1 = 0 then M else R) = fun _ => R := by
        funext t; simp
      simp only [offlineCost, ↓reduceIte, Nat.one_ne_zero, hconst, offlineCost_const]
      have hx : M.idxOf x < M.length := List.idxOf_lt_length_of_mem (h x List.mem_cons_self)
      simp only [accessCost, staticCost, List.map_cons, List.sum_cons]
      omega

/-- **Online and offline costs on the adversary's sequence.** Let $M$ be a nonempty list of $\ell$
distinct items, let $A$ be a deterministic online list-update algorithm on the items of $M$, let
$d$ be an item and $n$ a natural number, and let $\sigma$ be the adversary's sequence of $n$
requests against $A$ from its initial state, with default item $d$. Then the cost of $A$ on
$\sigma$ from its initial state is $n \ell$, and there are lists $L_0, L_1, L_2, \dots$, each a
rearrangement of $M$, with $L_0 = M$ such that the offline cost $C$ of this sequence of lists on
$\sigma$ satisfies $2 C \le n (\ell + 1) + 2 (\ell + \ell^2)$. -/
theorem adversary_vs_offline {M : List α} (hnd : M.Nodup) (hM : M ≠ [])
    (A : OnlineListUpdate α M) (d : α) (n : ℕ) :
    A.cost A.init (A.adversary d n A.init) = n * M.length ∧
    ∃ L : ℕ → List α, L 0 = M ∧ (∀ t, (L t).Perm M) ∧
      2 * offlineCost L (A.adversary d n A.init) ≤
        n * (M.length + 1) + 2 * (M.length + M.length * M.length) := by
  refine ⟨A.cost_adversary hnd hM n A.init, ?_⟩
  set σ := A.adversary d n A.init
  have hσ := A.adversary_mem d hM n A.init
  have hsum := staticCost_add_reverse hnd σ hσ
  rw [A.length_adversary d n A.init] at hsum
  have hrevσ : ∀ x ∈ σ, x ∈ M := hσ
  by_cases hle : staticCost M σ ≤ staticCost M.reverse σ
  · refine ⟨fun _ => M, rfl, fun _ => List.Perm.refl M, ?_⟩
    rw [offlineCost_const]
    have := Nat.zero_le (M.length + M.length * M.length)
    omega
  · refine ⟨fun t => if t = 0 then M else M.reverse, rfl, fun t => ?_, ?_⟩
    · beta_reduce
      split_ifs
      · exact List.Perm.refl M
      · exact List.reverse_perm M
    · have h1 := offlineCost_switch_le (R := M.reverse) σ hrevσ
      have h2 := inv_le_sq M M.reverse
      omega

/-- **No deterministic online list-update algorithm beats $2 - 2/(\ell + 1)$.** Let $M$ be a
nonempty list of $\ell$ distinct items and let $A$ be a deterministic online list-update
algorithm on the items of $M$. Let $c$, $d$ and $b$ be natural numbers with
$c (\ell + 1) < 2 \ell d$ (so $d \ge 1$ and $c / d < 2\ell / (\ell + 1) = 2 - 2/(\ell + 1)$).
Then there are a request sequence $\sigma$, each request an item of $M$, and lists
$L_0, L_1, L_2, \dots$, each a rearrangement of $M$, with $L_0 = M$, such that
$c \cdot C + d \cdot b < d \cdot K$, where $C$ is the offline cost without free exchanges of
$L_0, L_1, \dots$ on $\sigma$ and $K$ is the cost of $A$ on $\sigma$ from its initial state.

The offline lists make no free exchanges, so the same holds with the offline cost with free
exchanges in place of $C$.

Source: Karp and Raghavan, see Irani, *Two results on the list update problem*, IPL 38, 1991;
Borodin and El-Yaniv, Chapter 1. -/
theorem not_competitive {M : List α} (hnd : M.Nodup) (hM : M ≠ []) (A : OnlineListUpdate α M)
    {c d b : ℕ} (h : c * (M.length + 1) < 2 * M.length * d) :
    ∃ σ : List α, (∀ x ∈ σ, x ∈ M) ∧ ∃ L : ℕ → List α, L 0 = M ∧ (∀ t, (L t).Perm M) ∧
      c * offlineCost L σ + d * b < d * A.cost A.init σ := by
  obtain ⟨x0, hx0⟩ := List.exists_mem_of_ne_nil M hM
  set ℓ := M.length
  set n := 2 * c * (ℓ + ℓ * ℓ) + 2 * (d * b) + 1 with hn
  obtain ⟨hcost, L, hL0, hLp, hoff⟩ := adversary_vs_offline hnd hM A x0 n
  refine ⟨A.adversary x0 n A.init, A.adversary_mem x0 hM n A.init, L, hL0, hLp, ?_⟩
  rw [hcost]
  have p1 := Nat.mul_le_mul_left c hoff
  have p2 : n * (c * (ℓ + 1) + 1) ≤ n * (2 * ℓ * d) := Nat.mul_le_mul_left n h
  nlinarith

end Cslib.Algorithms.Lean.Online.ListUpdate
