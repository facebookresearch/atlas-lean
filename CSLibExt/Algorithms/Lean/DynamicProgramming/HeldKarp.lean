/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import CSLibExt.Algorithms.Lean.Approximation.MetricTSP
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Monoid.WithTop
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.List
public import Mathlib.Data.List.Sublists

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Rotate
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith

/-!
# Held–Karp dynamic program for the traveling salesman problem

Cities form a type `α` with decidable equality, `s : α` is the start city and
`d : α → α → R` gives the cost of travelling from one city to another, with values in a linearly
ordered additive commutative monoid `R` such as `ℤ` or `ℝ`: costs may be negative and need not be
symmetric. A path or tour is the list of the cities it visits, and its cost is the existing
`MetricTSP.pathFrom` and `MetricTSP.tourCost`. Mathlib's Hamiltonian walks
(`SimpleGraph.Walk.IsHamiltonian`) live in undirected simple graphs and visit every vertex of the
type, whereas here costs are directed and the subproblems visit a subset of the cities.

* `IsHamiltonianPath s S j L`: `s :: L` lists the cities of `S`, each once, and ends at `j`;
* `minPathCost d s S j`: the least cost `C(S, j)` of such a path, in `WithTop R` (`⊤` if none);
* `optimalTourCost d`: the least cost of a closed tour through every city exactly once;
* `heldKarp_correct`: for `s ∈ S` and `j ∈ S \ {s}`, `C(S, j)` is attained and, when `|S| ≥ 3`,
  satisfies `C(S, j) = min_{i ∈ S \ {s, j}} C(S \ {j}, i) + d i j`; `C({s, j}, j) = d s j` for
  `j ≠ s`; for at least two cities the optimal tour cost is `min_{j ≠ s} C(V, j) + d j s`, and on
  a duplicate-free list of all cities other than `s` the table-filling algorithm `solve` returns
  it in at most `n² 2ⁿ` steps, storing at most `n 2ⁿ` table entries.

## Cost model

`solve` fills a table indexed by a nonempty set `A` of cities other than `s` and a city `v ∈ A`,
level by level in `|A|`, so that the entries for `A \ {v}` are stored before those for `A`.
Its cost is a pair. The first component counts steps: one for each base entry, one for each
candidate `u` examined in a minimum (a table read, an addition and a comparison) and one for each
closing candidate. The second counts the table entries stored. Set operations, table writes and
the enumeration of the sets are not charged separately; with sets stored as bit masks, as in
Eppstein's notes, each takes constant time when `n` is at most the machine word size. For `n`
cities there are at most `n² 2ⁿ` steps and `n 2ⁿ` entries.

## References

* M. Held and R. M. Karp, *A dynamic programming approach to sequencing problems*, J. SIAM 10
  (1962), doi:10.1137/0110015.
* R. Bellman, *Dynamic programming treatment of the travelling salesman problem*, J. ACM 9
  (1962), doi:10.1145/321105.321111.
* D. Eppstein, *Exact TSP algorithm*, lecture notes, CS 163/265 Graph Algorithms, UC Irvine.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.HeldKarp

open MetricTSP

universe u v

variable {α : Type u} {R : Type v} [DecidableEq α]
  [AddCommMonoid R] [LinearOrder R] [IsOrderedAddMonoid R]

/-- **Hamiltonian path through a set of cities.** For cities $s$ and $j$, a finite set $S$ of
cities and a list $L = [x_1, \dots, x_k]$ of cities, the sequence $s, x_1, \dots, x_k$ is a path
from $s$ to $j$ that visits exactly the cities of $S$ when its entries are pairwise distinct, the
set of its entries is $S$, and its last entry ($x_k$, or $s$ when $L$ is empty) is $j$. -/
def IsHamiltonianPath (s : α) (S : Finset α) (j : α) (L : List α) : Prop :=
  (s :: L).Nodup ∧ (s :: L).toFinset = S ∧ L.getLastD s = j

instance (s : α) (S : Finset α) (j : α) : DecidablePred (IsHamiltonianPath s S j) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- **Cheapest path through a set of cities.** Let $d$ be a cost function on the cities with
values in a linearly ordered additive commutative monoid $R$. For cities $s$, $j$ and a finite set
$S$ of cities, $C(S, j)$ is the minimum, in $R \cup \{\top\}$, of
$d(s, x_1) + d(x_1, x_2) + \dots + d(x_{k-1}, x_k)$ over all lists $[x_1, \dots, x_k]$ such that
$s, x_1, \dots, x_k$ is a path from $s$ to $j$ that visits exactly the cities of $S$, each once;
it is $\top$ when there is no such path. Such a list orders $S \setminus \{s\}$, so there are
finitely many. -/
def minPathCost (d : α → α → R) (s : α) (S : Finset α) (j : α) : WithTop R :=
  (((S.erase s).val.lists.toFinset).filter (IsHamiltonianPath s S j)).inf
    fun L => ((pathFrom d s L : R) : WithTop R)

/-- **Optimal tour cost.** Let $d$ be a cost function on a finite set of cities with values in a
linearly ordered additive commutative monoid $R$. The optimal tour cost is the minimum, in
$R \cup \{\top\}$, of $d(x_1, x_2) + \dots + d(x_{n-1}, x_n) + d(x_n, x_1)$ over all lists
$[x_1, \dots, x_n]$ that contain every city exactly once: the cheapest closed tour that visits
each city once and returns to its first city. (With no cities, the empty tour costs $0$.) -/
def optimalTourCost [Fintype α] (d : α → α → R) : WithTop R :=
  ((Finset.univ : Finset α).val.lists.toFinset).inf fun H => ((tourCost d H : R) : WithTop R)

/-! ### The algorithm -/

-- The table `t` after storing `c` at `(A, v)`.
def store (t : Finset α → α → WithTop R) (A : Finset α) (v : α) (c : WithTop R) :
    Finset α → α → WithTop R :=
  fun B w => if B = A ∧ w = v then c else t B w

-- The minimum of `f` over a list, one step per element.
def minSteps (f : α → WithTop R) : List α → TimeM (ℕ × ℕ) (WithTop R)
  | [] => pure ⊤
  | w :: ws => do
    TimeM.tick (1, 0)
    let m ← minSteps f ws
    pure (min (f w) m)

-- The table entry for the set of cities of `A` and `v ∈ A`.
def entry (d : α → α → R) (s : α) (t : Finset α → α → WithTop R) (A : List α) (v : α) :
    TimeM (ℕ × ℕ) (WithTop R) :=
  if A.erase v = [] then do
    TimeM.tick (1, 0)
    pure (d s v : WithTop R)
  else minSteps (fun w => t (A.erase v).toFinset w + (d w v : WithTop R)) (A.erase v)

-- Store the entries of the set of cities of `A` at the cities of `vs`.
def fillSet (d : α → α → R) (s : α) (A : List α) :
    List α → (Finset α → α → WithTop R) → TimeM (ℕ × ℕ) (Finset α → α → WithTop R)
  | [], t => pure t
  | v :: vs, t =>
    (entry d s t A v).bind fun c =>
      (TimeM.tick (0, 1)).bind fun (_ : PUnit.{1}) => fillSet d s A vs (store t A.toFinset v c)

-- Store the entries of each set in a list of sets.
def fillLevel (d : α → α → R) (s : α) :
    List (List α) → (Finset α → α → WithTop R) → TimeM (ℕ × ℕ) (Finset α → α → WithTop R)
  | [], t => pure t
  | A :: As, t => do
    let t ← fillSet d s A A t
    fillLevel d s As t

-- Store the entries of the sets of sizes `1, …, k`.
def fillTable (d : α → α → R) (s : α) (others : List α) :
    ℕ → TimeM (ℕ × ℕ) (Finset α → α → WithTop R)
  | 0 => pure fun _ _ => ⊤
  | k + 1 => do
    let t ← fillTable d s others k
    fillLevel d s (others.sublistsLen (k + 1)) t

/-- **Held–Karp algorithm.** Let $d$ be a cost function on the cities with values in a linearly
ordered additive commutative monoid $R$, let $s$ be the start city and let `others` be a list of
distinct cities other than $s$. For $k = 1, 2, \dots$ up to the length of `others`, for each
sublist $A$ of `others` of length $k$ and each $v \in A$, the algorithm stores in a table, under
the set of cities of $A$ and $v$, the value $T(A, v) = d(s, v)$ if $A = [v]$, and otherwise the
minimum over the cities $u$ of $A$ other than $v$ of $T(A \setminus \{v\}, u) + d(u, v)$, read
from the table. It returns the minimum over the cities $v$ of `others` of
$T(\mathit{others}, v) + d(v, s)$, in $R \cup \{\top\}$. Its cost is a pair: the number of
steps, one for each base entry, one for each candidate $u$ examined in a minimum and one for each
closing candidate $v$; and the number of table entries stored. -/
def solve (d : α → α → R) (s : α) (others : List α) : TimeM (ℕ × ℕ) (WithTop R) :=
  (fillTable d s others others.length).bind fun t =>
    minSteps (fun v => t others.toFinset v + (d v s : WithTop R)) others

/-! ### Paths and their least cost -/

theorem mem_filter_lists_iff (s : α) (S : Finset α) (j : α) {L : List α} :
    L ∈ ((S.erase s).val.lists.toFinset).filter (IsHamiltonianPath s S j) ↔
      IsHamiltonianPath s S j L := by
  rw [Finset.mem_filter, Multiset.mem_toFinset, Multiset.mem_lists_iff]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  obtain ⟨hnd, hS, -⟩ := h
  rw [List.nodup_cons] at hnd
  rw [← hS, List.toFinset_cons, Finset.erase_insert (by simpa using hnd.1)]
  simp [List.toFinset_val, hnd.2.dedup]

omit [IsOrderedAddMonoid R] in
theorem minPathCost_le {d : α → α → R} {s : α} {S : Finset α} {j : α} {L : List α}
    (h : IsHamiltonianPath s S j L) : minPathCost d s S j ≤ pathFrom d s L :=
  Finset.inf_le ((mem_filter_lists_iff s S j).2 h)

omit [IsOrderedAddMonoid R] in
theorem le_minPathCost {d : α → α → R} {s : α} {S : Finset α} {j : α} {c : WithTop R}
    (h : ∀ L, IsHamiltonianPath s S j L → c ≤ pathFrom d s L) : c ≤ minPathCost d s S j :=
  Finset.le_inf fun L hL => h L ((mem_filter_lists_iff s S j).1 hL)

private theorem inf_add_coe {ι : Type*} (T : Finset ι) (f : ι → WithTop R) (c : R) :
    T.inf f + (c : WithTop R) = T.inf fun x => f x + c := by
  induction T using Finset.cons_induction with
  | empty => simp
  | cons a T ha ih =>
    rw [Finset.inf_cons, Finset.inf_cons, ← ih]
    exact (min_add_add_right _ _ _).symm

private theorem minPathCost_add (d : α → α → R) (s : α) (S : Finset α) (j : α) (c : R) :
    minPathCost d s S j + (c : WithTop R) =
      (((S.erase s).val.lists.toFinset).filter (IsHamiltonianPath s S j)).inf
        fun L => ((pathFrom d s L : R) : WithTop R) + c :=
  inf_add_coe _ _ _

omit [DecidableEq α] in
private theorem eq_concat_of_ne_nil {L : List α} (h : L ≠ []) :
    ∃ L' b, L = L' ++ [b] := by
  rcases List.eq_nil_or_concat L with h' | ⟨L', b, h'⟩
  · exact absurd h' h
  · exact ⟨L', b, by rw [h', List.concat_eq_append]⟩

theorem exists_isHamiltonianPath {s : α} {S : Finset α} {j : α} (hs : s ∈ S) (hj : j ∈ S)
    (hjs : j ≠ s) : ∃ L, IsHamiltonianPath s S j L := by
  refine ⟨(S \ {s, j}).toList ++ [j], ?_, ?_, List.getLastD_concat⟩
  · rw [← List.cons_append, List.nodup_append]
    refine ⟨?_, List.nodup_singleton j, ?_⟩
    · rw [List.nodup_cons]
      exact ⟨by simp, Finset.nodup_toList _⟩
    · intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      rcases List.mem_cons.1 ha with rfl | ha
      · exact hjs.symm
      · simp at ha
        tauto
  · ext x
    simp only [List.toFinset_cons, List.toFinset_append, List.toFinset_nil, Finset.mem_insert,
      Finset.mem_union, Finset.mem_sdiff, List.mem_toFinset, Finset.mem_toList,
      Finset.mem_singleton, insert_empty_eq]
    constructor
    · rintro (rfl | ⟨hx, -⟩ | rfl) <;> assumption
    · intro hx
      tauto

omit [IsOrderedAddMonoid R] in
theorem isLeast_minPathCost (d : α → α → R) {s : α} {S : Finset α} {j : α} (hs : s ∈ S)
    (hj : j ∈ S) (hjs : j ≠ s) :
    IsLeast ((fun L => ((pathFrom d s L : R) : WithTop R)) '' {L | IsHamiltonianPath s S j L})
      (minPathCost d s S j) := by
  obtain ⟨L₀, hL₀⟩ := exists_isHamiltonianPath hs hj hjs
  obtain ⟨L, hL, hmin⟩ := Finset.exists_mem_eq_inf _
    ⟨L₀, (mem_filter_lists_iff s S j).2 hL₀⟩ fun L => ((pathFrom d s L : R) : WithTop R)
  refine ⟨⟨L, (mem_filter_lists_iff s S j).1 hL, hmin.symm⟩, ?_⟩
  rintro _ ⟨L', hL', rfl⟩
  exact minPathCost_le hL'

omit [IsOrderedAddMonoid R] in
theorem minPathCost_pair (d : α → α → R) {s j : α} (hjs : j ≠ s) :
    minPathCost d s {s, j} j = d s j := by
  apply le_antisymm
  · have h : IsHamiltonianPath s {s, j} j [j] := ⟨by simp [hjs.symm], by simp, rfl⟩
    simpa [pathFrom] using minPathCost_le (d := d) h
  · apply le_minPathCost
    rintro L ⟨hnd, hS, -⟩
    rw [List.nodup_cons] at hnd
    have hmem : ∀ x, x ∈ L ↔ x = j := by
      intro x
      have hx := congrArg (x ∈ ·) hS
      simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset,
        Finset.mem_singleton, eq_iff_iff] at hx
      constructor
      · intro h
        have hxs : x ≠ s := fun h' => hnd.1 (h' ▸ h)
        tauto
      · rintro rfl
        exact (hx.2 (Or.inr rfl)).resolve_left hjs
    match L, hnd, hmem with
    | [], _, hmem => exact absurd ((hmem j).2 rfl) (by simp)
    | a :: L', hnd, hmem =>
      have ha : a = j := (hmem a).1 (List.mem_cons_self ..)
      subst ha
      have hL' : L' = [] := by
        refine List.eq_nil_iff_forall_not_mem.2 fun b hb => ?_
        have hb' := (hmem b).1 (List.mem_cons_of_mem _ hb)
        subst hb'
        exact (List.nodup_cons.1 hnd.2).1 hb
      subst hL'
      simp [pathFrom]

theorem isHamiltonianPath_append_singleton {s : α} {S : Finset α} {i j : α} {L : List α}
    (hj : j ∈ S) (h : IsHamiltonianPath s (S.erase j) i L) :
    IsHamiltonianPath s S j (L ++ [j]) := by
  obtain ⟨hnd, hS, -⟩ := h
  have hjL : j ∉ s :: L := fun hm => by
    have := List.mem_toFinset.2 hm
    rw [hS] at this
    simp at this
  refine ⟨?_, ?_, List.getLastD_concat⟩
  · rw [← List.cons_append, List.nodup_append]
    refine ⟨hnd, List.nodup_singleton j, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb
    subst hb
    exact fun h => hjL (h ▸ ha)
  · rw [← List.cons_append, List.toFinset_append, hS]
    simp [Finset.insert_erase hj]

theorem isHamiltonianPath_split {s : α} {S : Finset α} {j : α} {L : List α} (hjs : j ≠ s)
    (hcard : 3 ≤ S.card) (h : IsHamiltonianPath s S j L) :
    ∃ i ∈ S \ {s, j}, ∃ L', IsHamiltonianPath s (S.erase j) i L' ∧ L = L' ++ [j] := by
  obtain ⟨hnd, hS, hlast⟩ := h
  have hL : L ≠ [] := by
    rintro rfl
    exact hjs hlast.symm
  obtain ⟨L', b, rfl⟩ := eq_concat_of_ne_nil hL
  obtain rfl : b = j := by rwa [List.getLastD_concat] at hlast
  have hL' : L' ≠ [] := by
    rintro rfl
    have : S.card ≤ 2 := by
      rw [← hS]
      exact (List.toFinset_card_le _).trans (by simp)
    omega
  obtain ⟨L'', i, rfl⟩ := eq_concat_of_ne_nil hL'
  have h3 : [s, i, b].Nodup := hnd.sublist (List.Sublist.cons_cons s (by
    rw [List.append_assoc]
    exact List.sublist_append_right L'' [i, b]))
  have hsi : s ≠ i := by
    rintro rfl
    simp at h3
  have hib : i ≠ b := by
    rintro rfl
    simp at h3
  have hnd2 : ((s :: (L'' ++ [i])) ++ [b]).Nodup := by rwa [List.cons_append]
  have hS2 : ((s :: (L'' ++ [i])) ++ [b]).toFinset = S := by rwa [List.cons_append]
  rw [List.nodup_append] at hnd2
  have hbL : ∀ x ∈ s :: (L'' ++ [i]), x ≠ b := fun x hx =>
    hnd2.2.2 x hx b (List.mem_singleton_self _)
  refine ⟨i, ?_, L'' ++ [i], ⟨hnd2.1, ?_, List.getLastD_concat⟩, rfl⟩
  · rw [Finset.mem_sdiff, ← hS2]
    refine ⟨by simp, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hsi h.symm, hib⟩
  · ext x
    rw [Finset.mem_erase, ← hS2, List.mem_toFinset, List.mem_toFinset, List.mem_append,
      List.mem_singleton]
    constructor
    · intro hx
      exact ⟨hbL x hx, Or.inl hx⟩
    · rintro ⟨hxb, hx | rfl⟩
      · exact hx
      · exact absurd rfl hxb

theorem minPathCost_eq_inf (d : α → α → R) {s : α} {S : Finset α} {j : α} (hj : j ∈ S)
    (hjs : j ≠ s) (hcard : 3 ≤ S.card) :
    minPathCost d s S j = (S \ {s, j}).inf fun i => minPathCost d s (S.erase j) i + d i j := by
  apply le_antisymm
  · refine Finset.le_inf fun i _ => ?_
    rw [minPathCost_add]
    refine Finset.le_inf fun L hL => ?_
    rw [mem_filter_lists_iff] at hL
    have h := minPathCost_le (d := d) (isHamiltonianPath_append_singleton hj hL)
    rw [pathFrom_append, hL.2.2] at h
    simpa [pathFrom] using h
  · refine le_minPathCost fun L hL => ?_
    obtain ⟨i, hi, L', hL', rfl⟩ := isHamiltonianPath_split hjs hcard hL
    calc (S \ {s, j}).inf (fun i => minPathCost d s (S.erase j) i + d i j)
        ≤ minPathCost d s (S.erase j) i + d i j := Finset.inf_le hi
      _ ≤ pathFrom d s L' + d i j := add_le_add_left (minPathCost_le hL') _
      _ = pathFrom d s (L' ++ [j]) := by
        rw [pathFrom_append, hL'.2.2]
        simp [pathFrom]

/-! ### Tours -/

omit [DecidableEq α] [LinearOrder R] [IsOrderedAddMonoid R] in
private theorem tourCost_rotate_one (d : α → α → R) :
    ∀ l : List α, tourCost d (l.rotate 1) = tourCost d l
  | [] => rfl
  | [_] => by simp
  | h :: a :: t => by
    rw [List.rotate_cons_succ, List.rotate_zero]
    simp only [tourCost, List.cons_append, pathFrom]
    rw [pathFrom_append d a (t ++ [h]) [a], List.getLastD_concat]
    simp [pathFrom, add_comm]

omit [DecidableEq α] [LinearOrder R] [IsOrderedAddMonoid R] in
theorem tourCost_rotate (d : α → α → R) (l : List α) :
    ∀ n, tourCost d (l.rotate n) = tourCost d l
  | 0 => by rw [List.rotate_zero]
  | n + 1 => by rw [← List.rotate_rotate, tourCost_rotate_one, tourCost_rotate d l n]

theorem mem_lists_univ_iff [Fintype α] {H : List α} :
    H ∈ (Finset.univ : Finset α).val.lists.toFinset ↔ H.Nodup ∧ ∀ x, x ∈ H := by
  rw [Multiset.mem_toFinset, Multiset.mem_lists_iff]
  change Finset.univ.val = (H : Multiset α) ↔ _
  constructor
  · intro h
    refine ⟨Multiset.coe_nodup.1 (h ▸ Finset.univ.nodup), fun x => ?_⟩
    rw [← Multiset.mem_coe, ← h]
    exact Finset.mem_univ x
  · rintro ⟨hnd, hall⟩
    exact (Multiset.Nodup.ext Finset.univ.nodup (Multiset.coe_nodup.2 hnd)).2
      fun x => by simp [hall x]

theorem optimalTourCost_eq_inf [Fintype α] (d : α → α → R) (s : α)
    (hn : 2 ≤ Fintype.card α) :
    optimalTourCost d =
      (Finset.univ.erase s).inf fun j => minPathCost d s Finset.univ j + d j s := by
  apply le_antisymm
  · refine Finset.le_inf fun j _ => ?_
    rw [minPathCost_add]
    refine Finset.le_inf fun L hL => ?_
    obtain ⟨hnd, hS, hlast⟩ := (mem_filter_lists_iff s _ j).1 hL
    have hmem : s :: L ∈ (Finset.univ : Finset α).val.lists.toFinset :=
      mem_lists_univ_iff.2 ⟨hnd, fun x => List.mem_toFinset.1 (hS ▸ Finset.mem_univ x)⟩
    calc optimalTourCost d ≤ tourCost d (s :: L) := Finset.inf_le hmem
      _ = pathFrom d s L + d j s := by
        simp only [tourCost]
        rw [pathFrom_append d s L [s], hlast]
        simp [pathFrom]
  · refine Finset.le_inf fun H hH => ?_
    obtain ⟨hnd, hall⟩ := mem_lists_univ_iff.1 hH
    obtain ⟨A, B, rfl⟩ := List.append_of_mem (hall s)
    rw [← tourCost_rotate d (A ++ s :: B) A.length, List.rotate_append_length_eq]
    have hperm : (s :: (B ++ A)).Perm (A ++ s :: B) := by
      rw [← List.cons_append]
      exact List.perm_append_comm
    have hnd' : (s :: (B ++ A)).Nodup := hperm.nodup_iff.2 hnd
    have hall' : ∀ x, x ∈ s :: (B ++ A) := fun x => hperm.mem_iff.2 (hall x)
    obtain ⟨j, hjs⟩ := Fintype.exists_ne_of_one_lt_card (by omega) s
    have hne : B ++ A ≠ [] := by
      intro h
      have := hall' j
      rw [h] at this
      simp [hjs] at this
    obtain ⟨L', i, hL'⟩ := eq_concat_of_ne_nil hne
    have hlast : (B ++ A).getLastD s = i := by rw [hL', List.getLastD_concat]
    have his : i ≠ s := by
      rintro rfl
      exact (List.nodup_cons.1 hnd').1 (hL' ▸ List.mem_append_right _ (List.mem_singleton_self _))
    have hpath : IsHamiltonianPath s Finset.univ i (B ++ A) :=
      ⟨hnd', by ext x; simpa using hall' x, hlast⟩
    calc (Finset.univ.erase s).inf (fun j => minPathCost d s Finset.univ j + d j s)
        ≤ minPathCost d s Finset.univ i + d i s := Finset.inf_le (by simp [his])
      _ ≤ pathFrom d s (B ++ A) + d i s := add_le_add_left (minPathCost_le hpath) _
      _ = tourCost d (s :: (B ++ A)) := by
        simp only [tourCost]
        rw [pathFrom_append d s (B ++ A) [s], hlast]
        simp [pathFrom]

/-! ### Correctness of the algorithm -/

omit [DecidableEq α] [AddCommMonoid R] [IsOrderedAddMonoid R] in
theorem minSteps_ret [DecidableEq α] (f : α → WithTop R) (l : List α) :
    (minSteps f l).ret = l.toFinset.inf f := by
  induction l with
  | nil => rfl
  | cons w ws ih =>
    simp only [minSteps, TimeM.ret_bind, TimeM.ret_pure, ih, List.toFinset_cons,
      Finset.inf_insert]

omit [DecidableEq α] [AddCommMonoid R] [IsOrderedAddMonoid R] in
theorem minSteps_time (f : α → WithTop R) (l : List α) :
    (minSteps f l).time = (l.length, 0) := by
  induction l with
  | nil => rfl
  | cons w ws ih =>
    simp only [minSteps, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, ih,
      Prod.mk_add_mk, add_zero, List.length_cons]
    rw [add_comm 1]

omit [DecidableEq α] [AddCommMonoid R] [LinearOrder R] [IsOrderedAddMonoid R] in
@[simp] private theorem bind_ret {T β γ : Type*} [Add T] (m : TimeM T β) (f : β → TimeM T γ) :
    (m.bind f).ret = (f m.ret).ret := rfl

omit [DecidableEq α] [AddCommMonoid R] [LinearOrder R] [IsOrderedAddMonoid R] in
@[simp] private theorem bind_time {T β γ : Type*} [Add T] (m : TimeM T β)
    (f : β → TimeM T γ) : (m.bind f).time = m.time + (f m.ret).time := rfl

private def Agrees (d : α → α → R) (s : α) (t : Finset α → α → WithTop R) (A : Finset α)
    (v : α) : Prop :=
  t A v = minPathCost d s (insert s A) v

private def Filled (d : α → α → R) (s : α) (others : List α) (t : Finset α → α → WithTop R)
    (k : ℕ) : Prop :=
  ∀ A : List α, A.Sublist others → A ≠ [] → A.length ≤ k → ∀ v ∈ A, Agrees d s t A.toFinset v

omit [IsOrderedAddMonoid R] in
private theorem agrees_store {d : α → α → R} {s : α} {t : Finset α → α → WithTop R}
    {A : Finset α} {v : α} {c : WithTop R} (hc : c = minPathCost d s (insert s A) v)
    {B : Finset α} {w : α} (h : Agrees d s t B w) : Agrees d s (store t A v c) B w := by
  unfold Agrees store at *
  split_ifs with hBw
  · obtain ⟨rfl, rfl⟩ := hBw
    exact hc
  · exact h

omit [IsOrderedAddMonoid R] in
private theorem agrees_store_self {d : α → α → R} {s : α} {t : Finset α → α → WithTop R}
    {A : Finset α} {v : α} {c : WithTop R} (hc : c = minPathCost d s (insert s A) v) :
    Agrees d s (store t A v c) A v := by
  simp [Agrees, store, hc]

private theorem entry_ret (d : α → α → R) {s : α} {others : List α} (hothers : others.Nodup)
    (hs : s ∉ others) {t : Finset α → α → WithTop R} {A : List α} {v : α}
    (hA : A.Sublist others) (hv : v ∈ A) (hfill : Filled d s others t (A.length - 1)) :
    (entry d s t A v).ret = minPathCost d s (insert s A.toFinset) v := by
  have hAnd : A.Nodup := hothers.sublist hA
  have hsA : s ∉ A := fun h => hs (hA.subset h)
  have hvs : v ≠ s := fun h => hsA (h ▸ hv)
  unfold entry
  split_ifs with hB
  · have hlen := List.length_erase_of_mem hv
    rw [hB, List.length_nil] at hlen
    match A, hv, hlen with
    | [a], hv, _ =>
      rw [List.mem_singleton] at hv
      subst hv
      simp only [TimeM.ret_bind, TimeM.ret_pure, List.toFinset_cons, List.toFinset_nil,
        insert_empty_eq]
      exact (minPathCost_pair d hvs).symm
    | [], hv, _ => simp at hv
    | _ :: _ :: _, _, hlen => simp at hlen
  · rw [minSteps_ret]
    have hBsub : (A.erase v).Sublist others := List.erase_sublist.trans hA
    have hBlen : (A.erase v).length = A.length - 1 := List.length_erase_of_mem hv
    have hBpos : 0 < (A.erase v).length := List.length_pos_iff.2 hB
    rw [Finset.inf_congr rfl fun w hw => by
      rw [hfill _ hBsub hB hBlen.le w (List.mem_toFinset.1 hw)]]
    have hcard : 3 ≤ (insert s A.toFinset).card := by
      rw [Finset.card_insert_of_notMem (by simpa using hsA), List.toFinset_card_of_nodup hAnd]
      omega
    rw [minPathCost_eq_inf d (by simp [hv]) hvs hcard, Finset.erase_insert_of_ne hvs.symm]
    have hset : A.toFinset.erase v = (A.erase v).toFinset := by
      ext x
      simp [hAnd.mem_erase_iff]
    have hsdiff : insert s A.toFinset \ {s, v} = (A.erase v).toFinset := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert, List.mem_toFinset, Finset.mem_singleton,
        not_or, hAnd.mem_erase_iff]
      constructor
      · rintro ⟨rfl | hx, hxs, hxv⟩
        · exact absurd rfl hxs
        · exact ⟨hxv, hx⟩
      · rintro ⟨hxv, hx⟩
        exact ⟨Or.inr hx, fun h => hsA (h ▸ hx), hxv⟩
    rw [hset, hsdiff]

private theorem fillSet_spec (d : α → α → R) {s : α} {others : List α} (hothers : others.Nodup)
    (hs : s ∉ others) {A : List α} (hA : A.Sublist others) :
    ∀ (vs : List α) (t : Finset α → α → WithTop R), (∀ v ∈ vs, v ∈ A) →
      Filled d s others t (A.length - 1) →
      (∀ B w, Agrees d s t B w → Agrees d s (fillSet d s A vs t).ret B w) ∧
        ∀ v ∈ vs, Agrees d s (fillSet d s A vs t).ret A.toFinset v
  | [], _, _, _ => ⟨fun _ _ h => h, by simp⟩
  | v :: vs, t, hvs, hfill => by
    simp only [fillSet, bind_ret]
    have hc := entry_ret d hothers hs hA (hvs v (List.mem_cons_self ..)) hfill
    have hfill' : Filled d s others (store t A.toFinset v (entry d s t A v).ret)
        (A.length - 1) := fun B hB hne hlen w hw => agrees_store hc (hfill B hB hne hlen w hw)
    obtain ⟨h₁, h₂⟩ := fillSet_spec d hothers hs hA vs _
      (fun w hw => hvs w (List.mem_cons_of_mem _ hw)) hfill'
    refine ⟨fun B w h => h₁ B w (agrees_store hc h), fun w hw => ?_⟩
    rcases List.mem_cons.1 hw with rfl | hw
    · exact h₁ _ _ (agrees_store_self hc)
    · exact h₂ w hw

private theorem fillLevel_spec (d : α → α → R) {s : α} {others : List α}
    (hothers : others.Nodup) (hs : s ∉ others) (k : ℕ) :
    ∀ (As : List (List α)) (t : Finset α → α → WithTop R),
      (∀ A ∈ As, A.Sublist others ∧ A.length = k + 1) → Filled d s others t k →
      (∀ B w, Agrees d s t B w → Agrees d s (fillLevel d s As t).ret B w) ∧
        ∀ A ∈ As, ∀ v ∈ A, Agrees d s (fillLevel d s As t).ret A.toFinset v
  | [], _, _, _ => ⟨fun _ _ h => h, by simp⟩
  | A :: As, t, hAs, hfill => by
    simp only [fillLevel, TimeM.ret_bind]
    obtain ⟨hA, hlen⟩ := hAs A (List.mem_cons_self ..)
    obtain ⟨h₁, h₂⟩ := fillSet_spec d hothers hs hA A t (fun _ h => h) (by rwa [hlen])
    have hfill' : Filled d s others (fillSet d s A A t).ret k :=
      fun B hB hne hl w hw => h₁ _ _ (hfill B hB hne hl w hw)
    obtain ⟨h₃, h₄⟩ := fillLevel_spec d hothers hs k As _
      (fun B hB => hAs B (List.mem_cons_of_mem _ hB)) hfill'
    refine ⟨fun B w h => h₃ B w (h₁ B w h), fun B hB v hv => ?_⟩
    rcases List.mem_cons.1 hB with rfl | hB
    · exact h₃ _ _ (h₂ v hv)
    · exact h₄ B hB v hv

private theorem fillTable_filled (d : α → α → R) {s : α} {others : List α}
    (hothers : others.Nodup) (hs : s ∉ others) :
    ∀ k, Filled d s others (fillTable d s others k).ret k
  | 0 => fun A _ hne hlen => absurd (List.length_eq_zero_iff.1 (by omega)) hne
  | k + 1 => by
    simp only [fillTable, TimeM.ret_bind]
    have hfill := fillTable_filled d hothers hs k
    obtain ⟨h₁, h₂⟩ := fillLevel_spec d hothers hs k (others.sublistsLen (k + 1)) _
      (fun A hA => List.mem_sublistsLen.1 hA) hfill
    intro A hA hne hlen v hv
    rcases Nat.lt_or_ge A.length (k + 1) with hlt | hge
    · exact h₁ _ _ (hfill A hA hne (by omega) v hv)
    · exact h₂ A (List.mem_sublistsLen.2 ⟨hA, by omega⟩) v hv

omit [DecidableEq α] in
private theorem card_eq_length_add_one [Fintype α] {s : α} {others : List α}
    (hothers : others.Nodup) (hs : s ∉ others) (hall : ∀ x, x ≠ s → x ∈ others) :
    Fintype.card α = others.length + 1 := by
  classical
  have huniv : (s :: others).toFinset = Finset.univ := by
    ext x
    by_cases hx : x = s <;> simp [hx, hall]
  rw [← Finset.card_univ, ← huniv, List.toFinset_card_of_nodup (List.nodup_cons.2 ⟨hs, hothers⟩),
    List.length_cons]

theorem solve_ret [Fintype α] (d : α → α → R) {s : α} (hn : 2 ≤ Fintype.card α)
    {others : List α} (hothers : others.Nodup) (hs : s ∉ others)
    (hall : ∀ x, x ≠ s → x ∈ others) :
    (solve d s others).ret = optimalTourCost d := by
  have hcard := card_eq_length_add_one hothers hs hall
  have hne : others ≠ [] := by
    rintro rfl
    simp at hcard
    omega
  simp only [solve, bind_ret]
  rw [minSteps_ret]
  have hfill := fillTable_filled d hothers hs others.length
  rw [Finset.inf_congr rfl fun v hv => by
    rw [hfill others (List.Sublist.refl _) hne le_rfl v (List.mem_toFinset.1 hv)]]
  have h₁ : insert s others.toFinset = Finset.univ := by
    ext x
    by_cases hx : x = s <;> simp [hx, hall]
  have h₂ : others.toFinset = Finset.univ.erase s := by
    ext x
    by_cases hx : x = s
    · subst hx
      simp [hs]
    · simp [hx, hall]
  rw [h₁, h₂, optimalTourCost_eq_inf d s hn]

/-! ### Cost of the algorithm -/

omit [IsOrderedAddMonoid R] in
theorem entry_time (d : α → α → R) (s : α) (t : Finset α → α → WithTop R) {A : List α} {v : α}
    (hv : v ∈ A) : (entry d s t A v).time = (max 1 (A.length - 1), 0) := by
  have hlen := List.length_erase_of_mem hv
  have hpos : 0 < A.length := List.length_pos_of_mem hv
  unfold entry
  split_ifs with hB
  · rw [hB, List.length_nil] at hlen
    simp only [TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, add_zero]
    rw [← hlen]
    rfl
  · rw [minSteps_time, hlen]
    have : 0 < (A.erase v).length := List.length_pos_iff.2 hB
    rw [max_eq_right (by omega)]

omit [IsOrderedAddMonoid R] in
theorem fillSet_time (d : α → α → R) (s : α) (A : List α) :
    ∀ (vs : List α) (t : Finset α → α → WithTop R), (∀ v ∈ vs, v ∈ A) →
      (fillSet d s A vs t).time = (vs.length * max 1 (A.length - 1), vs.length)
  | [], _, _ => by simp [fillSet]; rfl
  | v :: vs, t, hvs => by
    simp only [fillSet, bind_time, TimeM.time_tick]
    rw [entry_time d s t (hvs v (List.mem_cons_self ..)),
      fillSet_time d s A vs _ fun w hw => hvs w (List.mem_cons_of_mem _ hw)]
    simp only [Prod.mk_add_mk, List.length_cons, Prod.mk.injEq]
    constructor <;> ring

omit [IsOrderedAddMonoid R] in
theorem fillLevel_time (d : α → α → R) (s : α) (k : ℕ) :
    ∀ (As : List (List α)) (t : Finset α → α → WithTop R), (∀ A ∈ As, A.length = k) →
      (fillLevel d s As t).time = (As.length * (k * max 1 (k - 1)), As.length * k)
  | [], _, _ => by simp [fillLevel]; rfl
  | A :: As, t, hAs => by
    simp only [fillLevel, TimeM.time_bind]
    have hA := hAs A (List.mem_cons_self ..)
    rw [fillSet_time d s A A t fun _ h => h,
      fillLevel_time d s k As _ fun B hB => hAs B (List.mem_cons_of_mem _ hB), hA]
    simp only [Prod.mk_add_mk, List.length_cons, Prod.mk.injEq]
    constructor <;> ring

omit [IsOrderedAddMonoid R] in
theorem fillTable_time (d : α → α → R) (s : α) (others : List α) :
    ∀ k, (fillTable d s others k).time =
      (∑ i ∈ Finset.range k, others.length.choose (i + 1) * ((i + 1) * max 1 i),
        ∑ i ∈ Finset.range k, others.length.choose (i + 1) * (i + 1))
  | 0 => rfl
  | k + 1 => by
    simp only [fillTable, TimeM.time_bind]
    rw [fillTable_time d s others k,
      fillLevel_time d s (k + 1) _ _ fun A hA => (List.mem_sublistsLen.1 hA).2,
      List.length_sublistsLen, Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [Prod.mk_add_mk, Nat.add_sub_cancel]

omit [IsOrderedAddMonoid R] in
theorem solve_time (d : α → α → R) (s : α) (others : List α) :
    (solve d s others).time =
      (others.length + ∑ i ∈ Finset.range others.length,
          others.length.choose (i + 1) * ((i + 1) * max 1 i),
        ∑ i ∈ Finset.range others.length, others.length.choose (i + 1) * (i + 1)) := by
  simp only [solve, bind_time]
  rw [fillTable_time, minSteps_time]
  simp only [Prod.mk_add_mk, add_zero, Prod.mk.injEq, and_true]
  rw [add_comm]

private theorem sum_choose_succ_le (m : ℕ) :
    ∑ i ∈ Finset.range m, m.choose (i + 1) ≤ 2 ^ m := by
  have h := Nat.sum_range_choose m
  rw [Finset.sum_range_succ'] at h
  omega

private theorem steps_le (m : ℕ) :
    m + ∑ i ∈ Finset.range m, m.choose (i + 1) * ((i + 1) * max 1 i) ≤
      (m + 1) ^ 2 * 2 ^ (m + 1) := by
  have hsum : ∑ i ∈ Finset.range m, m.choose (i + 1) * ((i + 1) * max 1 i) ≤
      ∑ i ∈ Finset.range m, m.choose (i + 1) * (m * m) := by
    refine Finset.sum_le_sum fun i hi => Nat.mul_le_mul_left _ ?_
    rw [Finset.mem_range] at hi
    exact Nat.mul_le_mul (by omega) (max_le (by omega) (by omega))
  rw [← Finset.sum_mul] at hsum
  have h2 := Nat.mul_le_mul_right (m * m) (sum_choose_succ_le m)
  have hpow : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hm : m ≤ 2 ^ m * m := by simpa using Nat.mul_le_mul_right m hpow
  have key : m + 2 ^ m * (m * m) ≤ (m + 1) ^ 2 * 2 ^ (m + 1) := by
    rw [pow_succ 2 m]
    generalize 2 ^ m = p at hpow hm ⊢
    nlinarith
  omega

private theorem entries_le (m : ℕ) :
    ∑ i ∈ Finset.range m, m.choose (i + 1) * (i + 1) ≤ (m + 1) * 2 ^ (m + 1) := by
  have hsum : ∑ i ∈ Finset.range m, m.choose (i + 1) * (i + 1) ≤
      ∑ i ∈ Finset.range m, m.choose (i + 1) * m := by
    refine Finset.sum_le_sum fun i hi => Nat.mul_le_mul_left _ ?_
    rw [Finset.mem_range] at hi
    omega
  rw [← Finset.sum_mul] at hsum
  have h2 := Nat.mul_le_mul_right m (sum_choose_succ_le m)
  have key : 2 ^ m * m ≤ (m + 1) * 2 ^ (m + 1) := by
    rw [pow_succ 2 m]
    generalize 2 ^ m = p
    nlinarith
  omega

/-! ### The Held–Karp theorem -/

/-- **Held–Karp dynamic program for the traveling salesman problem.** Let $V$ be a finite set of
$n \ge 2$ cities with a start city $s$, and let $d$ be a cost function on $V$ with values in a
linearly ordered additive commutative monoid $R$ (such as $\mathbb{Z}$ or $\mathbb{R}$; $d$ need
not be symmetric or nonnegative). For a set $S$ of cities and a city $j$, let $C(S, j)$ be the
minimum, in $R \cup \{\top\}$, of the costs of the paths that start at $s$, visit exactly the
cities of $S$, each once, and end at $j$. Then:

1. if $s \in S$ and $j \in S \setminus \{s\}$, some such path exists and $C(S, j)$ is the least
   cost of such a path;
2. $C(\{s, j\}, j) = d(s, j)$ for every city $j \ne s$;
3. if $s \in S$, $j \in S \setminus \{s\}$ and $|S| \ge 3$, then
   $C(S, j) = \min_{i \in S \setminus \{s, j\}} \bigl(C(S \setminus \{j\}, i) + d(i, j)\bigr)$;
4. the optimal tour cost, the least cost of a closed tour that visits every city exactly once, is
   $\min_{j \in V \setminus \{s\}} \bigl(C(V, j) + d(j, s)\bigr)$;
5. for every list of the cities other than $s$, each listed once, the Held–Karp algorithm that
   fills the table of $C$ level by level returns the optimal tour cost, in at most $n^2 2^n$ steps
   and storing at most $n 2^n$ table entries. -/
theorem heldKarp_correct [Fintype α] (d : α → α → R) (s : α) (hn : 2 ≤ Fintype.card α) :
    (∀ S j, s ∈ S → j ∈ S → j ≠ s →
      IsLeast ((fun L => ((pathFrom d s L : R) : WithTop R)) '' {L | IsHamiltonianPath s S j L})
        (minPathCost d s S j)) ∧
    (∀ j, j ≠ s → minPathCost d s {s, j} j = d s j) ∧
    (∀ S j, s ∈ S → j ∈ S → j ≠ s → 3 ≤ S.card →
      minPathCost d s S j = (S \ {s, j}).inf fun i => minPathCost d s (S.erase j) i + d i j) ∧
    optimalTourCost d =
      (Finset.univ.erase s).inf (fun j => minPathCost d s Finset.univ j + d j s) ∧
    ∀ others : List α, others.Nodup → s ∉ others → (∀ x, x ≠ s → x ∈ others) →
      (solve d s others).ret = optimalTourCost d ∧
      (solve d s others).time.1 ≤ Fintype.card α ^ 2 * 2 ^ Fintype.card α ∧
      (solve d s others).time.2 ≤ Fintype.card α * 2 ^ Fintype.card α := by
  refine ⟨fun S j hs hj hjs => isLeast_minPathCost d hs hj hjs,
    fun j hjs => minPathCost_pair d hjs,
    fun S j _ hj hjs hcard => minPathCost_eq_inf d hj hjs hcard,
    optimalTourCost_eq_inf d s hn, fun others hothers hs hall => ?_⟩
  have hcard := card_eq_length_add_one hothers hs hall
  refine ⟨solve_ret d hn hothers hs hall, ?_, ?_⟩
  · rw [solve_time, hcard]
    exact steps_le _
  · rw [solve_time, hcard]
    exact entries_le _

end Cslib.Algorithms.Lean.HeldKarp
