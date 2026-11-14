/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.HamPath

/-!
# SAT ≤ HAMPATH: the forward direction

Component of the SAT ≤ HAMPATH reduction specified in
`CSLibExt.Computability.Complexity.Karp.HamPath` (Sipser, Theorem 7.46): a satisfiable formula
gives a Hamiltonian path of its construction, `exists_isHamPath_of_cnfSat`.

Fix a satisfying assignment `σ` and, for every clause `j`, a diamond `c j` whose variable has a
literal of clause `j` true under `σ`. The path visits the diamonds in order. Diamond `i` runs its
row left to right when `σ` makes its variable true and right to left otherwise, and it picks up
every clause `j` with `c j = i` between the two vertices of the pair of `j`.

* `hfRow m i c`: the row of diamond `i` left to right, with clause `j` inserted after
  `hpR m i (3 j + 1)` when `c j = i`. A right-to-left traversal is its reverse: the reversed row
  visits `hpR m i (3 j + 2)`, `j`, `hpR m i (3 j + 1)`, the detour of a negative literal.
* `hfPath m k c d`: the path through `k` diamonds, `d i` the direction of diamond `i`.
* `hfPath_perm`: `hfPath` lists `0, …, hpT m k` once each, when `c` sends every clause to a
  diamond; this gives `Nodup`, the length and the vertex bounds.
* `isChain_hfPath`, `isChain_hfDiamond`, `isChain_hfRow`: consecutive vertices are related by
  any relation that holds on the frame, row and detour arcs used.
-/

@[expose] public section

namespace Cslib.Complexity.Karp

open Cslib.CookLevin Cslib.Logic.PL
open scoped List

/-! ### The path -/

/-- **The row of a diamond with its clauses inserted.** Let $m$ and $i$ be natural numbers and
$c : \mathbb{N} \to \mathbb{N}$ a map, and write $r_l = m + i(3m + 2) + 1 + l$ for the row
vertices of diamond $i$. The row of diamond $i$ for $c$ is the list $r_0, r_1, \dots, r_{3m}$ in
which, for every $j < m$ with $c(j) = i$, the clause vertex $j$ is inserted right after
$r_{3j+1}$. -/
def hfRow (m i : ℕ) (c : ℕ → ℕ) : List ℕ :=
  (List.range (3 * m + 1)).flatMap fun l =>
    hpR m i l :: if l % 3 = 1 ∧ c (l / 3) = i then [l / 3] else []

/-- **Clauses picked up by a diamond.** For natural numbers $m$ and $i$ and a map
$c : \mathbb{N} \to \mathbb{N}$, the clauses picked up by diamond $i$ are the list of all
$j < m$ with $c(j) = i$, in increasing order.

These are the clause vertices of the row of diamond $i$, in row order. -/
def hfPicks (m i : ℕ) (c : ℕ → ℕ) : List ℕ :=
  (List.range (3 * m + 1)).flatMap fun l => if l % 3 = 1 ∧ c (l / 3) = i then [l / 3] else []

/-- **The visit of a diamond.** For $m$ clauses, a diamond $i$, a clause-to-diamond map $c$ and
a direction $b$, the visit of diamond $i$ is the list consisting of its top
$T_i = m + i(3m+2)$ followed by its row with the clauses sent to $i$ by $c$ inserted, read left
to right if $b$ is true and right to left otherwise. -/
def hfDiamond (m i : ℕ) (c : ℕ → ℕ) (b : Bool) : List ℕ :=
  hpT m i :: if b then hfRow m i c else (hfRow m i c).reverse

/-- **The forward path through the diamonds.** Let $m$ and $k$ be natural numbers, let
$c : \mathbb{N} \to \mathbb{N}$ be a map and let $d : \mathbb{N} \to \{\mathrm{true},
\mathrm{false}\}$ give each diamond $i$ a direction $d(i)$. The forward path through the first
$k$ diamonds is the list obtained by concatenating, for $i = 0, 1, \dots, k - 1$ in this order,
the traversal of diamond $i$ for $c$ in direction $d(i)$, and then appending the vertex
$m + k(3m + 2)$, the top of diamond $k$. Here the traversal of diamond $i$ is its top
$m + i(3m + 2)$ followed by its row $r_0, r_1, \dots, r_{3m}$, where
$r_l = m + i(3m + 2) + 1 + l$ and the clause vertex $j$ is inserted right after $r_{3j+1}$ for
every $j < m$ with $c(j) = i$; the row is read left to right if $d(i)$ is true and right to left
otherwise. -/
def hfPath (m k : ℕ) (c : ℕ → ℕ) (d : ℕ → Bool) : List ℕ :=
  (List.range k).flatMap (fun i => hfDiamond m i c (d i)) ++ [hpT m k]

/-! ### Vertex bookkeeping -/

/-- **Clause vertices picked up by a row.** Let $m$ and $i$ be natural numbers and let
$c : \mathbb{N} \to \mathbb{N}$. A natural number $v$ is one of the clause vertices picked up by the
row of diamond $i$ under $c$, for $m$ clauses, if and only if $v < m$ and $c(v) = i$. -/
theorem mem_hfPicks {m i v : ℕ} {c : ℕ → ℕ} : v ∈ hfPicks m i c ↔ v < m ∧ c v = i := by
  simp only [hfPicks, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨l, hl, hv⟩
    split at hv
    · next h =>
      rw [List.mem_singleton] at hv
      subst hv
      exact ⟨by omega, h.2⟩
    · simp at hv
  · rintro ⟨hv, rfl⟩
    have h1 : (3 * v + 1) % 3 = 1 := by omega
    have h2 : (3 * v + 1) / 3 = v := by omega
    exact ⟨3 * v + 1, by omega, by simp [h1, h2]⟩

/-- **The clause vertices of a row are distinct.** For all natural numbers $m$, $i$ and every
function $c : \mathbb{N} \to \mathbb{N}$, the list of clause vertices picked up by the row of
diamond $i$ under $c$, for $m$ clauses, has no repeated entries. -/
theorem nodup_hfPicks (m i : ℕ) (c : ℕ → ℕ) : (hfPicks m i c).Nodup := by
  refine List.nodup_flatMap.2 ⟨fun l _ => ?_, List.pairwise_lt_range.imp fun {l l'} hll' => ?_⟩
  · split <;> simp
  · intro v hv hv'
    simp only at hv hv'
    split at hv
    · next h =>
      split at hv'
      · next h' =>
        rw [List.mem_singleton] at hv hv'
        omega
      · simp at hv'
    · simp at hv

/-- **Each clause is picked up by exactly one row.** Let $m, k$ be natural numbers and let $c$
send every clause $j < m$ to a diamond $c(j) < k$. For each diamond $i$, list the clauses
$j < m$ with $c(j) = i$ in increasing order (the clause vertices picked up by the row of
diamond $i$). Concatenating these lists for $i = 0, \dots, k - 1$ gives a permutation of
$0, 1, \dots, m - 1$. -/
theorem flatMap_hfPicks_perm {m k : ℕ} {c : ℕ → ℕ} (hc : ∀ j < m, c j < k) :
    (List.range k).flatMap (fun i => hfPicks m i c) ~ List.range m := by
  refine (List.perm_ext_iff_of_nodup ?_ List.nodup_range).2 fun j => ?_
  · refine List.nodup_flatMap.2 ⟨fun i _ => nodup_hfPicks m i c,
      List.pairwise_lt_range.imp fun {i i'} hii' => ?_⟩
    intro v hv hv'
    rw [mem_hfPicks] at hv hv'
    omega
  · simp only [List.mem_flatMap, List.mem_range, mem_hfPicks]
    constructor
    · rintro ⟨i, -, hj, -⟩
      exact hj
    · intro hj
      exact ⟨c j, hc j hj, hj, rfl⟩

/-- **The vertices of a diamond row.** For natural numbers $m$ and $i$ and a map
$c : \mathbb{N} \to \mathbb{N}$, let $r = m + i(3m + 2) + 1$ be the left end of the row of
diamond $i$. The row of diamond $i$ for $c$ (with its clause vertices inserted) is a permutation
of the concatenation of the list $r, r + 1, \dots, r + 3m$ and the list of clauses picked up by
diamond $i$ for $c$, that is, of all $j < m$ with $c(j) = i$ in increasing order. -/
theorem hfRow_perm (m i : ℕ) (c : ℕ → ℕ) :
    hfRow m i c ~ List.range' (hpR m i 0) (3 * m + 1) ++ hfPicks m i c := by
  have h1 : (List.range (3 * m + 1)).flatMap (fun l => [hpR m i l]) =
      List.range' (hpR m i 0) (3 * m + 1) := by
    rw [← List.map_eq_flatMap, List.range'_eq_map_range]
    rfl
  rw [← h1]
  exact (List.flatMap_append_perm (List.range (3 * m + 1)) (fun l => [hpR m i l])
    fun l => if l % 3 = 1 ∧ c (l / 3) = i then [l / 3] else []).symm

/-- **A diamond visit is a block of consecutive vertices plus its clauses.** For $m$ clauses, a
diamond $i$, a clause-to-diamond map $c$ and a direction $b$, let $T_i = m + i(3m+2)$ be the top
of diamond $i$. The visit of diamond $i$ in direction $b$ is a rearrangement of the list that
consists of $T_i, T_i + 1, \dots, T_i + 3m + 1$ and then the clauses $j < m$ with $c(j) = i$ in
increasing order. -/
theorem hfDiamond_perm (m i : ℕ) (c : ℕ → ℕ) (b : Bool) :
    hfDiamond m i c b ~ List.range' (hpT m i) (3 * m + 2) ++ hfPicks m i c := by
  have hrow : (if b then hfRow m i c else (hfRow m i c).reverse) ~ hfRow m i c := by
    cases b
    · exact List.reverse_perm _
    · exact List.Perm.refl _
  have h0 : hpR m i 0 = hpT m i + 1 := rfl
  rw [List.range'_succ, ← h0, List.cons_append]
  exact (hrow.trans (hfRow_perm m i c)).cons _

/-- **The first $t$ diamonds occupy consecutive vertices.** For natural numbers $m$ and $t$, let
$T_i = m + i(3m+2)$. Concatenating, for $i = 0, \dots, t - 1$, the lists
$T_i, T_i + 1, \dots, T_i + 3m + 1$ of $3m + 2$ consecutive numbers (the top and the row of
diamond $i$) gives the list $m, m + 1, \dots, m + t(3m+2) - 1$, that is, the numbers from $m$
to $T_t - 1$ in increasing order. -/
theorem flatMap_range'_hpT (m t : ℕ) :
    (List.range t).flatMap (fun i => List.range' (hpT m i) (3 * m + 2)) =
      List.range' m (t * (3 * m + 2)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [List.range_succ, List.flatMap_append, ih, List.flatMap_singleton, hpT,
      List.range'_append_1, Nat.add_one_mul t]

/-- **The forward path visits every vertex once.** Let $m, k$ be natural numbers, let $c$ send
every clause $j < m$ to a diamond $c(j) < k$, let $d$ be any directions, and let
$T_k = m + k(3m+2)$. The forward path through the first $k$ diamonds in directions $d$ with
clause choice $c$ is a permutation of the list $0, 1, \dots, T_k$. -/
theorem hfPath_perm {m k : ℕ} {c : ℕ → ℕ} (d : ℕ → Bool) (hc : ∀ j < m, c j < k) :
    hfPath m k c d ~ List.range (hpT m k + 1) := by
  have h1 : (List.range k).flatMap (fun i => hfDiamond m i c (d i)) ~
      List.range' m (k * (3 * m + 2)) ++ (List.range k).flatMap (fun i => hfPicks m i c) := by
    rw [← flatMap_range'_hpT]
    exact (List.Perm.flatMap_left _ fun i _ => hfDiamond_perm m i c (d i)).trans
      (List.flatMap_append_perm _ _ _).symm
  have h2 : List.range (hpT m k + 1) = List.range m ++ List.range' m (k * (3 * m + 2) + 1) := by
    have h := @List.range'_append_1 0 m (k * (3 * m + 2) + 1)
    rw [Nat.zero_add] at h
    rw [List.range_eq_range', List.range_eq_range', h, hpT, Nat.add_assoc]
  have h3 : List.range' m (k * (3 * m + 2) + 1) = List.range' m (k * (3 * m + 2)) ++ [hpT m k] :=
    List.range'_1_concat
  rw [hfPath, h2, h3]
  calc _ ~ (List.range' m (k * (3 * m + 2)) ++ (List.range k).flatMap (fun i => hfPicks m i c)) ++
          [hpT m k] := h1.append_right _
    _ ~ List.range' m (k * (3 * m + 2)) ++ ([hpT m k] ++
          (List.range k).flatMap (fun i => hfPicks m i c)) := by
        rw [List.append_assoc]
        exact List.Perm.append_left _ List.perm_append_comm
    _ ~ (List.range' m (k * (3 * m + 2)) ++ [hpT m k]) ++ List.range m := by
        rw [← List.append_assoc]
        exact List.Perm.append_left _ (flatMap_hfPicks_perm hc)
    _ ~ _ := List.perm_append_comm

/-! ### Arcs along the path -/

/-- **Chain condition for a diamond row.** Let $R$ be a relation on $\mathbb{N}$, let $m$ and $i$
be natural numbers and $c : \mathbb{N} \to \mathbb{N}$ a map, and write
$r_l = m + i(3m + 2) + 1 + l$ for the row vertices of diamond $i$. If $R(r_l, r_{l+1})$ holds
for every $l < 3m$, and $R(r_{3j+1}, j)$ and $R(j, r_{3j+2})$ hold for every $j < m$ with
$c(j) = i$, then the row of diamond $i$ for $c$ is a chain for $R$: every entry is related by
$R$ to the next one. -/
theorem isChain_hfRow {R : ℕ → ℕ → Prop} {m i : ℕ} {c : ℕ → ℕ}
    (hrow : ∀ l < 3 * m, R (hpR m i l) (hpR m i (l + 1)))
    (hdet : ∀ j < m, c j = i → R (hpR m i (3 * j + 1)) j ∧ R j (hpR m i (3 * j + 2))) :
    (hfRow m i c).IsChain R := by
  unfold hfRow
  rw [List.flatMap_def, List.isChain_flatten (by simp), List.isChain_map, List.isChain_range]
  refine ⟨?_, fun l hl => ?_⟩
  · simp only [List.mem_map, List.mem_range]
    rintro _ ⟨l, hl, rfl⟩
    split
    · next h =>
      obtain ⟨j, rfl⟩ : ∃ j, l = 3 * j + 1 := ⟨l / 3, by omega⟩
      have hj : (3 * j + 1) / 3 = j := by omega
      rw [hj] at h ⊢
      exact List.isChain_pair.2 (hdet j (by omega) h.2).1
    · exact List.isChain_singleton _
  · simp only [Nat.add_sub_cancel] at hl
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq', Nat.succ_eq_add_one]
    split
    · next h =>
      obtain ⟨j, rfl⟩ : ∃ j, l = 3 * j + 1 := ⟨l / 3, by omega⟩
      have hj : (3 * j + 1) / 3 = j := by omega
      rw [hj] at h ⊢
      simpa using (hdet j (by omega) h.2).2
    · simpa using hrow l hl

/-- **A row starts at its left end.** For $m$ clauses, a diamond $i$ and any clause-to-diamond
map $c$, the row of diamond $i$ read left to right, with the clauses sent to $i$ by $c$
inserted, starts at its left end, the row vertex $T_i + 1$, where $T_i = m + i(3m+2)$ is the
top of diamond $i$. -/
theorem head?_hfRow (m i : ℕ) (c : ℕ → ℕ) : (hfRow m i c).head? = some (hpR m i 0) := by
  simp [hfRow, List.range_succ_eq_map]

/-- **A row ends at its right end.** For $m$ clauses, a diamond $i$ and any clause-to-diamond
map $c$, the row of diamond $i$ read left to right, with the clauses sent to $i$ by $c$
inserted, ends at the row vertex $T_i + 1 + 3m$, where $T_i = m + i(3m+2)$ is the top of
diamond $i$. -/
theorem getLast?_hfRow (m i : ℕ) (c : ℕ → ℕ) :
    (hfRow m i c).getLast? = some (hpR m i (3 * m)) := by
  simp [hfRow, List.range_succ]

/-- **Chain condition for a diamond traversal.** Let $R$ be a relation on $\mathbb{N}$, let $m$
and $i$ be natural numbers, $c : \mathbb{N} \to \mathbb{N}$ a map and $b$ a boolean, and write
$t_a = m + a(3m + 2)$ for the top of diamond $a$ and $r_l = t_i + 1 + l$ for the row vertices
of diamond $i$. Suppose that $R(t_i, r_0)$, $R(t_i, r_{3m})$, $R(r_0, t_{i+1})$ and
$R(r_{3m}, t_{i+1})$ hold; that $R(r_l, r_{l+1})$ and $R(r_{l+1}, r_l)$ hold for every
$l < 3m$; that if $b$ is true, then $R(r_{3j+1}, j)$ and $R(j, r_{3j+2})$ hold for every
$j < m$ with $c(j) = i$; and that if $b$ is false, then $R(r_{3j+2}, j)$ and $R(j, r_{3j+1})$
hold for every $j < m$ with $c(j) = i$. Then the traversal of diamond $i$ for $c$ in
direction $b$, followed by $t_{i+1}$, is a chain for $R$: every entry is related by $R$ to the
next one. -/
theorem isChain_hfDiamond {R : ℕ → ℕ → Prop} {m i : ℕ} {c : ℕ → ℕ} {b : Bool}
    (hT0 : R (hpT m i) (hpR m i 0)) (hT3 : R (hpT m i) (hpR m i (3 * m)))
    (hB0 : R (hpR m i 0) (hpT m (i + 1))) (hB3 : R (hpR m i (3 * m)) (hpT m (i + 1)))
    (hrow : ∀ l < 3 * m, R (hpR m i l) (hpR m i (l + 1)) ∧ R (hpR m i (l + 1)) (hpR m i l))
    (hpos : b = true → ∀ j < m, c j = i →
      R (hpR m i (3 * j + 1)) j ∧ R j (hpR m i (3 * j + 2)))
    (hneg : b = false → ∀ j < m, c j = i →
      R (hpR m i (3 * j + 2)) j ∧ R j (hpR m i (3 * j + 1))) :
    (hfDiamond m i c b ++ [hpT m (i + 1)]).IsChain R := by
  rw [hfDiamond, List.cons_append, List.isChain_cons, List.isChain_append]
  cases b
  · simp only [Bool.false_eq_true, ite_false, List.head?_append, List.head?_reverse,
      getLast?_hfRow, List.getLast?_reverse, head?_hfRow, Option.some_or, Option.mem_def,
      Option.some.injEq, forall_eq', List.head?_cons, List.isChain_singleton, true_and]
    refine ⟨hT3, List.isChain_reverse.2 (isChain_hfRow (fun l hl => (hrow l hl).2) ?_), hB0⟩
    intro j hj hcj
    exact ⟨(hneg rfl j hj hcj).2, (hneg rfl j hj hcj).1⟩
  · simp only [ite_true, List.head?_append, getLast?_hfRow, head?_hfRow, Option.some_or,
      Option.mem_def, Option.some.injEq, forall_eq', List.head?_cons, List.isChain_singleton,
      true_and]
    exact ⟨hT0, isChain_hfRow (fun l hl => (hrow l hl).1) (hpos rfl), hB3⟩

/-- **Chain condition for the forward path.** Let $R$ be a relation on $\mathbb{N}$, let $m$ and
$k$ be natural numbers, $c : \mathbb{N} \to \mathbb{N}$ a map and $d : \mathbb{N} \to
\{\mathrm{true}, \mathrm{false}\}$ a choice of directions, and write $t_a = m + a(3m + 2)$ for
the top of diamond $a$. If for every $i < k$ the traversal of diamond $i$ for $c$ in direction
$d(i)$, followed by $t_{i+1}$, is a chain for $R$ (every entry is related by $R$ to the next
one), then the forward path through the first $k$ diamonds for $c$ and $d$ is a chain for
$R$. -/
theorem isChain_hfPath {R : ℕ → ℕ → Prop} {m k : ℕ} {c : ℕ → ℕ} {d : ℕ → Bool}
    (hD : ∀ i < k, (hfDiamond m i c (d i) ++ [hpT m (i + 1)]).IsChain R) :
    (hfPath m k c d).IsChain R := by
  induction k with
  | zero => simp [hfPath]
  | succ t ih =>
    have h1 := List.isChain_append.1 (ih fun i hi => hD i (by omega))
    rw [hfPath, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine List.isChain_append.2 ⟨h1.1, hD t (by omega), fun x hx y hy => ?_⟩
    simp only [hfDiamond, List.cons_append, List.head?_cons, Option.mem_def,
      Option.some.injEq] at hy
    subst hy
    exact h1.2.2 x hx _ rfl

/-- **The forward path starts at the first top.** For $m$ clauses, $k$ diamonds, any
clause-to-diamond map $c$ and any directions $d$, the forward path through the first $k$
diamonds in directions $d$ with clause choice $c$ starts at the top $T_0 = m$ of diamond $0$. -/
theorem head?_hfPath (m k : ℕ) (c : ℕ → ℕ) (d : ℕ → Bool) :
    (hfPath m k c d).head? = some (hpT m 0) := by
  cases k with
  | zero => simp [hfPath]
  | succ k => simp [hfPath, List.range_succ_eq_map, hfDiamond]

/-- **The forward path ends at the last top.** For $m$ clauses, $k$ diamonds, any
clause-to-diamond map $c$ and any directions $d$, the forward path through the first $k$
diamonds in directions $d$ with clause choice $c$ ends at the top $T_k = m + k(3m+2)$. -/
theorem getLast?_hfPath (m k : ℕ) (c : ℕ → ℕ) (d : ℕ → Bool) :
    (hfPath m k c d).getLast? = some (hpT m k) := by
  simp [hfPath]

/-! ### The arcs of the construction -/

/-- **Diamond arcs are arcs of the construction.** Let $\varphi$ be a CNF formula, let
$x_0, \dots, x_{k-1}$ be its distinct variables in the order used by the construction, and let
$i < k$. Every arc of diamond $i$ for variable $x_i$ is an arc of the HAMPATH construction for
$\varphi$. -/
theorem mem_hamEdges_of_mem_diamondEdges {φ : CNF} {e : ℕ × ℕ} {i : ℕ} (hi : i < (hamVars φ).length)
    (h : e ∈ diamondEdges φ i ((hamVars φ).getD i 0)) : e ∈ hamEdges φ :=
  List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, h⟩

/-- **The frame arcs of a diamond.** Let $\varphi$ be a CNF formula with $m$ clauses, let $i$
and $x$ be natural numbers, and write $t_a = m + a(3m + 2)$ for the top of diamond $a$ and
$r_l = t_i + 1 + l$ for the row vertices of diamond $i$. The four arcs $(t_i, r_0)$,
$(t_i, r_{3m})$, $(r_0, t_{i+1})$ and $(r_{3m}, t_{i+1})$ are arcs of diamond $i$ for the
variable $x$ in the construction for $\varphi$. -/
theorem mem_diamondEdges_frame (φ : CNF) (i x : ℕ) :
    (hpT φ.length i, hpR φ.length i 0) ∈ diamondEdges φ i x ∧
      (hpT φ.length i, hpR φ.length i (3 * φ.length)) ∈ diamondEdges φ i x ∧
      (hpR φ.length i 0, hpT φ.length (i + 1)) ∈ diamondEdges φ i x ∧
      (hpR φ.length i (3 * φ.length), hpT φ.length (i + 1)) ∈ diamondEdges φ i x := by
  simp [diamondEdges]

/-- **Row arcs of a diamond.** Let $\varphi$ be a CNF formula with $m$ clauses, let $i$ and $x$ be
natural numbers, and write $r_i(l)$ for row vertex $l$ of diamond $i$. For every $l < 3m$, the arcs
of diamond $i$ for variable $x$ include both the arc from $r_i(l)$ to $r_i(l+1)$ and the arc from
$r_i(l+1)$ to $r_i(l)$. -/
theorem mem_diamondEdges_row (φ : CNF) (i x : ℕ) {l : ℕ} (hl : l < 3 * φ.length) :
    (hpR φ.length i l, hpR φ.length i (l + 1)) ∈ diamondEdges φ i x ∧
      (hpR φ.length i (l + 1), hpR φ.length i l) ∈ diamondEdges φ i x := by
  simp only [diamondEdges]
  constructor <;>
    exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.2 ⟨l, List.mem_range.2 hl, by simp⟩))

/-- **Positive detour arcs of a diamond.** Let $\varphi$ be a CNF formula with $m$ clauses, let
$i$, $x$, $j$ be natural numbers with $j < m$, and write $r_i(l)$ for row vertex $l$ of diamond
$i$. If the variable $x$ occurs positively in clause $j$ of $\varphi$ (counting clauses from $0$),
then the arcs of diamond $i$ for variable $x$ include both the arc from $r_i(3j+1)$ to clause
vertex $j$ and the arc from clause vertex $j$ to $r_i(3j+2)$. -/
theorem mem_diamondEdges_pos {φ : CNF} {i x j : ℕ} (hj : j < φ.length)
    (h : (x, true) ∈ φ.getD j []) :
    (hpR φ.length i (3 * j + 1), j) ∈ diamondEdges φ i x ∧
      (j, hpR φ.length i (3 * j + 2)) ∈ diamondEdges φ i x := by
  simp only [diamondEdges]
  constructor <;>
    exact List.mem_append_right _ (List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, by
      simp only [h, ↓reduceIte]
      simp⟩)

/-- **The detour arcs of a negative occurrence.** Let $\varphi$ be a CNF formula with $m$
clauses, let $i$, $x$ and $j$ be natural numbers with $j < m$, and write
$r_l = m + i(3m + 2) + 1 + l$ for the row vertices of diamond $i$. If the negative literal
$\neg x$ occurs in clause $j$ of $\varphi$, then $(r_{3j+2}, j)$ and $(j, r_{3j+1})$ are arcs
of diamond $i$ for the variable $x$ in the construction for $\varphi$. -/
theorem mem_diamondEdges_neg {φ : CNF} {i x j : ℕ} (hj : j < φ.length)
    (h : (x, false) ∈ φ.getD j []) :
    (hpR φ.length i (3 * j + 2), j) ∈ diamondEdges φ i x ∧
      (j, hpR φ.length i (3 * j + 1)) ∈ diamondEdges φ i x := by
  simp only [diamondEdges]
  constructor <;>
    exact List.mem_append_right _ (List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, by
      simp only [h, ↓reduceIte]
      simp⟩)

/-! ### The forward direction -/

/-- **A satisfying choice gives a Hamiltonian path.** Let $\varphi$ be a CNF formula with $m$
clauses, let $v_0, \dots, v_{k-1}$ be its distinct variables in the order used by the
construction, let $\sigma$ assign a truth value to every variable, and write
$t_a = m + a(3m + 2)$ for the top of diamond $a$. Let $c : \mathbb{N} \to \mathbb{N}$ be such
that for every $j < m$ we have $c(j) < k$ and clause $j$ of $\varphi$ contains the literal over
$v_{c(j)}$ that $\sigma$ makes true (positive if $\sigma(v_{c(j)})$ is true, negative
otherwise). Then the forward path through the first $k$ diamonds for $c$, with diamond $i$
traversed in direction $\sigma(v_i)$, is a Hamiltonian path from $t_0$ to $t_k$ in the digraph
on the vertices $0, \dots, t_k$ whose arcs are the arcs of the construction for $\varphi$. -/
theorem isHamPath_hfPath {φ : CNF} {σ : ℕ → Bool} {c : ℕ → ℕ}
    (hc : ∀ j < φ.length, c j < (hamVars φ).length ∧
      ((hamVars φ).getD (c j) 0, σ ((hamVars φ).getD (c j) 0)) ∈ φ.getD j []) :
    IsHamPath (hpT φ.length (hamVars φ).length + 1) (hamEdges φ) (hpT φ.length 0)
      (hpT φ.length (hamVars φ).length)
      (hfPath φ.length (hamVars φ).length c fun i => σ ((hamVars φ).getD i 0)) := by
  have hp := hfPath_perm (fun i => σ ((hamVars φ).getD i 0)) fun j hj => (hc j hj).1
  refine ⟨hp.nodup_iff.2 List.nodup_range, hp.length_eq.trans List.length_range,
    fun v hv => List.mem_range.1 (hp.subset hv), head?_hfPath .., getLast?_hfPath .., ?_⟩
  refine isChain_hfPath fun i hi => ?_
  have hTk : ∀ i' ≤ (hamVars φ).length,
      hpT φ.length i' < hpT φ.length (hamVars φ).length + 1 :=
    fun i' hi' => Nat.lt_succ_of_le (hpT_mono hi')
  have hR : ∀ l ≤ 3 * φ.length, hpR φ.length i l < hpT φ.length (hamVars φ).length + 1 :=
    fun l hl => (hpR_lt_hpT_succ hl).trans (hTk _ hi)
  have hJ : ∀ j < φ.length, j < hpT φ.length (hamVars φ).length + 1 := fun j hj =>
    hj.trans_le ((Nat.le_add_right _ _).trans (hTk _ (Nat.zero_le _)).le)
  have arc : ∀ {u v}, (u, v) ∈ diamondEdges φ i ((hamVars φ).getD i 0) →
      u < hpT φ.length (hamVars φ).length + 1 → v < hpT φ.length (hamVars φ).length + 1 →
      Path.arc (hpT φ.length (hamVars φ).length + 1) (hamEdges φ) u v :=
    fun h hu hv => ⟨mem_hamEdges_of_mem_diamondEdges hi h, hu, hv⟩
  obtain ⟨f1, f2, f3, f4⟩ := mem_diamondEdges_frame φ i ((hamVars φ).getD i 0)
  refine isChain_hfDiamond (arc f1 (hTk i hi.le) (hR 0 (Nat.zero_le _)))
    (arc f2 (hTk i hi.le) (hR _ le_rfl)) (arc f3 (hR 0 (Nat.zero_le _)) (hTk _ hi))
    (arc f4 (hR _ le_rfl) (hTk _ hi)) (fun l hl => ?_) (fun hb j hj hcj => ?_)
    (fun hb j hj hcj => ?_)
  · obtain ⟨e1, e2⟩ := mem_diamondEdges_row φ i ((hamVars φ).getD i 0) hl
    exact ⟨arc e1 (hR l (by omega)) (hR (l + 1) (by omega)),
      arc e2 (hR (l + 1) (by omega)) (hR l (by omega))⟩
  · have hmem := (hc j hj).2
    rw [hcj, hb] at hmem
    obtain ⟨e1, e2⟩ := mem_diamondEdges_pos (i := i) hj hmem
    exact ⟨arc e1 (hR _ (by omega)) (hJ j hj), arc e2 (hJ j hj) (hR _ (by omega))⟩
  · have hmem := (hc j hj).2
    rw [hcj, hb] at hmem
    obtain ⟨e1, e2⟩ := mem_diamondEdges_neg (i := i) hj hmem
    exact ⟨arc e1 (hR _ (by omega)) (hJ j hj), arc e2 (hJ j hj) (hR _ (by omega))⟩

/-- **Satisfiable formulas give Hamiltonian paths (SAT ≤ HAMPATH, forward direction).** Let
$\varphi$ be a satisfiable CNF formula with $m$ clauses and $k$ distinct variables, and let
$T_i = m + i(3m+2)$ be the top of diamond $i$. Then the digraph on the vertices
$0, \dots, T_k$ whose arcs are the arcs of the HAMPATH construction for $\varphi$ has a
Hamiltonian path from $T_0$ to $T_k$. -/
theorem exists_isHamPath_of_cnfSat {φ : CNF} (h : CNFSat φ) :
    ∃ p, IsHamPath (hpT φ.length (hamVars φ).length + 1) (hamEdges φ)
      (hpT φ.length 0) (hpT φ.length (hamVars φ).length) p := by
  obtain ⟨σ, hσ⟩ := h
  have hex : ∀ j, ∃ i, j < φ.length → i < (hamVars φ).length ∧
      ((hamVars φ).getD i 0, σ ((hamVars φ).getD i 0)) ∈ φ.getD j [] := by
    intro j
    by_cases hj : j < φ.length
    · have hC : φ.getD j [] ∈ φ := by
        rw [List.getD_eq_getElem _ _ hj]
        exact List.getElem_mem hj
      obtain ⟨x, b, hxb, hσx⟩ := hσ _ hC
      obtain ⟨i, hi, hx⟩ : ∃ i, ∃ h : i < (hamVars φ).length, (hamVars φ)[i] = x :=
        List.mem_iff_getElem.1 (List.mem_dedup.2 (mem_varsOf hxb hC))
      refine ⟨i, fun _ => ⟨hi, ?_⟩⟩
      rw [List.getD_eq_getElem _ _ hi, hx, hσx]
      exact hxb
    · exact ⟨0, fun h => absurd h hj⟩
  choose c hc using hex
  exact ⟨_, isHamPath_hfPath fun j hj => hc j hj⟩

end Cslib.Complexity.Karp
