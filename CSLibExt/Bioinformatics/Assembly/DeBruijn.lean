/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.List.Range
import Mathlib.Data.List.Infix
import Mathlib.Data.List.TakeDrop

/-!
# de Bruijn graph assembly: the `k`-mer walk is an Eulerian trail

Pevzner, Tang and Waterman (2001) assemble a string from its `k`-mers through the de Bruijn
multigraph: the vertices are the `(k-1)`-mers, and every occurrence of a `k`-mer `w` contributes
one edge from its prefix `w.dropLast` to its suffix `w.tail`. The string itself traverses this
multigraph along its consecutive `(k-1)`-mers, using every edge occurrence exactly once (an
Eulerian trail); conversely, every Eulerian trail spells a string with the same `k`-mer multiset
(the same *spectrum*), so assembly reduces to finding an Eulerian trail (Hierholzer's algorithm,
`CSLibExt.Algorithms.Lean.Graph.Hierholzer`).

The multigraph is represented by its list of edge occurrences `deBruijnEdges k s` (one per
`k`-mer occurrence, in order of position), a walk by its vertex list `W`, and the steps of a walk
by its consecutive pairs `W.zip W.tail` (which is `Hierholzer.walkEdges W` by definition); `W` is
an Eulerian trail when its steps are a permutation of the edge occurrences, as in
`Hierholzer.IsEulerPath`.

## Main results

* `zip_tail_kmers`, `zip_tail_kmers_perm`: **the `(k-1)`-mer walk of `s` is an Eulerian trail**
  of its de Bruijn multigraph (`1 ≤ k`); its steps are the edges in order of position.
* `spell_kmers`: that walk spells `s` (`2 ≤ k ≤ |s| + 1`).
* `kmers_spell_perm`: **every Eulerian trail spells a string with the same `k`-mer multiset**
  (`2 ≤ k`; the vertices of the walk are `(k-1)`-mers).

Not covered: computing an Eulerian trail (Hierholzer's algorithm) on this multigraph, and the
uniqueness questions of assembly (several trails can spell different strings with the same
spectrum).

For `k = 1` the vertices are all the empty word and a trail does not determine the letters, so
the converse needs `2 ≤ k`.

## Design note

`Hierholzer.IsEulerPath` is stated for a `DirectedAdjacency`, whose vertex type is finite and
enumerated. The vertices here are words (`List α`), so the multigraph is kept as its edge list
and the Eulerian condition is stated directly on the steps `W.zip W.tail`; restricting to the
finite set of `(k-1)`-mers of `s` would add a subtype without changing the statements, and the
steps are spelled out rather than imported so that this module depends on Mathlib only.

## References

* P. A. Pevzner, H. Tang and M. S. Waterman, *An Eulerian path approach to DNA fragment
  assembly*, Proc. Natl. Acad. Sci. USA 98 (2001), 9748–9753.
* N. G. de Bruijn, *A combinatorial problem*, Proc. Koninklijke Nederlandse Akademie van
  Wetenschappen 49 (1946), 758–764.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.Assembly.DeBruijn

/-- The `k`-mers of `s` in order of position: the length-`k` windows `(s.drop i).take k`
for `i + k ≤ |s|`. -/
def kmers {α : Type*} (k : ℕ) (s : List α) : List (List α) :=
  (List.range (s.length + 1 - k)).map fun i => (s.drop i).take k

/-- Executable form of `kmers`: the suffixes of `s` are generated once by `List.tails`, so the
cost is `O(|s| · k)` rather than the `Θ(|s|²)` of recomputing `s.drop i` for every `i`. The
compiler uses it in place of `kmers` (`kmers_eq_kmersImpl`). -/
def kmersImpl {α : Type*} (k : ℕ) (s : List α) : List (List α) :=
  (s.tails.take (s.length + 1 - k)).map (·.take k)

@[csimp] theorem kmers_eq_kmersImpl : @kmers = @kmersImpl := by
  funext α k s
  apply List.ext_getElem
  · simp only [kmers, kmersImpl, List.length_map, List.length_range, List.length_take,
      List.length_tails]
    omega
  · intro i _ _
    simp [kmers, kmersImpl, List.getElem_tails]

/-- The edge of the de Bruijn multigraph contributed by a `k`-mer `w`: from its prefix
`(k-1)`-mer `w.dropLast` to its suffix `(k-1)`-mer `w.tail`. -/
def kmerEdge {α : Type*} (w : List α) : List α × List α := (w.dropLast, w.tail)

/-- The de Bruijn multigraph of `s` (Pevzner–Tang–Waterman 2001) as its list of edge
occurrences: one edge per `k`-mer occurrence, in order of position. -/
def deBruijnEdges {α : Type*} (k : ℕ) (s : List α) : List (List α × List α) :=
  (kmers k s).map kmerEdge

/-- The string spelled by a walk of `(k-1)`-mers: the first vertex followed by the last letter of
each later vertex. -/
def spell {α : Type*} : List (List α) → List α
  | [] => []
  | v :: W => v ++ W.flatMap fun u => u.getLast?.toList

private theorem kmers_cons {α : Type*} (k : ℕ) (a : α) (s : List α)
    (hs : k ≤ s.length + 1) :
    kmers k (a :: s) = (a :: s).take k :: kmers k s := by
  have h : (a :: s).length + 1 - k = (s.length + 1 - k) + 1 := by
    simp only [List.length_cons]
    omega
  simp only [kmers, h, List.range_succ_eq_map, List.map_cons, List.map_map,
    List.drop_zero]
  congr 1

private theorem kmers_short {α : Type*} (k : ℕ) (s : List α) (hs : s.length < k) :
    kmers k s = [] := by
  have h : s.length + 1 - k = 0 := by omega
  simp [kmers, h]

private theorem kmers_exact {α : Type*} (k : ℕ) (s : List α) (hs : s.length = k) :
    kmers k s = [s] := by
  simp [kmers, hs]

private theorem dropLast_append_last {α : Type*} (s : List α) :
    s.dropLast ++ s.getLast?.toList = s := by
  simpa only [List.dropLast_eq_take] using List.take_append_getLast? s

private theorem spell_prepend {α : Type*} (a : α) (u : List α) (W : List (List α)) :
    spell ((a :: u.dropLast) :: u :: W) = a :: spell (u :: W) := by
  simp only [spell, List.flatMap_cons, List.cons_append]
  rw [← List.append_assoc, dropLast_append_last]

/-- **The `(k-1)`-mer walk of `s` traverses the de Bruijn multigraph in order**: its steps are
exactly the edges contributed by the `k`-mers of `s`, one per occurrence, in order of position. -/
theorem zip_tail_kmers {α : Type*} (k : ℕ) (hk : 1 ≤ k) (s : List α) :
    (kmers (k - 1) s).zip (kmers (k - 1) s).tail = deBruijnEdges k s := by
  apply List.ext_getElem
  · simp only [deBruijnEdges, kmers, List.length_zip, List.length_tail,
      List.length_map, List.length_range]
    omega
  · intro i hi hj
    have hb : i + k ≤ s.length := by
      simp only [deBruijnEdges, kmers, List.length_map, List.length_range] at hj
      omega
    have hd : k ≤ (s.drop i).length := by
      simp only [List.length_drop]
      omega
    simp only [deBruijnEdges, kmers, List.getElem_zip, List.getElem_map,
      List.getElem_tail, List.getElem_range, kmerEdge]
    rw [List.dropLast_take hd, List.tail_take_eq_take_tail, List.tail_drop]

/-- **The `k`-mer walk of `s` is an Eulerian trail** of its de Bruijn multigraph: its steps are a
permutation of the edge occurrences, each traversed once. -/
theorem zip_tail_kmers_perm {α : Type*} (k : ℕ) (hk : 1 ≤ k) (s : List α) :
    ((kmers (k - 1) s).zip (kmers (k - 1) s).tail).Perm (deBruijnEdges k s) := by
  exact List.Perm.of_eq (zip_tail_kmers k hk s)

/-- The `(k-1)`-mer walk of `s` spells `s` back (`2 ≤ k`, `k - 1 ≤ |s|`). -/
theorem spell_kmers {α : Type*} (k : ℕ) (hk : 2 ≤ k) (s : List α) (hs : k - 1 ≤ s.length) :
    spell (kmers (k - 1) s) = s := by
  induction s with
  | nil => simp only [List.length_nil] at hs; omega
  | cons a s ih =>
    by_cases ht : k - 1 ≤ s.length
    · rw [kmers_cons (k - 1) a s (by omega)]
      obtain ⟨u, W, hu⟩ : ∃ u W, kmers (k - 1) s = u :: W := by
        cases s with
        | nil => simp only [List.length_nil] at ht; omega
        | cons b t =>
          exact ⟨(b :: t).take (k - 1), kmers (k - 1) t,
            kmers_cons (k - 1) b t (by simpa using ht)⟩
      have hp : u = s.take (k - 1) := by
        unfold kmers at hu
        have hz : s.length + 1 - (k - 1) = (s.length - (k - 1)) + 1 := by omega
        rw [hz, List.range_succ_eq_map] at hu
        simpa using (List.cons.inj hu).1.symm
      rw [List.take_cons (by omega), ← List.dropLast_take ht, ← hp, hu,
        spell_prepend, ← hu, ih ht]
    · have he : (a :: s).length = k - 1 := by simp only [List.length_cons] at hs ⊢; omega
      rw [kmers_exact (k - 1) (a :: s) he]
      simp [spell]

private theorem kmer_length {α : Type*} (k : ℕ) (s w : List α)
    (hw : w ∈ kmers k s) : w.length = k := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  have hb := List.mem_range.mp hi
  simp only [List.length_take, List.length_drop]
  omega

private theorem reconstruct_kmer {α : Type*} (w : List α) (hw : 2 ≤ w.length) :
    w.dropLast ++ w.tail.getLast?.toList = w := by
  cases w with
  | nil => simp only [List.length_nil] at hw; omega
  | cons a t =>
    have ht : t ≠ [] := by intro h; subst t; simp at hw
    rw [List.dropLast_cons_of_ne_nil ht]
    simp only [List.tail_cons, List.cons_append, dropLast_append_last]

private theorem kmers_spell_edges {α : Type*} (k : ℕ) (hk : 2 ≤ k)
    (W : List (List α)) (hlen : ∀ v ∈ W, v.length + 1 = k)
    (hov : ∀ e ∈ W.zip W.tail, e.1.tail = e.2.dropLast) :
    kmers k (spell W) =
      (W.zip W.tail).map (fun e => e.1 ++ e.2.getLast?.toList) := by
  induction W with
  | nil =>
    simp only [spell]
    rw [kmers_short k [] (by simp; omega)]
    rfl
  | cons v T ih =>
    cases T with
    | nil =>
      have hv := hlen v (by simp)
      simp only [spell, List.flatMap_nil, List.append_nil]
      rw [kmers_short k v (by omega)]
      rfl
    | cons u T =>
      have hv := hlen v (by simp)
      have hu := hlen u (by simp)
      have hl : ∀ z ∈ u :: T, z.length + 1 = k := by
        intro z hz
        exact hlen z (List.mem_cons_of_mem v hz)
      have ho : ∀ e ∈ (u :: T).zip (u :: T).tail, e.1.tail = e.2.dropLast := by
        intro e he
        exact hov e (by simpa using List.mem_cons_of_mem (v, u) he)
      have hpair : v.tail = u.dropLast := hov (v, u) (by simp)
      cases v with
      | nil => simp only [List.length_nil] at hv; omega
      | cons a t =>
        simp only [List.tail_cons] at hpair
        subst t
        have hs : k ≤ (spell (u :: T)).length + 1 := by
          simp only [spell, List.length_append]
          omega
        rw [spell_prepend, kmers_cons k a (spell (u :: T)) hs, ih hl ho]
        have ht : (a :: spell (u :: T)).take k =
            (a :: u.dropLast) ++ u.getLast?.toList := by
          rw [List.take_cons (by omega)]
          have hn : k - 1 = u.length := by omega
          simp only [spell, hn, List.take_left, List.cons_append,
            dropLast_append_last]
        rw [ht]
        rfl

/-- **Every Eulerian trail spells a string with the same `k`-mer multiset** (`2 ≤ k`): if `W` is a
walk of `(k-1)`-mers whose steps are a permutation of the edge occurrences of the de Bruijn
multigraph of `s`, then the `k`-mers of the spelled string are a permutation of those of `s`.
(The empty walk is allowed: it is a trail only when `s` has no `k`-mers, and spells `[]`.) -/
theorem kmers_spell_perm {α : Type*} (k : ℕ) (hk : 2 ≤ k) (s : List α) (W : List (List α))
    (hlen : ∀ v ∈ W, v.length + 1 = k)
    (hW : (W.zip W.tail).Perm (deBruijnEdges k s)) :
    (kmers k (spell W)).Perm (kmers k s) := by
  have hov : ∀ e ∈ W.zip W.tail, e.1.tail = e.2.dropLast := by
    intro e he
    have hd : e ∈ deBruijnEdges k s := hW.mem_iff.mp he
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hd
    exact List.tail_dropLast
  rw [kmers_spell_edges k hk W hlen hov]
  have hp := hW.map (fun e => e.1 ++ e.2.getLast?.toList)
  have hr : (deBruijnEdges k s).map (fun e => e.1 ++ e.2.getLast?.toList) =
      kmers k s := by
    simp only [deBruijnEdges, List.map_map]
    conv_rhs => rw [← List.map_id (kmers k s)]
    apply List.map_congr_left
    intro w hw
    exact reconstruct_kmer w (by rw [kmer_length k s w hw]; exact hk)
  rw [hr] at hp
  exact hp

end Cslib.Bioinformatics.Assembly.DeBruijn
