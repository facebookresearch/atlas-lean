/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Greedy algorithms for the shortest common superstring

Blum, Jiang, Li, Tromp and Yannakakis (1994): for a finite set `S` of strings, assumed
substring-free (no string of `S` is a substring of another), a common superstring contains every
string of `S` as a contiguous substring, and `OPT(S)` is the length of a shortest one. The overlap
`ov(s, t)` is the largest `|v|` with `s = u v` and `t = v w` for nonempty `u, w`, and the merge of
`s` and `t` is `pref(s, t) t`, where `s = pref(s, t) v` (Section 2).

* GREEDY repeatedly merges a pair of distinct strings of maximum overlap, ties broken arbitrarily,
  until one string remains. Theorem 12: its output has length at most `4 OPT(S)`.
* MGREEDY repeatedly chooses `s, t` (not necessarily distinct) of maximum overlap, ties broken
  arbitrarily; if `s ≠ t` it replaces them by their merge, and if `s = t` it moves `s` to a set
  `T`; when no string is left it outputs the concatenation of `T`. Theorems 8 and 10 together: its
  output has length at most `4 OPT(S)`.
* TGREEDY runs MGREEDY and then merges the strings of `T` by GREEDY. Theorem 11: its output has
  length at most `3 OPT(S)`.

Every run with any tie-breaking is covered: the runs are relations (`GreedyReaches`,
`MGreedyReaches`), and the theorems hold for every result they relate to `S`. The strings of `S`
are listed without repetition. Not recorded here: Theorem 18 (shortest superstring is MAX
SNP-hard), which needs the class MAX SNP and L-reductions. NP-completeness variants of the
decision problem are in `WantedExt.Complexity.NPComplete`.

Sources: A. Blum, T. Jiang, M. Li, J. Tromp and M. Yannakakis, "Linear approximation of shortest
superstrings", Journal of the ACM 41 (1994) 630–647, doi:10.1145/179812.179818, Section 2 and
Theorems 8, 10, 11 and 12.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Bioinformatics.Assembly.StringOverlap
public import Mathlib.Data.List.Infix
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Lattice.Nat

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.ShortestSuperstringGreedyWanted

variable {α : Type*} [DecidableEq α]

/-- **Overlap.** `ov(s, t)` is the largest `k` with `k < |s|`, `k < |t|` and the last `k` letters of
`s` equal to the first `k` letters of `t` (so `s = u v`, `t = v w` with `|v| = k` and `u`, `w`
nonempty): main's `Cslib.Bioinformatics.Assembly.StringOverlap.overlapAux` searching the lengths
below `min (|s|, |t|)`, and `0` when there is none. Unlike that module's `overlap`, which allows
`k = min (|s|, |t|)`, it is a proper overlap, as in the source; MGREEDY's self-overlap `ov(s, s)`
needs this. -/
def overlap (s t : List α) : ℕ :=
  Cslib.Bioinformatics.Assembly.StringOverlap.overlapAux s t (min s.length t.length - 1)

/-- **Merge.** The merge of `s` and `t` is `pref(s, t) t`, where `pref(s, t)` is `s` without its
last `ov(s, t)` letters; `Cslib.Bioinformatics.Assembly.StringOverlap.merge` splices along that
module's non-proper overlap instead. -/
def mergeStr (s t : List α) : List α :=
  s.take (s.length - overlap s t) ++ t

/-- `x` is a **common superstring** of `S`: every string of `S` is a contiguous substring of
`x`. -/
def IsSuperstring (x : List α) (S : List (List α)) : Prop :=
  ∀ s ∈ S, s <:+: x

/-- `S` is **substring-free**: no string of `S` is a substring of a different string of `S`. -/
def SubstringFree (S : List (List α)) : Prop :=
  ∀ s ∈ S, ∀ t ∈ S, s <:+: t → s = t

/-- `OPT(S)`: the length of a shortest common superstring of `S`. -/
noncomputable def optLength (S : List (List α)) : ℕ :=
  sInf {n | ∃ x, IsSuperstring x S ∧ x.length = n}

/-- The list `L` with the entries at positions `i` and `j` removed. -/
def eraseTwo (L : List (List α)) (i j : Fin L.length) : List (List α) :=
  ((List.finRange L.length).filter (fun k => k ≠ i ∧ k ≠ j)).map fun k => L.get k

/-- `GreedyReaches L r`: some run of **GREEDY** on the list `L` ends with the single string `r`.
At each step a pair of distinct positions `i ≠ j` with maximum overlap among all such pairs is
merged, ties broken arbitrarily. -/
inductive GreedyReaches : List (List α) → List α → Prop
  | single (s : List α) : GreedyReaches [s] s
  | step (L : List (List α)) (i j : Fin L.length) (hij : i ≠ j)
      (hmax : ∀ i' j' : Fin L.length, i' ≠ j' →
        overlap (L.get i') (L.get j') ≤ overlap (L.get i) (L.get j))
      (r : List α) (h : GreedyReaches (mergeStr (L.get i) (L.get j) :: eraseTwo L i j) r) :
      GreedyReaches L r

/-- `MGreedyReaches L T R`: some run of **MGREEDY** started from the working list `L` and the
finished list `T` ends with the finished list `R`. At each step positions `i, j` (possibly equal)
of maximum overlap among all ordered pairs are chosen, ties broken arbitrarily; if `i ≠ j` the
two strings are replaced by their merge, and if `i = j` the string moves to the finished list. -/
inductive MGreedyReaches : List (List α) → List (List α) → List (List α) → Prop
  | done (T : List (List α)) : MGreedyReaches [] T T
  | mergeStep (L T : List (List α)) (i j : Fin L.length) (hij : i ≠ j)
      (hmax : ∀ i' j' : Fin L.length,
        overlap (L.get i') (L.get j') ≤ overlap (L.get i) (L.get j))
      (R : List (List α))
      (h : MGreedyReaches (mergeStr (L.get i) (L.get j) :: eraseTwo L i j) T R) :
      MGreedyReaches L T R
  | finish (L T : List (List α)) (i : Fin L.length)
      (hmax : ∀ i' j' : Fin L.length,
        overlap (L.get i') (L.get j') ≤ overlap (L.get i) (L.get i))
      (R : List (List α)) (h : MGreedyReaches (L.eraseIdx i) (L.get i :: T) R) :
      MGreedyReaches L T R

/-- **GREEDY is a 4-approximation** (Blum, Jiang, Li, Tromp and Yannakakis 1994, Theorem 12):
for a nonempty, substring-free list `S` of strings without repetition, every result `r` of a run
of GREEDY on `S` is a common superstring of `S` of length at most `4 OPT(S)`.

Source: Blum, Jiang, Li, Tromp and Yannakakis (1994), Theorem 12. -/
public theorem_wanted greedy_le_four_opt (S : List (List α)) (hne : S ≠ []) (hnd : S.Nodup)
    (hfree : SubstringFree S) (r : List α) (hr : GreedyReaches S r) :
    IsSuperstring r S ∧ r.length ≤ 4 * optLength S

/-- **MGREEDY is a 4-approximation** (Blum, Jiang, Li, Tromp and Yannakakis 1994, Theorems 8 and
10: MGREEDY builds an optimal cycle cover, and concatenating the opened cycles of an optimal cycle
cover costs at most `4 OPT(S)`): for a nonempty, substring-free list `S` without repetition, for
every run of MGREEDY from `S` with an empty finished list that ends with the finished list `T`,
the concatenation of `T` is a common superstring of `S` of length at most `4 OPT(S)`.

Source: Blum, Jiang, Li, Tromp and Yannakakis (1994), Theorems 8 and 10. -/
public theorem_wanted mgreedy_le_four_opt (S : List (List α)) (hne : S ≠ []) (hnd : S.Nodup)
    (hfree : SubstringFree S) (T : List (List α)) (hT : MGreedyReaches S [] T) :
    IsSuperstring T.flatten S ∧ T.flatten.length ≤ 4 * optLength S

/-- **TGREEDY is a 3-approximation** (Blum, Jiang, Li, Tromp and Yannakakis 1994, Theorem 11): for
a nonempty, substring-free list `S` without repetition, for every run of MGREEDY from `S` with an
empty finished list that ends with the finished list `T`, and every result `r` of a run of GREEDY
on `T`, `r` is a common superstring of `S` of length at most `3 OPT(S)`.

Source: Blum, Jiang, Li, Tromp and Yannakakis (1994), Theorem 11. -/
public theorem_wanted tgreedy_le_three_opt (S : List (List α)) (hne : S ≠ []) (hnd : S.Nodup)
    (hfree : SubstringFree S) (T : List (List α)) (hT : MGreedyReaches S [] T) (r : List α)
    (hr : GreedyReaches T r) :
    IsSuperstring r S ∧ r.length ≤ 3 * optLength S

end WantedExt.Biology.ComputationalBiology.ShortestSuperstringGreedyWanted
