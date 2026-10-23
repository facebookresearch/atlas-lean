/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.List.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finding the `k` shortest paths (Eppstein), sidetracks and enumeration

Formalization of Eppstein's `k` shortest paths algorithm
(D. Eppstein, "Finding the k Shortest Paths",
SIAM J. Comput. 28(2):652–673, 1998), Sections 2.2–2.4:
the sidetrack/`δ` representation of `s–t` walks, the path-graph
correspondence, and ordered enumeration of shortest paths.

* **Lemma 1.** For every edge `e`, `δ(e) ≥ 0`; for edges of the
  shortest-path tree `T`, `δ(e) = 0`.
* **Lemma 2.** For any `s–t` path `p`,
  `ℓ(p) = d(s,t) + ∑ δ(e)` over `sidetracks(p)`
  (equivalently, over all of `p`, since `δ` vanishes on `T`).
* **Lemma 3.** `ℓ(p) ≥ ℓ(prefpath p)`: dropping the last sidetrack edge
  cannot increase the length.
* **Lemma 4** (the `D(G)`/`H_G` heap construction with its size/degree/time
  bounds) is intentionally not formalized: heap-edge segments are left
  implicit in `PPath`, and there is no cost model in scope.
* **Lemma 5.** `s–t` walks are in length-preserving correspondence
  with `PPath`s (decode/encode), via Lemma 2.
* **Lemma 6.** Extending a `PPath` by a sidetrack of nonnegative `δ`
  cannot decrease its weight.
* **Lemma 7.** The tree of `PPath`s (parent = `prefpath`) is heap-ordered
  by weight, via Lemma 3.
* **Theorems 1–2.** Correctness of best-first-search enumeration:
  every `IsBFSTrace` is weight-sorted and minimal, decodes to `s–t`
  walks, and every walk is represented or no shorter than the outputs.

Ported from the `kth-shortest-path-epp` T-Bench Lean verification task
(authored by Leo Osvald). Complexity bounds (`O(m + n log n + k log k)`
and variants) are documented in the source but not formalized:
there is no cost model in scope.

## Modeling choices

* The input digraph `G` and the single-destination shortest-path tree `T`
  are `Digraph`s (Mathlib). Edge lengths are `len : V → V → ℝ`
  and distances to the fixed target `t` are `dist : V → ℝ`.
* The characteristic consequences of "`T` is a shortest-path tree to `t`"
  (the triangle inequality and tightness of tree edges) are taken as
  explicit hypotheses. Deriving them from Dijkstra's algorithm is out of
  scope; they are exactly what the paper's proofs consume.
* Walks carry their endpoints in their type (`DiWalk G s t`), which makes
  the telescoping argument of Lemma 2 a direct induction.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.KShortestPathsEppstein

open Classical

universe u

variable {V : Type u}

/-- `δ(e) = ℓ(e) + d(head(e), t) − d(tail(e), t)` (Eppstein §2.2):
how much distance is lost by being "sidetracked" along `e`
instead of taking a shortest path to `t`. -/
noncomputable def eppDelta (len : V → V → ℝ) (dist : V → ℝ) (u v : V) : ℝ :=
  len u v + dist v - dist u

/-- A directed walk from `s` to `t` in the simple digraph `G`,
as an explicit sequence of steps. -/
inductive DiWalk (G : Digraph V) : V → V → Type u where
  | nil (u : V) : DiWalk G u u
  | cons (u v w : V) : G.Adj u v → DiWalk G v w → DiWalk G u w

/-- The edge (vertex-pair) sequence traversed by a walk. -/
def DiWalk.edges {G : Digraph V} {s t : V} : DiWalk G s t → List (V × V)
  | .nil _ => []
  | .cons u v _ _ tl => (u, v) :: tl.edges

/-- Total length `ℓ(p)` of a walk: the sum of its edge lengths. -/
noncomputable def DiWalk.length (len : V → V → ℝ) {G : Digraph V}
    {s t : V} : DiWalk G s t → ℝ
  | .nil _ => 0
  | .cons u v _ _ tl => len u v + tl.length len

/-- Sum of `δ` over every edge of a walk. -/
noncomputable def DiWalk.deltaSum (len : V → V → ℝ) (dist : V → ℝ)
    {G : Digraph V} {s t : V} : DiWalk G s t → ℝ
  | .nil _ => 0
  | .cons u v _ _ tl => eppDelta len dist u v + tl.deltaSum len dist

/-- Sum of `δ` over the sidetrack edges of a walk, i.e. the edges
outside the shortest-path tree `T` (tree edges contribute `0`). -/
noncomputable def DiWalk.sidetrackSum (T : Digraph V) (len : V → V → ℝ)
    (dist : V → ℝ) {G : Digraph V} {s t : V} : DiWalk G s t → ℝ
  | .nil _ => 0
  | .cons u v _ _ tl =>
      (if T.Adj u v then 0 else eppDelta len dist u v) + tl.sidetrackSum T len dist

/-- The sidetrack subsequence `sidetracks(p)`: the edges of the walk
that lie in `G − T`.  A path is uniquely determined by this subsequence
(Eppstein §2.2), since tree edges between consecutive sidetracks are forced. -/
noncomputable def DiWalk.sidetracks (T : Digraph V) {G : Digraph V}
    {s t : V} : DiWalk G s t → List (V × V)
  | .nil _ => []
  | .cons u v _ _ tl =>
      if T.Adj u v then tl.sidetracks T else (u, v) :: tl.sidetracks T

/-- Length of a path presented by its sidetrack sequence `L`:
`d(s,t) + ∑ δ(e)` over `L`. -/
noncomputable def listSidetrackSum (len : V → V → ℝ) (dist : V → ℝ)
    (L : List (V × V)) : ℝ :=
  (L.map (fun e => eppDelta len dist e.1 e.2)).sum

/-- Lemma 1 (first part): `δ(e) ≥ 0` for every edge of `G`, from the
triangle inequality for distances to `t`. -/
theorem lemma1_delta_nonneg (len : V → V → ℝ) (dist : V → ℝ)
    {G : Digraph V} {u v : V} (_hadj : G.Adj u v)
    (htri : dist u ≤ len u v + dist v) :
    0 ≤ eppDelta len dist u v := by
  unfold eppDelta
  linarith

/-- Lemma 1 (second part): `δ(e) = 0` for edges of the
shortest-path tree `T`, where the triangle inequality is tight. -/
theorem lemma1_delta_tree (len : V → V → ℝ) (dist : V → ℝ) {u v : V}
    (htight : len u v + dist v = dist u) :
    eppDelta len dist u v = 0 := by
  unfold eppDelta
  linarith

/-- Lemma 1 over a whole graph: every edge has nonnegative `δ`. -/
theorem lemma1_all_nonneg (len : V → V → ℝ) (dist : V → ℝ)
    {G : Digraph V}
    (htri : ∀ a b : V, G.Adj a b → dist a ≤ len a b + dist b)
    {u v : V} (hadj : G.Adj u v) :
    0 ≤ eppDelta len dist u v :=
  lemma1_delta_nonneg len dist hadj (htri u v hadj)

/-- Lemma 2 (first equality): the walk length telescopes to
`ℓ(p) = d(s,t) + ∑_{e ∈ p} δ(e)`.  This is pure algebra and needs
no optimality hypotheses. -/
theorem lemma2_telescoping (len : V → V → ℝ) (dist : V → ℝ)
    {G : Digraph V} {s t : V} (p : DiWalk G s t) :
    p.length len = dist s - dist t + p.deltaSum len dist := by
  induction p with
  | nil u =>
    simp only [DiWalk.length, DiWalk.deltaSum]
    ring
  | cons u v w _ tl ih =>
    simp only [DiWalk.length, DiWalk.deltaSum]
    rw [ih]
    unfold eppDelta
    ring

/-- Lemma 2 (second equality): since `δ` vanishes on tree edges, the sum
of `δ` over all edges of a walk equals the sum over its sidetracks. -/
theorem lemma2_sidetrack (T : Digraph V) (len : V → V → ℝ)
    (dist : V → ℝ) {G : Digraph V} {s t : V}
    (htight : ∀ a b : V, T.Adj a b → eppDelta len dist a b = 0)
    (p : DiWalk G s t) :
    p.deltaSum len dist = p.sidetrackSum T len dist := by
  induction p with
  | nil _ => rfl
  | cons u v w _ tl ih =>
    simp only [DiWalk.deltaSum, DiWalk.sidetrackSum]
    by_cases h : T.Adj u v
    · simp only [h, ite_true, htight u v h, ih]
    · simp only [h, ite_false, ih]

/-- Lemma 2 in the paper's form: with `d(t,t) = 0`,
`ℓ(p) = d(s,t) + ∑_{e ∈ sidetracks(p)} δ(e)`. -/
theorem lemma2_path_length (T : Digraph V) (len : V → V → ℝ)
    (dist : V → ℝ) {G : Digraph V} {s t : V} (hdist_t : dist t = 0)
    (htight : ∀ a b : V, T.Adj a b → eppDelta len dist a b = 0)
    (p : DiWalk G s t) :
    p.length len = dist s + p.sidetrackSum T len dist := by
  have h1 := lemma2_telescoping len dist p
  have h2 := lemma2_sidetrack T len dist htight p
  rw [h2, hdist_t] at h1
  simpa using h1

/-- The recursive sidetrack sum agrees with the sum over the explicit
sidetrack list.  This bridges the walk view and the sequence view of §2.2. -/
theorem sidetrackSum_eq_listSum (T : Digraph V) (len : V → V → ℝ)
    (dist : V → ℝ) {G : Digraph V} {s t : V} (p : DiWalk G s t) :
    p.sidetrackSum T len dist = listSidetrackSum len dist (p.sidetracks T) := by
  induction p with
  | nil _ => simp only [DiWalk.sidetrackSum, DiWalk.sidetracks, listSidetrackSum, List.map_nil, List.sum_nil]
  | cons u v w _ tl ih =>
    simp only [DiWalk.sidetrackSum, DiWalk.sidetracks]
    by_cases h : T.Adj u v
    · simp only [h, ite_true, ih, zero_add]
    · simp only [h, ite_false, ih]
      unfold listSidetrackSum
      simp only [List.map_cons, List.sum_cons]

/-- Lemma 3 (sequence core): dropping the last sidetrack edge cannot
increase `d(s,t) + ∑ δ`, since the dropped `δ` is nonnegative (Lemma 1). -/
theorem lemma3_core (len : V → V → ℝ) (dist : V → ℝ) (P : List (V × V))
    {u v : V} (hδ : 0 ≤ eppDelta len dist u v) :
    listSidetrackSum len dist P
      ≤ listSidetrackSum len dist (P ++ [(u, v)]) := by
  have h : listSidetrackSum len dist (P ++ [(u, v)])
      = listSidetrackSum len dist P + eppDelta len dist u v := by
    unfold listSidetrackSum
    rw [List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [h]
  linarith

/-- Lemma 3 (Eppstein): `ℓ(p) ≥ ℓ(prefpath p)`.  Here `q` plays the role
of `prefpath p`: its sidetrack sequence is that of `p` with the last
sidetrack edge dropped. -/
theorem lemma3_prefpath_le (T : Digraph V) (len : V → V → ℝ)
    (dist : V → ℝ) {G : Digraph V} {s t : V} (hdist_t : dist t = 0)
    (htight : ∀ a b : V, T.Adj a b → eppDelta len dist a b = 0)
    (p q : DiWalk G s t) (P : List (V × V)) {u v : V}
    (hδ : 0 ≤ eppDelta len dist u v)
    (hp : p.sidetracks T = P ++ [(u, v)])
    (hq : q.sidetracks T = P) :
    q.length len ≤ p.length len := by
  have hp_len := lemma2_path_length T len dist hdist_t htight p
  have hq_len := lemma2_path_length T len dist hdist_t htight q
  have hp_sum := sidetrackSum_eq_listSum T len dist p
  have hq_sum := sidetrackSum_eq_listSum T len dist q
  rw [hp] at hp_sum
  rw [hq] at hq_sum
  have hle := lemma3_core len dist P hδ
  rw [hq_len, hp_len, hq_sum, hp_sum]
  linarith [hle]

/-!
# The path graph (§2.3) and the basic algorithm (§2.4, Theorems 1–2).

A node of the paper's path graph `P(G)` is a sidetrack edge; heap edges
walk between sidetracks that share a tree path, and cross edges jump from
a sidetrack to the heap of the tree below its head.  We model a path of
`P(G)` starting from the root directly: a `PPath` is the sidetrack
sequence of an `s–t` walk, where consecutive sidetracks are joined by an
explicit tree walk (the heap-edge segments of `P(G)` are thereby left
implicit).  Its `weight` is the sum of `δ` over the sidetracks, i.e. the
length of the corresponding `P(G)` path (edge weights telescope).

* **Lemma 5.** `s–t` walks in `G` are in length-preserving correspondence
  with `PPath`s (decode/encode), via Lemma 2.
* **Lemma 6.** Extending a `PPath` by a sidetrack of nonnegative `δ`
  cannot decrease its weight (heap-edge weights are nonnegative).
* **Lemma 7.** The tree of `PPath`s (parent = `prefpath`) is heap-ordered
  by weight, via Lemma 3.
* **Theorems 1–2.** Correctness of best-first-search enumeration: every
  `IsBFSTrace` over the path tree is weight-sorted and minimal (from `s`
  to `t`, resp. to every vertex), decodes to `s–t` walks, and every walk
  is represented in the outputs or no shorter than them.  Complexity
  bounds (`O(m + n log n + k log k)` for the basic algorithm) are
  documented here but not formalized: there is no cost model in scope.
-/

/-- Concatenation of two compatible walks. -/
def DiWalk.append {G : Digraph V} {a b c : V} :
    DiWalk G a b → DiWalk G b c → DiWalk G a c
  | .nil _, q => q
  | .cons u v _ h tl, q => .cons u v _ h (tl.append q)

/-- Single-edge walk. -/
def DiWalk.single {G : Digraph V} {a b : V} (h : G.Adj a b) :
    DiWalk G a b :=
  .cons a b b h (.nil b)

/-- Lift a walk in the tree `T` to a walk in `G` (using `T ⊆ G`). -/
def DiWalk.liftT {G T : Digraph V}
    (Tle : ∀ a b : V, T.Adj a b → G.Adj a b) {a b : V} :
    DiWalk T a b → DiWalk G a b
  | .nil u => .nil u
  | .cons u v w h tl => .cons u v w (Tle u v h) (tl.liftT Tle)

/-- Vertices visited by a walk, in order. -/
def DiWalk.vertices {G : Digraph V} {s t : V} : DiWalk G s t → List V
  | .nil u => [u]
  | .cons u _ _ _ tl => u :: tl.vertices

/-- A path of the path graph `P(G)` starting from the root: the sidetrack
sequence of an `s`-rooted walk, with consecutive sidetracks joined by an
explicit tree walk in `T`.  The endpoint index is the head of the last
sidetrack (or `s` for the empty sequence). -/
inductive PPath (G T : Digraph V) (s : V) : V → Type u where
  | root : PPath G T s s
  | sidestep {a : V} (e : V × V) : PPath G T s a → DiWalk T a e.1 →
      G.Adj e.1 e.2 → ¬ T.Adj e.1 e.2 → PPath G T s e.2

/-- The sidetrack sequence underlying a `PPath`. -/
def PPath.sidetrackList {G T : Digraph V} {s c : V} :
    PPath G T s c → List (V × V)
  | .root => []
  | .sidestep e prev _ _ _ => prev.sidetrackList ++ [e]

/-- Weight of a `PPath`: the sum of `δ` over its sidetracks.  This is the
length of the corresponding path in `P(G)` (heap-edge weights telescope),
so an `s–t` walk has length `d(s,t) + weight` by Lemma 2. -/
noncomputable def PPath.weight (len : V → V → ℝ) (dist : V → ℝ)
    {G T : Digraph V} {s c : V} : PPath G T s c → ℝ
  | .root => 0
  | .sidestep e prev _ _ _ => prev.weight len dist + eppDelta len dist e.1 e.2

/-- Parent of a `PPath` in the path tree (`prefpath`: drop the last
sidetrack). -/
def PPath.parent {G T : Digraph V} {s c : V} :
    PPath G T s c → Option (Σ c', PPath G T s c')
  | .root => none
  | .sidestep _ prev _ _ _ => some ⟨_, prev⟩

/-- Child relation in the path tree `H(G)`: `child` extends `par` by a single
sidestep (the converse of `PPath.parent`). -/
def PPath.IsChild {G T : Digraph V} {s : V}
    (child par : Σ c, PPath G T s c) : Prop :=
  ∃ (e : V × V) (tw : DiWalk T par.1 e.1) (hadj : G.Adj e.1 e.2)
    (hside : ¬ T.Adj e.1 e.2),
    child = ⟨e.2, PPath.sidestep e par.2 tw hadj hside⟩

/-- Best-first-search traces over the heap-ordered path tree: the list starts
at `root`, and each new output is a minimum-weight frontier node — a child of
an already-output node that has not been output yet.  These are exactly the
lists the paper's §2.4 algorithm produces (breadth-first search with a
priority queue); tie-breaking between equal-weight frontier nodes is left
arbitrary. -/
inductive IsBFSTrace (G T : Digraph V) (s : V) (len : V → V → ℝ)
    (dist : V → ℝ) : List (Σ c, PPath G T s c) → Prop where
  | root : IsBFSTrace G T s len dist [⟨s, PPath.root⟩]
  | step (L : List (Σ c, PPath G T s c)) (next : Σ c, PPath G T s c) :
      IsBFSTrace G T s len dist L →
      (∃ par ∈ L, PPath.IsChild next par) →
      next ∉ L →
      (∀ y : Σ c, PPath G T s c, (∃ par ∈ L, PPath.IsChild y par) → y ∉ L →
        next.2.weight len dist ≤ y.2.weight len dist) →
      IsBFSTrace G T s len dist (L ++ [next])

theorem listSidetrackSum_append (len : V → V → ℝ) (dist : V → ℝ)
    (L1 L2 : List (V × V)) :
    listSidetrackSum len dist (L1 ++ L2)
      = listSidetrackSum len dist L1 + listSidetrackSum len dist L2 := by
  unfold listSidetrackSum
  rw [List.map_append, List.sum_append]

theorem PPath_weight_eq_listSum (len : V → V → ℝ) (dist : V → ℝ)
    {G T : Digraph V} {s c : V} (q : PPath G T s c) :
    q.weight len dist = listSidetrackSum len dist q.sidetrackList := by
  induction q with
  | root =>
    simp only [PPath.weight, PPath.sidetrackList, listSidetrackSum,
      List.map_nil, List.sum_nil]
  | sidestep e prev tw hadj hside ih =>
    simp only [PPath.weight, PPath.sidetrackList]
    rw [listSidetrackSum_append]
    have hsingle : listSidetrackSum len dist [e]
        = eppDelta len dist e.1 e.2 := by
      simp only [listSidetrackSum, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero]
    rw [hsingle, ih]

theorem DiWalk_sidetracks_append {G : Digraph V} (T : Digraph V)
    {a b c : V} (p : DiWalk G a b) (q : DiWalk G b c) :
    (p.append q).sidetracks T = p.sidetracks T ++ q.sidetracks T := by
  induction p with
  | nil _ =>
    simp only [DiWalk.append, DiWalk.sidetracks, List.nil_append]
  | cons u v w hadj tl ih =>
    simp only [DiWalk.append, DiWalk.sidetracks]
    by_cases h : T.Adj u v
    · simp only [h, ite_true, ih]
    · simp only [h, ite_false, ih, List.cons_append]

theorem DiWalk_liftT_sidetracks {G T : Digraph V}
    (Tle : ∀ a b : V, T.Adj a b → G.Adj a b)
    {a b : V} (r : DiWalk T a b) :
    (r.liftT Tle).sidetracks T = [] := by
  induction r with
  | nil _ =>
    simp only [DiWalk.liftT, DiWalk.sidetracks]
  | cons u v w h tl ih =>
    simp only [DiWalk.liftT, DiWalk.sidetracks]
    have hT : T.Adj u v := h
    simp only [hT, ite_true, ih]

theorem DiWalk_single_sidetracks {G : Digraph V} (T : Digraph V)
    {a b : V} (h : G.Adj a b) (hside : ¬ T.Adj a b) :
    (DiWalk.single h).sidetracks T = [(a, b)] := by
  simp only [DiWalk.single, DiWalk.sidetracks, hside, ite_false]

theorem decode_aux (T : Digraph V)
    {G : Digraph V} {s : V}
    (Tle : ∀ a b : V, T.Adj a b → G.Adj a b)
    {c : V} (q : PPath G T s c) :
    ∃ r : DiWalk G s c, r.sidetracks T = q.sidetrackList := by
  induction q with
  | root =>
    exact ⟨DiWalk.nil s, rfl⟩
  | sidestep e prev tw hadj hside ih =>
    obtain ⟨r_prev, hr_prev⟩ := ih
    refine ⟨r_prev.append ((tw.liftT Tle).append (DiWalk.single hadj)), ?_⟩
    rw [DiWalk_sidetracks_append, DiWalk_sidetracks_append,
      DiWalk_liftT_sidetracks Tle,
      DiWalk_single_sidetracks T hadj hside, hr_prev]
    simp only [PPath.sidetrackList]
    cases e with
    | mk e1 e2 =>
      simp only [List.nil_append]

theorem encode_aux {G T : Digraph V} {s : V} {a b : V} (p : DiWalk G a b) :
    ∀ {a0 : V} (q : PPath G T s a0) (tw : DiWalk T a0 a),
      ∃ (c : V) (q' : PPath G T s c),
        q'.sidetrackList = q.sidetrackList ++ p.sidetracks T := by
  induction p with
  | nil u =>
    intro a0 q tw
    exact ⟨a0, q, by simp only [DiWalk.sidetracks, List.append_nil]⟩
  | cons u v w hadj tl ih =>
    intro a0 q tw
    by_cases hT : T.Adj u v
    · have hp : (DiWalk.cons u v w hadj tl).sidetracks T
          = tl.sidetracks T := by
        simp only [DiWalk.sidetracks, hT, ite_true]
      have tw' : DiWalk T a0 v := tw.append (DiWalk.single hT)
      obtain ⟨c, q', hq'⟩ := ih q tw'
      refine ⟨c, q', ?_⟩
      rw [hp]
      exact hq'
    · have hp : (DiWalk.cons u v w hadj tl).sidetracks T
          = (u, v) :: tl.sidetracks T := by
        simp only [DiWalk.sidetracks, hT, ite_false]
      let q1 : PPath G T s v := PPath.sidestep (u, v) q tw hadj hT
      have hq1 : q1.sidetrackList = q.sidetrackList ++ [(u, v)] := rfl
      obtain ⟨c, q', hq'⟩ := ih q1 (DiWalk.nil v)
      rw [hq1] at hq'
      have heq : (q.sidetrackList ++ [(u, v)]) ++ tl.sidetracks T
          = q.sidetrackList ++ ((u, v) :: tl.sidetracks T) := by
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      rw [heq] at hq'
      refine ⟨c, q', ?_⟩
      rw [hp]
      exact hq'

/-- Lemma 5 (decode): every `PPath` determines an `s–t` walk with the same
sidetracks, of length `d(s,t) + weight` (length preservation is Lemma 2:
tree segments contribute `δ = 0` by Lemma 1, and the final tree walk to
`t` is `treeWalk`). -/
theorem lemma5_decode (T : Digraph V) (len : V → V → ℝ)
    (dist : V → ℝ) {G : Digraph V} {s t : V}
    (Tle : ∀ a b : V, T.Adj a b → G.Adj a b)
    (treeWalk : ∀ a : V, DiWalk T a t)
    (hdist_t : dist t = 0)
    (htight : ∀ a b : V, T.Adj a b → eppDelta len dist a b = 0)
    {c : V} (q : PPath G T s c) :
    ∃ p : DiWalk G s t, p.sidetracks T = q.sidetrackList ∧
      p.length len = dist s + q.weight len dist := by
  obtain ⟨r, hr⟩ := decode_aux T Tle q
  have hp_side : (r.append ((treeWalk c).liftT Tle)).sidetracks T
      = q.sidetrackList := by
    rw [DiWalk_sidetracks_append, hr, DiWalk_liftT_sidetracks Tle,
      List.append_nil]
  have hp_len : (r.append ((treeWalk c).liftT Tle)).length len
      = dist s + q.weight len dist := by
    have h1 := lemma2_path_length T len dist hdist_t htight
      (r.append ((treeWalk c).liftT Tle))
    have h2 := sidetrackSum_eq_listSum T len dist
      (r.append ((treeWalk c).liftT Tle))
    have h3 := PPath_weight_eq_listSum len dist q
    rw [h2, hp_side, ← h3] at h1
    exact h1
  exact ⟨_, hp_side, hp_len⟩

/-- Lemma 5 (encode): every `s–t` walk arises from a `PPath` with the same
sidetrack sequence (its tree segments become the joining tree walks). -/
theorem lemma5_encode (T : Digraph V) (len : V → V → ℝ)
    (dist : V → ℝ) {G : Digraph V} {s t : V}
    (Tle : ∀ a b : V, T.Adj a b → G.Adj a b)
    (treeWalk : ∀ a : V, DiWalk T a t)
    (p : DiWalk G s t) :
    ∃ (c : V) (q : PPath G T s c), q.sidetrackList = p.sidetracks T := by
  obtain ⟨c, q, hq⟩ := encode_aux p PPath.root (DiWalk.nil s)
  refine ⟨c, q, ?_⟩
  simpa [PPath.sidetrackList] using hq

/-- Lemma 6 (nonnegative extension): appending a sidetrack of nonnegative
`δ` (Lemma 1) cannot decrease a `PPath`'s weight.  This is the content of
the paper's Lemma 6 that heap/cross edges of `P(G)` have nonnegative
weight. -/
theorem lemma6_weight_mono (len : V → V → ℝ) (dist : V → ℝ)
    {G T : Digraph V} {s a : V} (q : PPath G T s a) (e : V × V)
    (tw : DiWalk T a e.1) (hadj : G.Adj e.1 e.2) (hside : ¬ T.Adj e.1 e.2)
    (hδ : 0 ≤ eppDelta len dist e.1 e.2) :
    q.weight len dist ≤ (PPath.sidestep e q tw hadj hside).weight len dist := by
  simp only [PPath.weight]
  linarith [hδ]

/-- Lemma 7 (heap-ordered path tree): a `PPath` weighs no less than its
parent (`prefpath`), provided every sidetrack has nonnegative `δ`.
This is Lemma 3 lifted to the path tree `H(G)`. -/
theorem lemma7_parent_weight (len : V → V → ℝ) (dist : V → ℝ)
    {G T : Digraph V} {s c : V} (q : PPath G T s c)
    {c' : V} {q' : PPath G T s c'} (hpar : q.parent = some ⟨c', q'⟩)
    (hnn : ∀ e ∈ q.sidetrackList, 0 ≤ eppDelta len dist e.1 e.2) :
    q'.weight len dist ≤ q.weight len dist := by
  cases q with
  | root =>
    simp only [PPath.parent] at hpar
    cases hpar
  | sidestep e prev tw hadj hside =>
    simp only [PPath.parent] at hpar
    have hEq : ((⟨_, prev⟩ : Σ c, PPath G T s c)) = ⟨c', q'⟩ :=
      Option.some_inj.mp hpar
    have hW : prev.weight len dist = q'.weight len dist :=
      congrArg (fun x => x.2.weight len dist) hEq
    have hmem : e ∈ (PPath.sidestep e prev tw hadj hside).sidetrackList := by
      simp only [PPath.sidetrackList, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, or_true]
    have hδ : 0 ≤ eppDelta len dist e.1 e.2 := hnn e hmem
    have hWeight : (PPath.sidestep e prev tw hadj hside).weight len dist
        = prev.weight len dist + eppDelta len dist e.1 e.2 := by
      simp only [PPath.weight]
    rw [hWeight, ← hW]
    linarith [hδ]

-- PPath weights are nonneg under triangle inequality (uses lemma1_all_nonneg)
theorem PPath_weight_nonneg {G T : Digraph V} {s : V}
    (len : V → V → ℝ) (dist : V → ℝ)
    (htri : ∀ a b : V, G.Adj a b → dist a ≤ len a b + dist b)
    {c : V} (q : PPath G T s c) : 0 ≤ q.weight len dist := by
  induction q with
  | root =>
    simp only [PPath.weight, le_refl]
  | sidestep e prev tw hadj hside ih =>
    simp only [PPath.weight]
    have hδ : 0 ≤ eppDelta len dist e.1 e.2 :=
      lemma1_all_nonneg len dist htri hadj
    linarith [ih]

theorem trace_root_mem {G T : Digraph V} {s : V}
    (len : V → V → ℝ) (dist : V → ℝ)
    {L : List (Σ c, PPath G T s c)} (h : IsBFSTrace G T s len dist L) :
    (⟨s, PPath.root⟩ : Σ c, PPath G T s c) ∈ L := by
  induction h with
  | root =>
    simp only [List.mem_singleton]
  | step L next hTrace hChild hNotMem hMin ih =>
    exact List.mem_append_left _ ih

theorem pairwise_append {α : Type*} {R : α → α → Prop}
    {l₁ l₂ : List α}
    (h₁ : l₁.Pairwise R) (h₂ : l₂.Pairwise R)
    (hcross : ∀ x ∈ l₁, ∀ y ∈ l₂, R x y) :
    (l₁ ++ l₂).Pairwise R := by
  induction l₁ with
  | nil =>
    simpa using h₂
  | cons a t ih =>
    cases h₁ with
    | cons h_head h_tail =>
      have hcross_t : ∀ x ∈ t, ∀ y ∈ l₂, R x y := by
        intro x hx y hy
        exact hcross x (List.mem_cons.mpr (Or.inr hx)) y hy
      have ih' := ih h_tail hcross_t
      apply List.Pairwise.cons
      · intro y hy
        have hOr := List.mem_append.mp hy
        cases hOr with
        | inl hyt =>
          exact h_head y hyt
        | inr hyl2 =>
          exact hcross a (List.mem_cons.mpr (Or.inl rfl)) y hyl2
      · exact ih'

theorem complete_of_minimal (T : Digraph V) (len : V → V → ℝ)
    (dist : V → ℝ) {G : Digraph V} {s t : V}
    (Tle : ∀ a b : V, T.Adj a b → G.Adj a b)
    (treeWalk : ∀ a : V, DiWalk T a t)
    (hdist_t : dist t = 0)
    (htight : ∀ a b : V, T.Adj a b → eppDelta len dist a b = 0)
    (L : List (Σ c, PPath G T s c))
    (hMin : ∀ x ∈ L, ∀ y : Σ c, PPath G T s c, y ∉ L →
      x.2.weight len dist ≤ y.2.weight len dist) :
    (∀ y : DiWalk G s t,
      (∃ q : Σ c, PPath G T s c,
        q ∈ L ∧ q.2.sidetrackList = y.sidetracks T) ∨
      (∀ x ∈ L, ∀ p : DiWalk G s t,
        p.sidetracks T = x.2.sidetrackList →
        p.length len = dist s + x.2.weight len dist →
        p.length len ≤ y.length len)) := by
  intro y
  obtain ⟨c, q, hq_list⟩ := lemma5_encode T len dist Tle treeWalk y
  let qSig : Σ c, PPath G T s c := ⟨c, q⟩
  by_cases hmem : qSig ∈ L
  · left
    exact ⟨qSig, hmem, hq_list⟩
  · right
    intro x hx p hp_side hp_len
    have hMin_xq : x.2.weight len dist ≤ qSig.2.weight len dist :=
      hMin x hx qSig hmem
    have hy_len : y.length len = dist s + qSig.2.weight len dist := by
      have h1 := lemma2_path_length T len dist hdist_t htight y
      have h2 := sidetrackSum_eq_listSum T len dist y
      have h3 := PPath_weight_eq_listSum len dist q
      rw [h2] at h1
      rw [← hq_list] at h1
      rw [← h3] at h1
      exact h1
    rw [hp_len, hy_len]
    linarith [hMin_xq]

/-- Theorem 1 (basic algorithm, correctness): every best-first-search trace
over the path tree lists shortest paths first — `L` is duplicate-free,
weight-sorted, and every path outside `L` weighs at least as much as every
path inside it.  Each output decodes to an `s–t` walk of length
`d(s,t) + weight` (Lemma 5, decode direction), and every `s–t` walk is
either represented in `L` or no shorter than every output.  This is the
paper's §2.4 claim ("output the shortest paths in order", `O(log i)` per
path); complexity bounds are not formalized (no cost model).
Unlike a bare `∃ L` existence claim (which an oracle could provide), this
states correctness of the lists the algorithm produces (`IsBFSTrace`:
successive frontier minima).  Neither `δ`-fact is assumed.  No finiteness
hypothesis: correctness is universal over traces; only the existence of
length-`k` traces would need a finite graph.  `T` is a spanning tree
(`htree`: unique tree walks), so Lemma 5 is a bijection: every walk has a
unique `PPath`. -/
theorem thm1_bfs_enumeration (T : Digraph V) (len : V → V → ℝ)
    (dist : V → ℝ) {G : Digraph V} {s t : V}
    (Tle : ∀ a b : V, T.Adj a b → G.Adj a b)
    (treeWalk : ∀ a : V, DiWalk T a t)
    (htree : ∀ a b (p q : DiWalk T a b), p = q)
    (hdist_t : dist t = 0)
    (htight : ∀ a b : V, T.Adj a b → len a b + dist b = dist a)
    (htri : ∀ a b : V, G.Adj a b → dist a ≤ len a b + dist b) :
    ∀ L : List (Σ c, PPath G T s c), IsBFSTrace G T s len dist L →
      L.Nodup ∧
      L.Pairwise (fun x y => x.2.weight len dist ≤ y.2.weight len dist) ∧
      (∀ x ∈ L, ∀ y : Σ c, PPath G T s c, y ∉ L →
        x.2.weight len dist ≤ y.2.weight len dist) ∧
      (∀ x ∈ L, ∃ p : DiWalk G s t,
        p.sidetracks T = x.2.sidetrackList ∧
        p.length len = dist s + x.2.weight len dist) ∧
      (∀ y : DiWalk G s t,
        (∃ q : Σ c, PPath G T s c,
          q ∈ L ∧ q.2.sidetrackList = y.sidetracks T) ∨
        (∀ x ∈ L, ∀ p : DiWalk G s t,
          p.sidetracks T = x.2.sidetrackList →
          p.length len = dist s + x.2.weight len dist →
          p.length len ≤ y.length len)) := by
  have htight_delta : ∀ a b : V, T.Adj a b → eppDelta len dist a b = 0 :=
    fun a b h => lemma1_delta_tree len dist (htight a b h)
  intro L hTrace
  induction hTrace with
  | root =>
    have hNodup : ([(⟨s, PPath.root⟩ : Σ c, PPath G T s c)]).Nodup := by
      exact List.Pairwise.cons (by simp) List.Pairwise.nil
    have hPair : ([(⟨s, PPath.root⟩ : Σ c, PPath G T s c)]).Pairwise
        (fun x y => x.2.weight len dist ≤ y.2.weight len dist) := by
      exact List.Pairwise.cons (by simp) List.Pairwise.nil
    have hMin : ∀ x ∈ [(⟨s, PPath.root⟩ : Σ c, PPath G T s c)],
        ∀ y : Σ c, PPath G T s c, y ∉ [(⟨s, PPath.root⟩ : Σ c, PPath G T s c)] →
        x.2.weight len dist ≤ y.2.weight len dist := by
      intro x hx y hy
      have hx_eq := List.mem_singleton.mp hx
      subst hx_eq
      obtain ⟨c, q⟩ := y
      show (PPath.root : PPath G T s s).weight len dist ≤ q.weight len dist
      have hRoot : (PPath.root : PPath G T s s).weight len dist = 0 := rfl
      rw [hRoot]
      exact PPath_weight_nonneg len dist htri q
    have hDec : ∀ x ∈ [(⟨s, PPath.root⟩ : Σ c, PPath G T s c)],
        ∃ p : DiWalk G s t,
        p.sidetracks T = x.2.sidetrackList ∧
        p.length len = dist s + x.2.weight len dist := by
      intro x hx
      exact lemma5_decode T len dist Tle treeWalk hdist_t htight_delta x.2
    have hComp := complete_of_minimal T len dist Tle treeWalk hdist_t
      htight_delta [(⟨s, PPath.root⟩ : Σ c, PPath G T s c)] hMin
    exact ⟨hNodup, hPair, hMin, hDec, hComp⟩
  | step L next hTrace hChild hNotMem hMinChoice ih =>
    obtain ⟨hNodupL, hPairL, hMinL, hDecL, hCompL⟩ := ih
    have hNodup' : (L ++ [next]).Nodup := by
      have hSingle : ([next].Pairwise (· ≠ ·)) :=
        List.Pairwise.cons (by simp) List.Pairwise.nil
      have hcross : ∀ x ∈ L, ∀ y ∈ [next], x ≠ y := by
        intro x hx y hy
        have hy_eq := List.mem_singleton.mp hy
        rw [hy_eq]
        intro hEq
        rw [hEq] at hx
        exact hNotMem hx
      exact pairwise_append hNodupL hSingle hcross
    have hPair' : (L ++ [next]).Pairwise
        (fun x y => x.2.weight len dist ≤ y.2.weight len dist) := by
      have hSingle : ([next].Pairwise
          (fun x y => x.2.weight len dist ≤ y.2.weight len dist)) :=
        List.Pairwise.cons (by simp) List.Pairwise.nil
      have hcross : ∀ x ∈ L, ∀ y ∈ [next],
          x.2.weight len dist ≤ y.2.weight len dist := by
        intro x hx y hy
        have hy_eq := List.mem_singleton.mp hy
        rw [hy_eq]
        exact hMinL x hx next hNotMem
      exact pairwise_append hPairL hSingle hcross
    have hNextMin : ∀ y : Σ c, PPath G T s c, y ∉ L ++ [next] →
        next.2.weight len dist ≤ y.2.weight len dist := by
      have hAux : ∀ {c : V} (q : PPath G T s c),
          (⟨c, q⟩ : Σ c, PPath G T s c) ∉ L ++ [next] →
          next.2.weight len dist ≤
            (⟨c, q⟩ : Σ c, PPath G T s c).2.weight len dist := by
        intro c q
        induction q with
        | root =>
          intro hy
          have hRootL : (⟨s, PPath.root⟩ : Σ c, PPath G T s c) ∈ L :=
            trace_root_mem len dist hTrace
          have hRootL' : (⟨s, PPath.root⟩ : Σ c, PPath G T s c) ∈ L ++ [next] :=
            List.mem_append.mpr (Or.inl hRootL)
          exact absurd hRootL' hy
        | sidestep e prev tw hadj hside ih2 =>
          intro hy
          have hδ : 0 ≤ eppDelta len dist e.1 e.2 :=
            lemma1_all_nonneg len dist htri hadj
          have hPrevLe : prev.weight len dist ≤
              (PPath.sidestep e prev tw hadj hside).weight len dist :=
            lemma6_weight_mono len dist prev e tw hadj hside hδ
          by_cases hPrevMem : (⟨_, prev⟩ : Σ c, PPath G T s c) ∈ L ++ [next]
          · have hOrPrev := List.mem_append.mp hPrevMem
            cases hOrPrev with
            | inl hInL =>
              have hyL : (⟨e.2, PPath.sidestep e prev tw hadj hside⟩ :
                  Σ c, PPath G T s c) ∉ L := by
                intro h
                exact hy (List.mem_append.mpr (Or.inl h))
              have hFront : ∃ par ∈ L, PPath.IsChild
                  (⟨e.2, PPath.sidestep e prev tw hadj hside⟩ :
                    Σ c, PPath G T s c) par := by
                exact ⟨⟨_, prev⟩, hInL, e, tw, hadj, hside, rfl⟩
              exact hMinChoice _ hFront hyL
            | inr hInSingle =>
              have heq := List.mem_singleton.mp hInSingle
              have hEqW : prev.weight len dist = next.2.weight len dist :=
                congrArg (fun x => x.2.weight len dist) heq
              show next.2.weight len dist ≤
                (PPath.sidestep e prev tw hadj hside).weight len dist
              linarith [hPrevLe, hEqW]
          · have hNextPrev : next.2.weight len dist ≤
                (⟨_, prev⟩ : Σ c, PPath G T s c).2.weight len dist :=
              ih2 hPrevMem
            have h1 : next.2.weight len dist ≤ prev.weight len dist :=
              hNextPrev
            have h2 : prev.weight len dist ≤
                (⟨e.2, PPath.sidestep e prev tw hadj hside⟩ :
                  Σ c, PPath G T s c).2.weight len dist :=
              hPrevLe
            exact le_trans h1 h2
      intro y hy
      obtain ⟨c, q⟩ := y
      exact hAux q hy
    have hMin' : ∀ x ∈ L ++ [next], ∀ y : Σ c, PPath G T s c,
        y ∉ L ++ [next] → x.2.weight len dist ≤ y.2.weight len dist := by
      intro x hx y hy
      have hOr := List.mem_append.mp hx
      cases hOr with
      | inl hxL =>
        have hyL : y ∉ L := fun h => hy (List.mem_append.mpr (Or.inl h))
        exact hMinL x hxL y hyL
      | inr hxSingle =>
        have hx_eq := List.mem_singleton.mp hxSingle
        rw [hx_eq]
        exact hNextMin y hy
    have hDec' : ∀ x ∈ L ++ [next], ∃ p : DiWalk G s t,
        p.sidetracks T = x.2.sidetrackList ∧
        p.length len = dist s + x.2.weight len dist := by
      intro x hx
      exact lemma5_decode T len dist Tle treeWalk hdist_t htight_delta x.2
    have hComp' := complete_of_minimal T len dist Tle treeWalk hdist_t
      htight_delta (L ++ [next]) hMin'
    exact ⟨hNodup', hPair', hMin', hDec', hComp'⟩

/-- Theorem 2 (one source, all destinations, correctness): for every target
`t`, every best-first-search trace over the path tree of `T t` is correct
as in Theorem 1 (duplicate-free, weight-sorted, minimal, decoding to
`s–t` walks with `length = dist t s + weight`, represented-or-longer
completeness).  `htree` gives unique tree walks (spanning tree), hence
the Lemma 5 bijection, as in Theorem 1.  (The paper applies the
construction to the reversed graph `Gᴿ` with destination `s`; here the
per-target trees are taken as parameters.)  Complexity
`O(m + n log n + kn log k)` not formalized. -/
theorem thm2_all_dests (len : V → V → ℝ) (dist : V → V → ℝ)
    {G : Digraph V} {s : V}
    (T : V → Digraph V)
    (Tle : ∀ t a b : V, (T t).Adj a b → G.Adj a b)
    (treeWalk : ∀ t a : V, DiWalk (T t) a t)
    (htree : ∀ t a b (p q : DiWalk (T t) a b), p = q)
    (hdist : ∀ t : V, dist t t = 0)
    (htight : ∀ t a b : V, (T t).Adj a b → len a b + dist t b = dist t a)
    (htri : ∀ t a b : V, G.Adj a b → dist t a ≤ len a b + dist t b) :
    ∀ t : V, ∀ L : List (Σ c, PPath G (T t) s c),
      IsBFSTrace G (T t) s len (dist t) L →
      L.Nodup ∧
      L.Pairwise (fun x y => x.2.weight len (dist t) ≤ y.2.weight len (dist t)) ∧
      (∀ x ∈ L, ∀ y : Σ c, PPath G (T t) s c, y ∉ L →
        x.2.weight len (dist t) ≤ y.2.weight len (dist t)) ∧
      (∀ x ∈ L, ∃ p : DiWalk G s t,
        p.sidetracks (T t) = x.2.sidetrackList ∧
        p.length len = dist t s + x.2.weight len (dist t)) ∧
      (∀ y : DiWalk G s t,
        (∃ q : Σ c, PPath G (T t) s c,
          q ∈ L ∧ q.2.sidetrackList = y.sidetracks (T t)) ∨
        (∀ x ∈ L, ∀ p : DiWalk G s t,
          p.sidetracks (T t) = x.2.sidetrackList →
          p.length len = dist t s + x.2.weight len (dist t) →
          p.length len ≤ y.length len)) := by
  intro t L hL
  exact thm1_bfs_enumeration (T t) len (dist t) (Tle t) (treeWalk t)
    (htree t) (hdist t) (htight t) (htri t) L hL

end Cslib.Algorithms.Lean.KShortestPathsEppstein
