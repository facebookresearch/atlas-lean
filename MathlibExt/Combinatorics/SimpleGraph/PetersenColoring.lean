/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Bridgeless
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Set.Card
public import Mathlib.Data.ZMod.Basic

import Mathlib.Tactic.Eval
import Mathlib.Tactic.FinCases

/-!
# A counterexample to the Petersen coloring conjecture

The theorem `conjecture_refuted` uses the 52-vertex construction of Goedgebeur, Jooken,
Máčajová, Mattiolo, Mazzuoccolo and Ulyanov. We enumerate the possible edge colors at the
boundary of their four-pole, then compose two four-poles in each of three sectors.

## Record carried over from the retired wanted module

From `WantedExt/GraphTheory/PetersenColoringConjectureWanted.lean`:

Source record `OPG-143` (UnsolvedMath numeric id `3196`).

Graphs are finite simple graphs, so parallel edges are excluded from the model
(see the registry adequacy gaps). The `Bool` layer `false` is the outer 5-cycle
(`i -- i+1`) and the `Bool` layer `true` is the inner 5-star (`i -- i+2`),
joined by the spokes `(i, false) -- (i, true)`. Since `1 ≠ 0` and `2 ≠ 0` in
`ZMod 5`, every generator below joins distinct vertices, so the edge set is
loop-free and `SimpleGraph.fromEdgeSet` retains all of it.

This Petersen representation is intentionally distinct from
`PetersenMinorFourFlow.PetersenAdj`: that entry models branch sets in a host
multigraph (tail/head edges, `Sum (ZMod 5) (ZMod 5)` vertices), while a
Petersen coloring maps edges between simple graphs, so this entry uses a
`SimpleGraph` on `ZMod 5 × Bool` with incidence via `SimpleGraph.incidenceSet`.
Bridgelessness uses the canonical `SimpleGraph.IsBridgeless` predicate.

Historical references: the registry adequacy gaps and the `PetersenMinorFourFlow.PetersenAdj` entry
named above came from Formal-Math with the retired wanted module and do not resolve in ATLAS.
-/

@[expose] public section

namespace MathlibExt.GraphTheory.PetersenColoringConjectureWanted

/-- **Vertices of the Petersen graph.** The vertex set of the Petersen graph is
$\mathbb{Z}/5\mathbb{Z} \times \{\mathrm{false}, \mathrm{true}\}$; the vertices
$(i, \mathrm{false})$ with $i \in \mathbb{Z}/5\mathbb{Z}$ form the outer 5-cycle and the vertices
$(i, \mathrm{true})$ form the inner 5-star. -/
abbrev PVertex := ZMod 5 × Bool

/-- **Edges of the Petersen graph.** The edge set of the Petersen graph on
$\mathbb{Z}/5\mathbb{Z} \times \{\mathrm{false}, \mathrm{true}\}$ consists of the unordered
pairs $\{(i, \mathrm{false}), (i + 1, \mathrm{false})\}$ (the outer 5-cycle),
$\{(i, \mathrm{false}), (i, \mathrm{true})\}$ (the spokes) and
$\{(i, \mathrm{true}), (i + 2, \mathrm{true})\}$ (the inner 5-star), for
$i \in \mathbb{Z}/5\mathbb{Z}$. -/
def petersenEdgeSet : Set (Sym2 PVertex) :=
  {e | ∃ i : ZMod 5, e = s((i, false), (i + 1, false))} ∪
    {e | ∃ i : ZMod 5, e = s((i, false), (i, true))} ∪
      {e | ∃ i : ZMod 5, e = s((i, true), (i + 2, true))}

/-- **Petersen graph.** The Petersen graph is the simple graph on
$\mathbb{Z}/5\mathbb{Z} \times \{\mathrm{false}, \mathrm{true}\}$ whose edges are the outer
5-cycle edges $\{(i, \mathrm{false}), (i + 1, \mathrm{false})\}$, the spokes
$\{(i, \mathrm{false}), (i, \mathrm{true})\}$ and the inner 5-star edges
$\{(i, \mathrm{true}), (i + 2, \mathrm{true})\}$ for $i \in \mathbb{Z}/5\mathbb{Z}$. -/
def petersenGraph : SimpleGraph PVertex := SimpleGraph.fromEdgeSet petersenEdgeSet

/-- **Petersen coloring.** Let $G$ be a simple graph on a vertex type $V$ and let $P$ be the
Petersen graph. A map $f$ from unordered pairs of vertices of $G$ to unordered pairs of vertices
of $P$ is a Petersen coloring of $G$ when $f$ sends every edge of $G$ to an edge of $P$ and, for
every vertex $v$ of $G$, there is a vertex $w$ of $P$ such that $f$ maps the set of edges of $G$
incident to $v$ bijectively onto the set of edges of $P$ incident to $w$. -/
def IsPetersenColoring {V : Type*} (G : SimpleGraph V)
    (f : Sym2 V → Sym2 PVertex) : Prop :=
  (∀ e ∈ G.edgeSet, f e ∈ petersenGraph.edgeSet) ∧
    ∀ v : V, ∃ w : PVertex,
      Set.BijOn f (G.incidenceSet v) (petersenGraph.incidenceSet w)

/-- **Petersen coloring conjecture.** For every finite vertex type $V$ and every simple graph $G$
on $V$, if every vertex of $G$ has exactly three neighbors and $G$ is bridgeless, then $G$ admits
a Petersen coloring. -/
def conjecture : Prop :=
  ∀ (V : Type) [Finite V] (G : SimpleGraph V),
    (∀ v, (G.neighborSet v).ncard = 3) → G.IsBridgeless →
      ∃ f : Sym2 V → Sym2 PVertex, IsPetersenColoring G f

private abbrev Vertex := Fin 52

-- Vertices 17i,...,17i+16 form sector i. Its first and second blocks of eight
-- are the two four-poles; vertex 17i+16 joins them to the center, vertex 51.
private def neighbors (v : Vertex) : List Vertex :=
  (#[
    [1, 4, 39], [0, 2, 5], [1, 3, 6], [2, 7, 16],
    [0, 6, 7], [1, 7, 17], [2, 4, 8], [3, 4, 5],
    [6, 9, 12], [8, 10, 13], [9, 11, 14], [10, 15, 31],
    [8, 14, 15], [9, 15, 16], [10, 12, 45], [11, 12, 13],
    [3, 13, 51], [5, 18, 21], [17, 19, 22], [18, 20, 23],
    [19, 24, 33], [17, 23, 24], [18, 24, 34], [19, 21, 25],
    [20, 21, 22], [23, 26, 29], [25, 27, 30], [26, 28, 31],
    [27, 32, 48], [25, 31, 32], [26, 32, 33], [11, 27, 29],
    [28, 29, 30], [20, 30, 51], [22, 35, 38], [34, 36, 39],
    [35, 37, 40], [36, 41, 50], [34, 40, 41], [0, 35, 41],
    [36, 38, 42], [37, 38, 39], [40, 43, 46], [42, 44, 47],
    [43, 45, 48], [14, 44, 49], [42, 48, 49], [43, 49, 50],
    [28, 44, 46], [45, 46, 47], [37, 47, 51], [16, 33, 50]] : Array (List Vertex))[v.val]!

private def witness : SimpleGraph Vertex where
  Adj u v := v ∈ neighbors u
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide⟩

private instance witnessDecidableAdj : DecidableRel witness.Adj :=
  fun u v => inferInstanceAs (Decidable (v ∈ neighbors u))

private theorem cubic (v : Vertex) : (witness.neighborSet v).ncard = 3 := by
  rw [SimpleGraph.ncard_neighborSet]
  exact (by decide : ∀ u, witness.degree u = 3) v

-- Search non-backtracking walks in the graph with the specified edge deleted.
private def detour (edge : Sym2 Vertex) (dst prev cur : Vertex) : Nat → Bool
  | 0 => cur == dst
  | n + 1 => cur == dst || (neighbors cur).any fun y =>
      y != prev && s(cur, y) != edge && detour edge dst cur y n

private theorem detour_sound {edge dst prev cur n} (h : detour edge dst prev cur n) :
    (witness.deleteEdges {edge}).Reachable cur dst := by
  induction n generalizing prev cur with
  | zero =>
    have he : cur = dst := by simpa [detour] using h
    exact he ▸ SimpleGraph.Reachable.rfl
  | succ n ih =>
    simp only [detour, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
      Bool.and_eq_true, bne_iff_ne] at h
    obtain h | ⟨y, hy, ⟨_, he⟩, ht⟩ := h
    · exact h ▸ SimpleGraph.Reachable.rfl
    · exact (SimpleGraph.Adj.reachable (SimpleGraph.deleteEdges_adj.mpr
        ⟨show witness.Adj cur y from hy, he⟩)).trans (ih ht)

private theorem bridgeless : witness.IsBridgeless := by
  have walks : ∀ u : Vertex, ∀ v ∈ neighbors u, detour s(u, v) v u u 9 := by decide +kernel
  rintro ⟨u, v⟩ huv
  exact fun hb => SimpleGraph.isBridge_iff.mp hb (detour_sound (walks u v huv))

-- Number the outer edges 0–4, the spokes 5–9, and the inner edges 10–14.
private abbrev Color := Fin 15

-- For a fixed first edge, the four ways to complete an ordered star at either endpoint.
private def extensions (a : Color) : List (Color × Color) :=
  (#[
    [(4, 5), (5, 4), (1, 6), (6, 1)],
    [(0, 6), (6, 0), (2, 7), (7, 2)],
    [(1, 7), (7, 1), (3, 8), (8, 3)],
    [(2, 8), (8, 2), (4, 9), (9, 4)],
    [(0, 5), (5, 0), (3, 9), (9, 3)],
    [(0, 4), (4, 0), (10, 13), (13, 10)],
    [(1, 0), (0, 1), (11, 14), (14, 11)],
    [(2, 1), (1, 2), (12, 10), (10, 12)],
    [(3, 2), (2, 3), (13, 11), (11, 13)],
    [(4, 3), (3, 4), (14, 12), (12, 14)],
    [(13, 5), (5, 13), (12, 7), (7, 12)],
    [(14, 6), (6, 14), (13, 8), (8, 13)],
    [(10, 7), (7, 10), (14, 9), (9, 14)],
    [(10, 5), (5, 10), (11, 8), (8, 11)],
    [(11, 6), (6, 11), (12, 9), (9, 12)]] : Array (List (Color × Color)))[a.val]!

private def targetEdge (c : Color) : Sym2 PVertex :=
  let i : ZMod 5 := c.val
  if c.val < 5 then s((i, false), (i + 1, false)) else
    if c.val < 10 then s((i, false), (i, true)) else s((i, true), (i + 2, true))

private theorem numbered {e : Sym2 PVertex} (he : e ∈ petersenGraph.edgeSet) :
    ∃ c, targetEdge c = e := by
  rw [petersenGraph, SimpleGraph.edgeSet_fromEdgeSet] at he
  rcases he.1 with (⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩
  · exact (by decide : ∀ i : ZMod 5, ∃ c, targetEdge c = s((i, false), (i + 1, false))) i
  · exact (by decide : ∀ i : ZMod 5, ∃ c, targetEdge c = s((i, false), (i, true))) i
  · exact (by decide : ∀ i : ZMod 5, ∃ c, targetEdge c = s((i, true), (i + 2, true))) i

open scoped Classical in
private noncomputable def number (e : Sym2 PVertex) : Color :=
  if h : ∃ c, targetEdge c = e then h.choose else 0

private theorem number_spec {e : Sym2 PVertex} (he : e ∈ petersenGraph.edgeSet) :
    targetEdge (number e) = e := by
  simp only [number, dite_eq_left (numbered he), (numbered he).choose_spec]

private theorem targetStar :
    ∀ v : PVertex, ∀ a b c : Color, v ∈ targetEdge a → v ∈ targetEdge b → v ∈ targetEdge c →
      a ≠ b → a ≠ c → b ≠ c → (b, c) ∈ extensions a := by
  decide +kernel

private noncomputable def paint (f : Sym2 Vertex → Sym2 PVertex) (v w : Vertex) : Color :=
  number (f s(min v w, max v w))

private theorem paint_eq (f : Sym2 Vertex → Sym2 PVertex) (v w : Vertex) :
    paint f v w = number (f s(v, w)) := by
  by_cases h : v ≤ w
  · simp [paint, min_eq_left h, max_eq_right h]
  · simp [paint, min_eq_right (le_of_not_ge h), max_eq_left (le_of_not_ge h), Sym2.eq_swap]

private theorem paint_comm (f : Sym2 Vertex → Sym2 PVertex) (v w : Vertex) :
    paint f v w = paint f w v := by rw [paint, min_comm, max_comm, paint]

private def IsStar (v a b c : Vertex) : Prop :=
  a ∈ neighbors v ∧ b ∈ neighbors v ∧ c ∈ neighbors v ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c

private instance isStarDecidable (v a b c : Vertex) : Decidable (IsStar v a b c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

private theorem atVertex {f : Sym2 Vertex → Sym2 PVertex} (hf : IsPetersenColoring witness f)
    {v a b c : Vertex} (h : IsStar v a b c) :
    (paint f v b, paint f v c) ∈ extensions (paint f v a) := by
  obtain ⟨w, hw⟩ := hf.2 v
  have inc {x : Vertex} (hx : x ∈ neighbors v) : s(v, x) ∈ witness.incidenceSet v :=
    witness.mk'_mem_incidenceSet_left_iff.mpr hx
  have eqn {x : Vertex} (hx : x ∈ neighbors v) :
      targetEdge (paint f v x) = f s(v, x) := by
    rw [paint_eq]
    exact number_spec (hf.1 _ hx)
  have mem {x : Vertex} (hx : x ∈ neighbors v) : w ∈ targetEdge (paint f v x) := by
    rw [eqn hx]
    exact (hw.mapsTo (inc hx)).2
  have inj {x y : Vertex} (hx : x ∈ neighbors v) (hy : y ∈ neighbors v)
      (he : paint f v x = paint f v y) : x = y := by
    have eqImage := (eqn hx).symm.trans ((congrArg targetEdge he).trans (eqn hy))
    have hi := hw.injOn (inc hx) (inc hy) eqImage
    rcases Sym2.eq_iff.mp hi with h | h
    · exact h.2
    · exact h.2.trans h.1
  obtain ⟨ha, hb, hc, hab, hac, hbc⟩ := h
  exact targetStar w _ _ _ (mem ha) (mem hb) (mem hc)
    (fun e => hab (inj ha hb e)) (fun e => hac (inj ha hc e)) (fun e => hbc (inj hb hc e))

-- The four-pole is the Petersen graph with the ends of one spoke removed.
-- Its first two ports determine at most two possibilities for the last two ports.
private def boundary (a b : Color) : List (Color × Color) :=
  if a = b || (extensions a).any (fun p => p.1 == b) then [(a, b)] else
    let crossed := (extensions a).flatMap fun (x, t) =>
      ((extensions b).filter (fun p => p.1 == x)).map fun p => (t, p.2)
    if crossed.isEmpty then [] else (a, b) :: crossed

-- Traverse the two four-vertex paths (outer and inner) and their four spokes.
-- Each bounded quantifier extends the assignment across one more vertex.
private def checkFour (i : Color) : Bool :=
  (extensions i).all fun p => (extensions p.1).all fun q =>
    (extensions q.1).all fun r => (extensions p.2).all fun s =>
      (extensions r.2).all fun t => t.1 != s.1 || (extensions q.2).all fun u =>
        (extensions u.2).all fun v => v.1 != t.2 || (extensions s.2).all fun w =>
          w.1 != u.1 || (boundary i r.1).contains (v.2, w.2)

private theorem checkedFour (i : Color) : checkFour i = true := by
  fin_cases i <;> decide +kernel

private theorem fourPoleCheck :
    ∀ i₁ : Color, ∀ p ∈ extensions i₁, ∀ q ∈ extensions p.1,
    ∀ r ∈ extensions q.1, ∀ s ∈ extensions p.2, ∀ t ∈ extensions r.2,
    t.1 = s.1 → ∀ u ∈ extensions q.2, ∀ v ∈ extensions u.2, v.1 = t.2 →
    ∀ w ∈ extensions s.2, w.1 = u.1 → (v.2, w.2) ∈ boundary i₁ r.1 := by
  intro i
  simpa only [checkFour, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, List.contains_iff_mem,
    Classical.or_iff_not_imp_left, not_not] using checkedFour i

private theorem fourPole {i₁ i₂ o₁ o₂ a b c d e f s₁ s₂ s₃ s₄ : Color}
    (h₁ : (a, s₁) ∈ extensions i₁) (h₂ : (s₂, b) ∈ extensions a)
    (h₃ : (i₂, d) ∈ extensions s₂) (h₄ : (e, f) ∈ extensions s₁)
    (h₅ : (e, s₄) ∈ extensions d) (h₆ : (s₃, c) ∈ extensions b)
    (h₇ : (s₄, o₁) ∈ extensions c) (h₈ : (s₃, o₂) ∈ extensions f) :
    (o₁, o₂) ∈ boundary i₁ i₂ :=
  fourPoleCheck i₁ _ h₁ _ h₂ _ h₃ _ h₄ _ h₅ rfl _ h₆ _ h₇ rfl _ h₈ rfl

-- At the subdividing vertex the green edge fixes the two edges leading into the
-- four-poles. The other connection between the four-poles carries a common color.
private def sectors (green : Color) : List ((Color × Color) × (Color × Color)) := do
  let (top, bot) ← extensions green
  let common ← List.finRange 15
  let (r₁, b₁) ← boundary top common
  let (b₂, r₂) ← boundary common bot
  return ((r₁, r₂), (b₁, b₂))

private theorem sector {g top bot common r₁ r₂ b₁ b₂ : Color}
    (hg : (top, bot) ∈ extensions g) (ht : (r₁, b₁) ∈ boundary top common)
    (hb : (b₂, r₂) ∈ boundary common bot) : ((r₁, r₂), (b₁, b₂)) ∈ sectors g := by
  unfold sectors
  change _ ∈ List.flatMap _ _
  refine List.mem_flatMap.mpr ⟨_, hg, ?_⟩
  refine List.mem_flatMap.mpr ⟨common, List.mem_finRange _, ?_⟩
  refine List.mem_flatMap.mpr ⟨_, ht, ?_⟩
  exact List.mem_flatMap.mpr ⟨_, hb, by simp⟩

-- Store each sector relation as a bit matrix on the 225 ordered pairs of colors.
-- In a row, bit j records whether the pair numbered j can occur on the far side.
private def pairIndex (p : Color × Color) : Nat := 15 * p.1.val + p.2.val

private def matrix (g : Color) (reverse : Bool) : Nat :=
  (sectors g).foldl (init := 0) fun bits (r, b) =>
    let (i, j) := if reverse then (b, r) else (r, b)
    bits ||| (1 <<< (225 * pairIndex i + pairIndex j))

private def matrices : List (Nat × Nat) :=
  eval% (List.finRange 15).map fun g => (matrix g false, matrix g true)

private def row (m : Nat) (p : Color × Color) : Nat :=
  (m >>> (225 * pairIndex p)) % (2 ^ 225)

private def forward (g : Color) := row (matrices[g.val]!).1
private def backward (g : Color) := row (matrices[g.val]!).2

private theorem sector_bits :
    ∀ g : Color, ∀ x ∈ sectors g,
      (forward g x.1).testBit (pairIndex x.2) ∧ (backward g x.2).testBit (pairIndex x.1) := by
  have checked : ∀ g : Color, (sectors g).all fun x =>
      (forward g x.1).testBit (pairIndex x.2) && (backward g x.2).testBit (pairIndex x.1) := by
    decide +kernel
  simpa only [List.all_eq_true, Bool.and_eq_true] using checked

-- After fixing one sector and the central star, the possible far sides of
-- the next sector and near sides of the previous sector are disjoint.
private theorem noRing :
    ∀ g : Color, ∀ p ∈ extensions g, ∀ x ∈ sectors g,
      forward p.1 x.2 &&& backward p.2 x.1 = 0 := by
  have checked : ∀ g : Color, (extensions g).all fun p => (sectors g).all fun x =>
      (forward p.1 x.2 &&& backward p.2 x.1) == 0 := by decide +kernel
  simpa only [List.all_eq_true, beq_iff_eq] using checked

-- Local numbering in a four-pole: the outer path has vertices 0,1,2,3,
-- the inner path 5,7,4,6, and the spokes join k to k+4. The four external
-- neighbors (8,9,10,11) attach at vertices (0,5,3,6), respectively.
private def layout (k : Fin 8) : Fin 12 × Fin 12 × Fin 12 :=
  (#[(8, 1, 4), (0, 5, 2), (1, 6, 3), (2, 7, 10),
     (0, 7, 6), (1, 9, 7), (4, 2, 11), (5, 4, 3)] : Array _)[k.val]!

private def Fits (v : Fin 12 → Vertex) (k : Fin 8) : Prop :=
  let t := layout k
  IsStar (v (k.castLE (by decide))) (v t.1) (v t.2.1) (v t.2.2)

private instance fitsDecidable (v : Fin 12 → Vertex) (k : Fin 8) : Decidable (Fits v k) :=
  inferInstanceAs (Decidable (IsStar _ _ _ _))

private theorem boundaryAt {f} (hf : IsPetersenColoring witness f) (v : Fin 12 → Vertex)
    (h : ∀ k, Fits v k) :
    (paint f (v 3) (v 10), paint f (v 6) (v 11)) ∈
      boundary (paint f (v 0) (v 8)) (paint f (v 5) (v 9)) := by
  let col (i j : Fin 12) := paint f (v (min i j)) (v (max i j))
  have hc (i j) : col i j = paint f (v i) (v j) := by
    by_cases hij : i ≤ j
    · simp [col, min_eq_left hij, max_eq_right hij]
    · simp [col, min_eq_right (le_of_not_ge hij), max_eq_left (le_of_not_ge hij), paint_comm]
  have hs (k : Fin 8) :
      (col (k.castLE (by decide)) (layout k).2.1, col (k.castLE (by decide)) (layout k).2.2) ∈
        extensions (col (k.castLE (by decide)) (layout k).1) := by
    simpa only [hc] using atVertex hf (h k)
  exact fourPole (hs 0) (hs 1) (hs 5) (hs 4) (hs 7) (hs 2) (hs 3) (hs 6)

private def slot (i : Fin 3) (j : Nat) : Vertex := Fin.ofNat 52 (17 * i.val + j)

private def embedding (i : Fin 3) (bottom : Bool) (k : Fin 12) : Vertex :=
  let v := slot i
  let p := slot (i - 1)
  let n := slot (i + 1)
  let vertices := if bottom then
    #[v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 6, v 16, n 14, p 11]
  else
    #[v 3, v 2, v 1, v 0, v 7, v 6, v 5, v 4, v 16, v 8, p 5, n 0]
  vertices[k.val]!

private theorem placements : ∀ i b k, Fits (embedding i b) k := by decide +kernel

private theorem middle : ∀ i, IsStar (slot i 16) 51 (slot i 3) (slot i 13) := by decide

private noncomputable def green (f : Sym2 Vertex → Sym2 PVertex) (i : Fin 3) :=
  paint f 51 (slot i 16)

-- The ordered pair on the cut from sector i to its successor.
private noncomputable def cut (f : Sym2 Vertex → Sym2 PVertex) (i : Fin 3) :=
  (paint f (slot i 5) (slot (i + 1) 0), paint f (slot i 11) (slot (i + 1) 14))

private theorem sectorAt {f} (hf : IsPetersenColoring witness f) (i : Fin 3) :
    (cut f (i - 1), cut f i) ∈ sectors (green f i) := by
  have hm := atVertex hf (middle i)
  have ht := boundaryAt hf (embedding i false) (placements i false)
  have hb := boundaryAt hf (embedding i true) (placements i true)
  fin_cases i <;> exact sector hm ht hb

private theorem uncolorable {f} (hf : IsPetersenColoring witness f) : False := by
  have center := atVertex hf (show IsStar 51 (slot 0 16) (slot 1 16) (slot 2 16) by decide)
  have h₀ := sectorAt hf 0
  have h₁ : (forward (green f 1) (cut f 0)).testBit (pairIndex (cut f 1)) :=
    (sector_bits _ _ (sectorAt hf 1)).1
  have h₂ : (backward (green f 2) (cut f 2)).testBit (pairIndex (cut f 1)) :=
    (sector_bits _ _ (sectorAt hf 2)).2
  have empty := noRing _ _ center _ h₀
  have hit := congrArg (fun n : Nat => n.testBit (pairIndex (cut f 1))) empty
  change (forward (green f 1) (cut f 0) &&& backward (green f 2) (cut f 2)).testBit _ = _ at hit
  simp [Nat.testBit_and, h₁, h₂] at hit

/-- **The Petersen coloring conjecture is false.** There are a finite vertex type $V$ and a
simple graph $G$ on $V$ in which every vertex has exactly three neighbors and no edge is a bridge,
such that $G$ has no Petersen coloring: no map $f$ from unordered pairs of vertices of $G$ to
unordered pairs of vertices of the Petersen graph $P$ sends every edge of $G$ to an edge of $P$
and, for every vertex $v$ of $G$, maps the edges of $G$ at $v$ bijectively onto the edges of $P$
at some vertex $w$ of $P$.

Putman (arXiv:2608.10012, Aug 2026) gave 112-vertex counterexamples with SAT/DRAT certificates,
and Goedgebeur, Jooken, Macajova, Mattiolo, Mazzuoccolo and Ulyanov (arXiv:2608.10028,
Theorem 6) prove two simple bridgeless cubic 52-vertex graphs have no Petersen colouring.

Source: Jan Goedgebeur, Jorik Jooken, Edita
Macajova, Davide Mattiolo, Giuseppe Mazzuoccolo and Nikolay Ulyanov, Disproving the Petersen
Coloring Conjecture: Theoretical Analysis and an Infinite Family of Counterexamples, arXiv
preprint (2026), arXiv:2608.10028, https://arxiv.org/abs/2608.10028; Bryce Putman, A 112-Vertex
Counterexample to the Petersen Coloring Conjecture, arXiv preprint (2026), arXiv:2608.10012,
https://arxiv.org/abs/2608.10012. Moved from
`OpenConjectures/GraphTheory/PetersenColoringConjecture`.
-/
theorem conjecture_refuted : ¬ conjecture := by
  intro h
  obtain ⟨f, hf⟩ := h Vertex witness cubic bridgeless
  exact uncolorable hf

end MathlibExt.GraphTheory.PetersenColoringConjectureWanted
