/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Card

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

/-!
# Infinite antichains in the cycle-continuous order

The theorem `conjecture_holds` proves the existence of an infinite antichain of
finite multigraphs under cycle-continuous maps.

UnsolvedMath record `OPG-323__3223`.

We use a variant of Šámal's path of 3-joined snarks. Every block is the same
18-vertex snark. The three attachment vertices are distinguished by the number
of five-edge cycles meeting their incident edges. The two terminal junctions
use distinct ordered pairs of attachment types, forcing a cycle-continuous
map to preserve the entire path and its length.
-/

@[expose] public section

open scoped BigOperators

namespace MathlibExt.GraphTheory.CycleContinuousAntichainWanted

/-- **Multigraphs with loops and parallel edges.** A multigraph $G$ consists of a type $V$ of
vertices, a type $E$ of edges, and a map assigning to each edge an ordered pair of vertices,
its two endpoints. Distinct edges may have the same endpoints (parallel edges), and the two
endpoints of an edge may coincide (a loop). Neither $V$ nor $E$ is required to be finite.

Source: [OPG-323] Antichains in the cycle continuous order
(URL: http://www.openproblemgarden.org/op/antichains_in_the_cycle_continuous_order). -/
structure FGraph where
  V : Type
  E : Type
  ends : E → V × V

/-- **Finite multigraphs with at least one edge.** A multigraph $G$ is finite and nontrivial
when its set of vertices and its set of edges are both finite and it has at least one edge.
These are the graphs on which the cycle-continuous order is considered.

Source: [OPG-323]
(URL: http://www.openproblemgarden.org/op/antichains_in_the_cycle_continuous_order). -/
def IsFiniteNontrivial (G : FGraph) : Prop :=
  Finite G.V ∧ Finite G.E ∧ Nonempty G.E

/-- **Binary cycle space.** Let $G$ be a multigraph. A set $S$ of edges of $G$ is a binary cycle
when $S$ is finite and every vertex $v$ is an endpoint of an even number of edges of $S$, where
only edges with exactly one endpoint equal to $v$ are counted; loops are not counted, which
agrees modulo $2$ with counting each loop twice. The cycle space of $G$ is the set of all
binary cycles of $G$.

Source: [OPG-323]
(URL: http://www.openproblemgarden.org/op/antichains_in_the_cycle_continuous_order). -/
noncomputable def cycleSpace (G : FGraph) : Set (Set G.E) :=
  {S | Set.Finite S ∧ ∀ v : G.V, Even (Set.ncard
    {e ∈ S | ((G.ends e).1 = v ∧ (G.ends e).2 ≠ v) ∨
      ((G.ends e).1 ≠ v ∧ (G.ends e).2 = v)})}

/-- **Cycle-continuous maps.** Let $G$ and $H$ be multigraphs. A map $f$ from the edges of $G$
to the edges of $H$ is cycle-continuous when, for every binary cycle $C$ of $H$, the preimage
$f^{-1}(C)$ is a binary cycle of $G$.

Source: [OPG-323]
(URL: http://www.openproblemgarden.org/op/antichains_in_the_cycle_continuous_order). -/
noncomputable def IsCycleContinuous (G H : FGraph) (f : G.E → H.E) : Prop :=
  ∀ C ∈ cycleSpace H, f ⁻¹' C ∈ cycleSpace G

/-- **Infinite antichains in the cycle-continuous order.** There is a sequence
$G_0, G_1, G_2, \dots$ of pairwise distinct finite multigraphs, each with at least one edge,
such that for all $i \ne j$ there is no cycle-continuous map from the edges of $G_i$ to the
edges of $G_j$.

Source: [OPG-323]
(URL: http://www.openproblemgarden.org/op/antichains_in_the_cycle_continuous_order). -/
noncomputable def conjecture : Prop :=
  ∃ G : ℕ → FGraph, (∀ n, IsFiniteNontrivial (G n)) ∧ Function.Injective G ∧
    ∀ i j, i ≠ j → ¬∃ f : (G i).E → (G j).E, IsCycleContinuous (G i) (G j) f

/-! ## The finite snark and its binary cycles -/

private abbrev Vertex := Fin 18
private abbrev Edge := Fin 27
private abbrev Bit := ZMod 2

-- The dot product of two Petersen graphs, with edges numbered in the order shown.
private def endpoints (e : Edge) : Vertex × Vertex :=
  (#[(0, 1), (0, 4), (0, 8), (1, 2), (1, 5), (2, 3), (2, 6),
    (3, 7), (3, 9), (4, 6), (4, 7), (5, 7), (5, 10), (6, 11),
    (8, 12), (8, 13), (9, 10), (9, 14), (10, 15), (11, 12), (11, 16),
    (12, 17), (13, 15), (13, 16), (14, 16), (14, 17), (15, 17)] : Array (Vertex × Vertex))[e.val]!

-- The incident edge numbers, in increasing order at each vertex.
private def star (v : Vertex) (j : Fin 3) : Edge :=
  ((#[![0, 1, 2], ![0, 3, 4], ![3, 5, 6], ![5, 7, 8], ![1, 9, 10], ![4, 11, 12], ![6, 9, 13],
    ![7, 10, 11], ![2, 14, 15], ![8, 16, 17], ![12, 16, 18], ![13, 19, 20], ![14, 19, 21],
    ![15, 22, 23],
    ![17, 24, 25], ![18, 22, 26], ![20, 23, 24], ![21, 25, 26]] : Array (Fin 3 → Edge))[v.val]!) j

private def total {A : Type*} [AddCommMonoid A] (x : Edge → A) (v : Vertex) : A :=
  ∑ j, x (star v j)

private def Balanced (x : Edge → Bit) : Prop :=
  ∀ v, total x v = 0

private def bits (m : ℕ) (e : Edge) : Bit :=
  if m.testBit e.val then 1 else 0

private theorem bits_xor (m n : ℕ) (e : Edge) :
    bits (m ^^^ n) e = bits m e + bits n e := by
  simp only [bits, Nat.testBit_xor]
  cases m.testBit e.val <;> cases n.testBit e.val <;> decide

private theorem balanced_add {x y : Edge → Bit} (hx : Balanced x) (hy : Balanced y) :
    Balanced (fun e => x e + y e) := by
  intro v
  change (∑ j, (x (star v j) + y (star v j))) = 0
  rw [Finset.sum_add_distrib]
  change total x v + total y v = 0
  rw [hx v, hy v, add_zero]

private abbrev Chord := Fin 10

private def chord (i : Chord) : Edge :=
  (#[0, 1, 3, 5, 7, 9, 14,
    16, 19, 22] : Array Edge)[i.val]!

-- Fundamental cycles of the spanning tree, encoded as binary edge masks.
private def basisMask (i : Chord) : ℕ :=
  #[126128149, 126131206, 118763608, 17965408, 101063040, 118767104, 60866560,
    101122048, 54001664, 130023424][i.val]!

private theorem basis_balanced : ∀ i, Balanced (bits (basisMask i)) := by
  change ∀ i v, total (bits (basisMask i)) v = 0
  decide +kernel

private theorem basis_chord : ∀ i j, bits (basisMask i) (chord j) = if i = j then 1 else 0 := by
  decide +kernel

-- If the chord coordinates vanish, repeatedly apply balance at a leaf of the
-- remaining spanning tree to show that each tree edge has coordinate zero.
private theorem zero_of_chords {x : Edge → Bit} (hx : Balanced x)
    (h : ∀ i, x (chord i) = 0) (e : Edge) : x e = 0 := by
  have leaf (v : Vertex) : x (star v 0) + x (star v 1) + x (star v 2) = 0 := by
    simpa only [total, Fin.sum_univ_three] using hx v
  have left (a b c : Bit) (ha : a + b + c = 0) (hb : b = 0) (hc : c = 0) : a = 0 := by
    simpa [hb, hc] using ha
  have middle (a b c : Bit) (ha : a + b + c = 0) (hb : a = 0) (hc : c = 0) : b = 0 := by
    simpa [hb, hc] using ha
  have right (a b c : Bit) (ha : a + b + c = 0) (hb : a = 0) (hc : b = 0) : c = 0 := by
    simpa [hb, hc] using ha
  have e0 : x 0 = 0 := h 0
  have e1 : x 1 = 0 := h 1
  have e3 : x 3 = 0 := h 2
  have e5 : x 5 = 0 := h 3
  have e7 : x 7 = 0 := h 4
  have e9 : x 9 = 0 := h 5
  have e14 : x 14 = 0 := h 6
  have e16 : x 16 = 0 := h 7
  have e19 : x 19 = 0 := h 8
  have e22 : x 22 = 0 := h 9
  have e2 : x 2 = 0 := right _ _ _ (leaf 0) e0 e1
  have e4 : x 4 = 0 := right _ _ _ (leaf 1) e0 e3
  have e6 : x 6 = 0 := right _ _ _ (leaf 2) e3 e5
  have e8 : x 8 = 0 := right _ _ _ (leaf 3) e5 e7
  have e10 : x 10 = 0 := right _ _ _ (leaf 4) e1 e9
  have e13 : x 13 = 0 := right _ _ _ (leaf 6) e6 e9
  have e11 : x 11 = 0 := right _ _ _ (leaf 7) e7 e10
  have e12 : x 12 = 0 := right _ _ _ (leaf 5) e4 e11
  have e15 : x 15 = 0 := right _ _ _ (leaf 8) e2 e14
  have e17 : x 17 = 0 := right _ _ _ (leaf 9) e8 e16
  have e18 : x 18 = 0 := right _ _ _ (leaf 10) e12 e16
  have e20 : x 20 = 0 := right _ _ _ (leaf 11) e13 e19
  have e21 : x 21 = 0 := right _ _ _ (leaf 12) e14 e19
  have e23 : x 23 = 0 := right _ _ _ (leaf 13) e15 e22
  have e26 : x 26 = 0 := right _ _ _ (leaf 15) e18 e22
  have e24 : x 24 = 0 := right _ _ _ (leaf 16) e20 e23
  have e25 : x 25 = 0 := right _ _ _ (leaf 14) e17 e24
  fin_cases e <;> assumption

private def closure : List Chord → List ℕ
  | [] => [0]
  | j :: js =>
    let rest := closure js
    rest ++ rest.map (basisMask j ^^^ ·)

private theorem closure_balanced (js : List Chord) {m : ℕ} (hm : m ∈ closure js) :
    Balanced (bits m) := by
  induction js generalizing m with
  | nil =>
    simp only [closure, List.mem_singleton] at hm
    subst m
    intro v
    simp [total, bits]
  | cons j js ih =>
    simp only [closure, List.mem_append, List.mem_map] at hm
    rcases hm with hm | ⟨r, hr, rfl⟩
    · exact ih hm
    · have he : bits (basisMask j ^^^ r) = fun e => bits (basisMask j) e + bits r e :=
        funext (bits_xor _ _)
      rw [he]
      exact balanced_add (basis_balanced j) (ih hr)

private theorem bit_cases (b : Bit) : b = 0 ∨ b = 1 := by
  exact (by decide : ∀ x : Bit, x = 0 ∨ x = 1) b

private theorem mem_closure (x : Edge → Bit) (js : List Chord) (hj : js.Nodup) :
    ∃ m ∈ closure js, ∀ i, bits m (chord i) = if i ∈ js then x (chord i) else 0 := by
  induction js with
  | nil => exact ⟨0, by simp [closure], by simp [bits]⟩
  | cons j js ih =>
    obtain ⟨hn, hj⟩ := List.nodup_cons.mp hj
    obtain ⟨r, hr, h⟩ := ih hj
    rcases bit_cases (x (chord j)) with hj | hj
    · refine ⟨r, List.mem_append_left _ hr, fun i => ?_⟩
      rw [h]
      by_cases hi : i = j
      · subst i
        simp [hn, hj]
      · simp [hi]
    · refine ⟨basisMask j ^^^ r, List.mem_append_right _ (List.mem_map_of_mem hr), fun i => ?_⟩
      rw [bits_xor, basis_chord, h]
      by_cases hi : i = j
      · subst i
        simp [hn, hj]
      · simp [Ne.symm hi, hi]

private def cycleMasks : List ℕ := closure (List.finRange 10)

private theorem exists_mask {x : Edge → Bit} (hx : Balanced x) :
    ∃ m ∈ cycleMasks, x = bits m := by
  have hn : (List.finRange 10).Nodup := by decide
  obtain ⟨m, hm, h⟩ := mem_closure x (List.finRange 10) hn
  have hm' := closure_balanced _ hm
  have hz : Balanced (fun e => x e + bits m e) := balanced_add hx hm'
  refine ⟨m, hm, funext fun e => ?_⟩
  have hzero (i : Chord) : x (chord i) + bits m (chord i) = 0 := by
    rw [h i]
    simp only [List.mem_finRange, ite_true]
    exact (by decide : ∀ a : Bit, a + a = 0) _
  have he := zero_of_chords hz hzero e
  exact (by decide : ∀ a b : Bit, a + b = 0 → a = b) _ _ he


/-! ## Flows on edge deletions and cycles at attachment vertices -/

private abbrev Color := Bit × Bit

private def Flow (x : Edge → Color) : Prop :=
  Balanced (Prod.fst ∘ x) ∧ Balanced (Prod.snd ∘ x)

private def touches (m : ℕ) (v : Vertex) : Bool :=
  m.testBit (star v 0).val || m.testBit (star v 1).val || m.testBit (star v 2).val

private def fullMasks : List ℕ :=
  cycleMasks.filter fun m => (List.finRange 18).all (touches m)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation enumerates the fundamental cycle combinations.
private theorem noCoverCheck :
    (fullMasks.all fun m => fullMasks.all fun k =>
      (List.finRange 27).any fun e => !(m.testBit e.val || k.testBit e.val)) = true := by
  decide +kernel

private theorem full_of_flow {x : Edge → Color} (hx : Flow x) (hn : ∀ e, x e ≠ 0)
    {m k : ℕ} (hm : Prod.fst ∘ x = bits m) (hk : Prod.snd ∘ x = bits k) :
    (∀ v, touches m v = true) ∧ ∀ v, touches k v = true := by
  have localFact :
      ∀ (a b c : Color), a ≠ 0 → b ≠ 0 → c ≠ 0 →
        a.1 + b.1 + c.1 = 0 → a.2 + b.2 + c.2 = 0 →
        (a.1 ≠ 0 ∨ b.1 ≠ 0 ∨ c.1 ≠ 0) ∧ (a.2 ≠ 0 ∨ b.2 ≠ 0 ∨ c.2 ≠ 0) := by
    decide +kernel
  have hv (v : Vertex) := localFact _ _ _ (hn (star v 0)) (hn (star v 1)) (hn (star v 2))
    (by simpa only [total, Fin.sum_univ_three, Function.comp_apply] using hx.1 v)
    (by simpa only [total, Fin.sum_univ_three, Function.comp_apply] using hx.2 v)
  have hb (p : ℕ) (e : Edge) : bits p e ≠ 0 ↔ p.testBit e.val = true := by
    unfold bits
    cases p.testBit e.val <;> decide
  constructor <;> intro v
  · have h := (hv v).1
    change (Prod.fst ∘ x) (star v 0) ≠ 0 ∨
      (Prod.fst ∘ x) (star v 1) ≠ 0 ∨ (Prod.fst ∘ x) (star v 2) ≠ 0 at h
    simpa only [hm, hb, touches, Bool.or_eq_true, or_assoc] using h
  · have h := (hv v).2
    change (Prod.snd ∘ x) (star v 0) ≠ 0 ∨
      (Prod.snd ∘ x) (star v 1) ≠ 0 ∨ (Prod.snd ∘ x) (star v 2) ≠ 0 at h
    simpa only [hk, hb, touches, Bool.or_eq_true, or_assoc] using h

private theorem noFlow (x : Edge → Color) (hx : Flow x) : ∃ e, x e = 0 := by
  by_contra! hn
  obtain ⟨m, hm, hxm⟩ := exists_mask hx.1
  obtain ⟨k, hk, hxk⟩ := exists_mask hx.2
  obtain ⟨hmt, hkt⟩ := full_of_flow hx hn hxm hxk
  have hm' : m ∈ fullMasks := List.mem_filter.mpr ⟨hm, List.all_eq_true.mpr fun v _ => hmt v⟩
  have hk' : k ∈ fullMasks := List.mem_filter.mpr ⟨hk, List.all_eq_true.mpr fun v _ => hkt v⟩
  obtain ⟨e, _, he⟩ := List.any_eq_true.mp
    (List.all_eq_true.mp (List.all_eq_true.mp noCoverCheck _ hm') _ hk')
  change (!(m.testBit e.val || k.testBit e.val)) = true at he
  have hz : m.testBit e.val = false ∧ k.testBit e.val = false := by simpa using he
  apply hn e
  apply Prod.ext
  · change (Prod.fst ∘ x) e = 0
    rw [hxm]; simp [bits, hz.1]
  · change (Prod.snd ∘ x) e = 0
    rw [hxk]; simp [bits, hz.2]

private def maskFlow (p : ℕ × ℕ) (e : Edge) : Color := (bits p.1 e, bits p.2 e)

private def singleDeletion (e : Edge) : ℕ × ℕ :=
  #[(49769150, 123328472), (58060600, 115037941), (91486891, 65875315),
    (58059667, 115037941), (49768109, 123329483), (58059667, 115039821),
    (49769150, 123327891), (58060147, 115036766), (49769150, 91985653),
    (49768693, 123329835), (49769150, 123329483), (49768109, 123327347),
    (49769150, 91916237), (58559454, 115037941), (58560373, 99302059),
    (50268915, 130645805), (57997995, 114970485), (58559454, 130645805),
    (91917278, 130645805), (65359733, 91486891), (40812333, 130643422),
    (130645805, 23055091), (61456173, 111135475), (58559454, 105641203),
    (82935597, 40809950), (91486891, 14503797), (30310189, 58559454)][e.val]!

private def doubleDeletion (i j : Fin 3) : ℕ × ℕ :=
  #[(49769566, 123328472), (58060600, 115036766), (49769566, 91986662),
    (49770005, 123328472), (58060600, 115039821), (49768693, 91987533),
    (58059667, 99302475), (58060600, 99302475), (91486891, 50269784)][3 * i.val + j.val]!

private theorem singleDeletion_flow (e : Edge) :
    ∃ x : Edge → Color, Flow x ∧ ∀ f, x f = 0 ↔ f = e := by
  refine ⟨maskFlow (singleDeletion e), ?_, ?_⟩
  · have h : ∀ e v, total (bits (singleDeletion e).1) v = 0 ∧
        total (bits (singleDeletion e).2) v = 0 := by decide +kernel
    exact ⟨fun v => (h e v).1, fun v => (h e v).2⟩
  · exact (by decide +kernel : ∀ e f, maskFlow (singleDeletion e) f = 0 ↔ f = e) e

private theorem doubleDeletion_flow (i j : Fin 3) :
    ∃ x : Edge → Color, Flow x ∧ ∀ f, x f = 0 ↔ f = star 0 i ∨ f = star 3 j := by
  refine ⟨maskFlow (doubleDeletion i j), ?_, ?_⟩
  · have h : ∀ i j v, total (bits (doubleDeletion i j).1) v = 0 ∧
        total (bits (doubleDeletion i j).2) v = 0 := by decide +kernel
    exact ⟨fun v => (h i j v).1, fun v => (h i j v).2⟩
  · exact (by decide +kernel : ∀ i j f,
      maskFlow (doubleDeletion i j) f = 0 ↔ f = star 0 i ∨ f = star 3 j) i j

-- For each of the three ports and each pair of edges of that port, a cycle
-- meeting the port in just that pair and avoiding the other attachment vertex
-- if there are two active ports in that block.
private def portMask (v : Vertex) (i : Fin 3) : ℕ :=
  let k := if v = 0 then 0 else if v = 3 then 3 else 6
  #[126131206, 126128149, 3091, 101063040, 17965408, 118765792,
    126128149, 69488661, 60866560][k + i.val]!

private theorem realizePort (v : Vertex) (h : v = 0 ∨ v = 3 ∨ v = 17)
    (p : Fin 3 → Bit) (hp : ∑ k, p k = 0) :
    ∃ y : Edge → Bit, Balanced y ∧ (∀ k, y (star v k) = p k) ∧
      (v = 0 → ∀ k, y (star 3 k) = 0) ∧ (v = 3 → ∀ k, y (star 0 k) = 0) := by
  have hcase : p = (fun _ => 0) ∨ ∃ i : Fin 3, ∀ k, p k = if i = k then 0 else 1 := by
    have h' : ∀ p : Fin 3 → Bit, p 0 + p 1 + p 2 = 0 →
        p = (fun _ => 0) ∨ ∃ i : Fin 3, ∀ k, p k = if i = k then 0 else 1 := by
      decide +kernel
    exact h' _ (by simpa only [Fin.sum_univ_three] using hp)
  rcases hcase with rfl | ⟨i, hi⟩
  · exact ⟨fun _ => 0, fun _ => by simp [total], fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  refine ⟨bits (portMask v i), fun w => ?_, fun k => ?_, fun he k => ?_, fun he k => ?_⟩
  · exact (by decide +kernel : ∀ v, v = 0 ∨ v = 3 ∨ v = 17 →
      ∀ i w, total (bits (portMask v i)) w = 0) v h i w
  · rw [hi]
    exact (by decide +kernel : ∀ v, v = 0 ∨ v = 3 ∨ v = 17 →
      ∀ i k, bits (portMask v i) (star v k) = if i = k then 0 else 1) v h i k
  · subst v
    exact (by decide +kernel : ∀ i k, bits (portMask 0 i) (star 3 k) = 0) i k
  · subst v
    exact (by decide +kernel : ∀ i k, bits (portMask 3 i) (star 0 k) = 0) i k


/-! ## Paths of 3-joined blocks -/

-- The path has n+3 blocks and n+2 junctions. Both terminal blocks use port 17.
private abbrev Block (n : ℕ) := Fin (n + 3)
private abbrev Junction (n : ℕ) := Fin (n + 2)

private def leftPort {n : ℕ} (i : Block n) : Vertex :=
  if i.val = n + 2 then 17 else 0

private def rightPort {n : ℕ} (i : Block n) : Vertex :=
  if i.val = 0 then 17 else 3

private abbrev HasLeft {n : ℕ} (i : Block n) : Prop := 0 < i.val

private abbrev HasRight {n : ℕ} (i : Block n) : Prop := i.val + 1 < n + 3

private def prev {n : ℕ} (i : Block n) (h : HasLeft i) : Junction n :=
  ⟨i.val - 1, by have hi := i.isLt; unfold HasLeft at h; omega⟩

private def next {n : ℕ} (i : Block n) (h : HasRight i) : Junction n :=
  ⟨i.val, by unfold HasRight at h; omega⟩

private theorem prev_succ {n : ℕ} (i : Block n) (h : HasLeft i) : (prev i h).succ = i := by
  apply Fin.ext
  unfold HasLeft at h
  change i.val - 1 + 1 = i.val
  omega

private theorem next_castSucc {n : ℕ} (i : Block n) (h : HasRight i) :
    (next i h).castSucc = i := Fin.ext rfl

private theorem left_of_succ {n : ℕ} (j : Junction n) : HasLeft j.succ :=
  Nat.succ_pos _

private theorem right_of_castSucc {n : ℕ} (j : Junction n) : HasRight j.castSucc := by
  have hj := j.isLt
  change j.val + 1 < n + 3
  omega

private theorem prev_of_succ {n : ℕ} (j : Junction n) :
    prev j.succ (left_of_succ j) = j := by
  apply Fin.ext
  change j.val + 1 - 1 = j.val
  omega

private theorem next_of_castSucc {n : ℕ} (j : Junction n) :
    next j.castSucc (right_of_castSucc j) = j := Fin.ext rfl

private abbrev LeftEdge {n : ℕ} (i : Block n) (e : Edge) : Prop :=
  HasLeft i ∧ (∃ k, star (leftPort i) k = e)

private abbrev RightEdge {n : ℕ} (i : Block n) (e : Edge) : Prop :=
  HasRight i ∧ (∃ k, star (rightPort i) k = e)

private abbrev PathEdge (n : ℕ) :=
  {p : Block n × Edge // ¬LeftEdge p.1 p.2 ∧ ¬RightEdge p.1 p.2} ⊕ (Junction n × Fin 3)

private def IsPort (v : Vertex) : Prop := v = 0 ∨ v = 3 ∨ v = 17

private theorem star_injective (v : Vertex) : Function.Injective (star v) := by
  exact (by decide +kernel : ∀ (v : Vertex) (i j : Fin 3), star v i = star v j → i = j) v

private theorem port_star_disjoint (v w : Vertex) (hv : IsPort v) (hw : IsPort w)
    (hne : v ≠ w) (i j : Fin 3) : star v i ≠ star w j := by
  exact (by
    unfold IsPort
    decide +kernel : ∀ v w, IsPort v → IsPort w → v ≠ w → ∀ i j, star v i ≠ star w j)
    v w hv hw hne i j

private theorem left_isPort {n : ℕ} (i : Block n) : IsPort (leftPort i) := by
  unfold leftPort IsPort
  split <;> simp

private theorem right_isPort {n : ℕ} (i : Block n) : IsPort (rightPort i) := by
  unfold rightPort IsPort
  split <;> simp

private theorem active_ports {n : ℕ} (i : Block n) (hl : HasLeft i) (hr : HasRight i) :
    leftPort i = 0 ∧ rightPort i = 3 := by
  unfold HasLeft at hl
  unfold HasRight at hr
  have hlast : i.val ≠ n + 2 := by omega
  have hfirst : i.val ≠ 0 := by omega
  simp [leftPort, rightPort, hlast, hfirst]

private theorem left_not_right {n : ℕ} {i : Block n} {e : Edge}
    (hl : LeftEdge i e) : ¬RightEdge i e := by
  rintro ⟨hr, k, hk⟩
  obtain ⟨hl, j, hj⟩ := hl
  obtain ⟨hleft, hright⟩ := active_ports i hl hr
  have h₀ : IsPort 0 := Or.inl rfl
  have h₃ : IsPort 3 := Or.inr (Or.inl rfl)
  exact port_star_disjoint 0 3 h₀ h₃ (by decide) j k
    (by simpa only [hleft, hright] using hj.trans hk.symm)

private noncomputable def includeEdge {n : ℕ} (i : Block n) (e : Edge) : PathEdge n := by
  classical
  exact if h : LeftEdge i e then .inr (prev i h.1, h.2.choose)
    else if h' : RightEdge i e then .inr (next i h'.1, h'.2.choose)
    else .inl ⟨(i, e), h, h'⟩

private theorem include_left {n : ℕ} (j : Junction n) (k : Fin 3) :
    includeEdge j.succ (star (leftPort j.succ) k) = .inr (j, k) := by
  have h : LeftEdge j.succ (star (leftPort j.succ) k) := ⟨left_of_succ j, k, rfl⟩
  simp only [includeEdge, dite_eq_left h, prev_of_succ]
  rw [star_injective _ h.2.choose_spec]

private theorem include_right {n : ℕ} (j : Junction n) (k : Fin 3) :
    includeEdge j.castSucc (star (rightPort j.castSucc) k) = .inr (j, k) := by
  have h : RightEdge j.castSucc (star (rightPort j.castSucc) k) := ⟨right_of_castSucc j, k, rfl⟩
  have hn : ¬LeftEdge j.castSucc (star (rightPort j.castSucc) k) := fun hl => left_not_right hl h
  simp only [includeEdge, dite_eq_right hn, dite_eq_left h, next_of_castSucc]
  rw [star_injective _ h.2.choose_spec]

private theorem include_internal_iff {n : ℕ} (i : Block n) (e : Edge)
    (p : {p : Block n × Edge // ¬LeftEdge p.1 p.2 ∧ ¬RightEdge p.1 p.2}) :
    includeEdge i e = .inl p ↔ (i, e) = p.val := by
  constructor
  · intro h
    unfold includeEdge at h
    split at h
    · cases h
    split at h
    · cases h
    · exact congrArg Subtype.val (Sum.inl.inj h)
  · rintro h
    obtain ⟨⟨i', e'⟩, hl, hr⟩ := p
    cases h
    simp [includeEdge, hl, hr]

private theorem include_join_iff {n : ℕ} (i : Block n) (e : Edge)
    (j : Junction n) (k : Fin 3) :
    includeEdge i e = .inr (j, k) ↔
      (i = j.castSucc ∧ e = star (rightPort i) k) ∨
        (i = j.succ ∧ e = star (leftPort i) k) := by
  constructor
  · intro h
    unfold includeEdge at h
    split at h
    · rename_i hl
      obtain ⟨rfl, hk⟩ := Prod.mk.inj (Sum.inr.inj h)
      exact Or.inr ⟨(prev_succ i hl.1).symm, hk ▸ hl.2.choose_spec.symm⟩
    split at h
    · rename_i _ hr
      obtain ⟨rfl, hk⟩ := Prod.mk.inj (Sum.inr.inj h)
      exact Or.inl ⟨(next_castSucc i hr.1).symm, hk ▸ hr.2.choose_spec.symm⟩
    · cases h
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact include_right j k
    · exact include_left j k

private theorem include_injective {n : ℕ} (i : Block n) : Function.Injective (includeEdge i) := by
  intro e f h
  obtain hp | ⟨j, k, hp⟩ := (includeEdge i e).rec
    (fun p => Or.inl ⟨p, rfl⟩) (fun p => Or.inr ⟨p.1, p.2, rfl⟩)
    (motive := fun x =>
      (∃ p, x = .inl p) ∨ ∃ (j : Junction n) (k : Fin 3), x = .inr (j, k))
  · obtain ⟨p, hp⟩ := hp
    have he := (include_internal_iff i e p).mp hp
    have hf := (include_internal_iff i f p).mp (h.symm.trans hp)
    exact congrArg Prod.snd (he.trans hf.symm)
  · have he := (include_join_iff i e j k).mp hp
    have hf := (include_join_iff i f j k).mp (h.symm.trans hp)
    have hn : j.castSucc ≠ j.succ := by
      intro hn
      have hval := congrArg Fin.val hn
      change j.val = j.val + 1 at hval
      omega
    rcases he with ⟨he, rfl⟩ | ⟨he, rfl⟩ <;>
      rcases hf with ⟨hf, rfl⟩ | ⟨hf, rfl⟩
    · rfl
    · exact (hn (he.symm.trans hf)).elim
    · exact (hn (hf.symm.trans he)).elim
    · rfl


private def otherEnd (v : Vertex) (e : Edge) : Vertex :=
  if (endpoints e).1 = v then (endpoints e).2 else (endpoints e).1

private def Touches {A : Type*} (p : A × A) (v : A) : Prop :=
  (p.1 = v ∧ p.2 ≠ v) ∨ (p.1 ≠ v ∧ p.2 = v)

private theorem touches_star (v : Vertex) (e : Edge) :
    Touches (endpoints e) v ↔ ∃ k, star v k = e := by
  exact (by
    unfold Touches
    decide +kernel : ∀ v e, Touches (endpoints e) v ↔ ∃ k, star v k = e) v e

private theorem other_touches (v : Vertex) (k : Fin 3) :
    Touches (endpoints (star v k)) (otherEnd v (star v k)) := by
  exact (by
    unfold Touches
    decide +kernel : ∀ v k, Touches (endpoints (star v k)) (otherEnd v (star v k))) v k

private theorem other_not_port {v : Vertex} (hv : IsPort v) (k : Fin 3) :
    ¬IsPort (otherEnd v (star v k)) := by
  exact (by
    unfold IsPort
    decide +kernel : ∀ v, IsPort v → ∀ k, ¬IsPort (otherEnd v (star v k))) v hv k

private theorem eq_other {v w : Vertex} {e : Edge} (hv : Touches (endpoints e) v)
    (hw : Touches (endpoints e) w) (hne : w ≠ v) : otherEnd v e = w := by
  unfold Touches at hv hw
  rcases hv with ⟨hv, hnv⟩ | ⟨hnv, hv⟩ <;>
    rcases hw with ⟨hw, _⟩ | ⟨_, hw⟩
  · exact (hne (hw.symm.trans hv)).elim
  · simpa only [otherEnd, hv, ite_true] using hw
  · simpa only [otherEnd, hnv, ite_false] using hw
  · exact (hne (hw.symm.trans hv)).elim

private def pathEnds {n : ℕ} : PathEdge n → (Block n × Vertex) × (Block n × Vertex)
  | .inl ⟨(i, e), _⟩ => ((i, (endpoints e).1), (i, (endpoints e).2))
  | .inr (j, k) =>
    ((j.castSucc, otherEnd (rightPort j.castSucc) (star (rightPort j.castSucc) k)),
      (j.succ, otherEnd (leftPort j.succ) (star (leftPort j.succ) k)))

-- Keep the attachment vertices removed by the joins as isolated vertices.
private def pathGraph (n : ℕ) : FGraph :=
  ⟨Block n × Vertex, PathEdge n, pathEnds⟩

private def Alive {n : ℕ} (i : Block n) (v : Vertex) : Prop :=
  (HasLeft i → v ≠ leftPort i) ∧ (HasRight i → v ≠ rightPort i)

set_option maxHeartbeats 600000 in
-- The proof unfolds the dependent edge labels and checks their incidence.
private theorem path_touches {n : ℕ} (i : Block n) (v : Vertex) (a : PathEdge n) :
    Touches (pathEnds a) (i, v) ↔
      Alive i v ∧ ∃ k, includeEdge i (star v k) = a := by
  cases a with
  | inl p =>
    rcases p with ⟨⟨j,e⟩, hnl, hnr⟩
    have hp : (fun k => includeEdge i (star v k) = .inl ⟨(j,e), hnl, hnr⟩) =
        (fun k => i = j ∧ star v k = e) := by
      funext k
      rw [include_internal_iff, Prod.mk.injEq]
    rw [hp]
    by_cases hj : i = j
    · subst j
      have h : Touches (pathEnds (.inl ⟨(i, e), hnl, hnr⟩)) (i, v) ↔
          Touches (endpoints e) v := by simp [pathEnds, Touches]
      rw [h, touches_star]
      constructor
      · rintro ⟨k, hk⟩
        refine ⟨⟨fun hl he => hnl ⟨hl, k, he ▸ hk⟩,
          fun hr he => hnr ⟨hr, k, he ▸ hk⟩⟩, k, rfl, hk⟩
      · rintro ⟨_, k, _, hk⟩
        exact ⟨k, hk⟩
    · simp [pathEnds, Touches, Ne.symm hj, hj]
  | inr p =>
    rcases p with ⟨j, k⟩
    have hnj : j.castSucc ≠ j.succ := fun h => by
      have hh := congrArg Fin.val h
      change j.val = j.val + 1 at hh
      omega
    have hneq : (pathEnds (.inr (j, k))).1 ≠ (pathEnds (.inr (j,k))).2 :=
      fun he => hnj (congrArg Prod.fst he)
    have touch : Touches (pathEnds (.inr (j, k))) (i, v) ↔
        (pathEnds (.inr (j, k))).1 = (i, v) ∨ (pathEnds (.inr (j, k))).2 = (i, v) := by
      unfold Touches
      constructor
      · rintro (⟨h, _⟩ | ⟨_, h⟩)
        · exact Or.inl h
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl ⟨h, fun he => hneq (h.trans he.symm)⟩
        · exact Or.inr ⟨fun he => hneq (he.trans h.symm), h⟩
    rw [touch]
    simp only [pathEnds, Prod.mk.injEq, include_join_iff]
    by_cases hh : i = j.castSucc
    · subst i
      have hport := other_not_port (right_isPort j.castSucc) k
      have hr := right_of_castSucc j
      have ht := (touches_star (rightPort j.castSucc) _).mpr ⟨k, rfl⟩
      have hi := other_touches (rightPort j.castSucc) k
      have hal :
          Alive j.castSucc (otherEnd (rightPort j.castSucc) (star (rightPort j.castSucc) k)) :=
        ⟨fun _ he => hport (he.symm ▸ left_isPort _),
          fun _ he => hport (he.symm ▸ right_isPort _)⟩
      simp only [hnj, Ne.symm hnj, false_and, true_and, or_false]
      constructor
      · rintro rfl
        exact ⟨hal, (touches_star _ _).mp hi⟩
      · rintro ⟨ha, l, hl⟩
        exact eq_other ht ((touches_star _ _).mpr ⟨l, hl⟩) (ha.2 hr)
    · by_cases hl : i = j.succ
      · subst i
        have hport := other_not_port (left_isPort j.succ) k
        have hleft := left_of_succ j
        have ht := (touches_star (leftPort j.succ) _).mpr ⟨k, rfl⟩
        have hi := other_touches (leftPort j.succ) k
        have hal : Alive j.succ (otherEnd (leftPort j.succ) (star (leftPort j.succ) k)) :=
          ⟨fun _ he => hport (he.symm ▸ left_isPort _),
          fun _ he => hport (he.symm ▸ right_isPort _)⟩
        simp only [hnj, Ne.symm hnj, false_and, true_and, false_or]
        constructor
        · rintro rfl
          exact ⟨hal, (touches_star _ _).mp hi⟩
        · rintro ⟨ha, l, hl⟩
          exact eq_other ht ((touches_star _ _).mpr ⟨l, hl⟩) (ha.1 hleft)
      · simp [hh, hl, Ne.symm hh, Ne.symm hl]

private def support {E : Type*} (x : E → Bit) : Set E := {e | x e = 1}

private theorem support_ite {E : Type*} (x : E → Bit) (e : E) [Decidable (e ∈ support x)] :
    (if e ∈ support x then 1 else 0 : Bit) = x e := by
  rcases bit_cases (x e) with hx | hx <;> simp [support, hx]

private theorem even_range_iff {E : Type*} (a : Fin 3 → E) (ha : Function.Injective a)
    (x : E → Bit) :
    Even (Set.ncard {e ∈ support x | e ∈ Set.range a}) ↔ ∑ k, x (a k) = 0 := by
  classical
  have heq : {e ∈ support x | e ∈ Set.range a} = a '' (a ⁻¹' support x) := by
    ext e
    constructor
    · rintro ⟨hx, k, rfl⟩
      exact ⟨k, hx, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨hk, k, rfl⟩
  rw [heq, Set.ncard_image_of_injective _ ha, even_iff_two_dvd,
    ← ZMod.natCast_eq_zero_iff]
  have hu : (a ⁻¹' support x).toFinset =
      Finset.univ.filter (fun k => a k ∈ support x) := by ext k; simp
  rw [Set.ncard_eq_toFinset_card', hu, Finset.card_filter, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, support_ite]

private theorem path_cycle_iff {n : ℕ} (x : PathEdge n → Bit) :
    support x ∈ cycleSpace (pathGraph n) ↔
      ∀ i v, Alive i v → total (x ∘ includeEdge i) v = 0 := by
  classical
  have : Finite (pathGraph n).E := by unfold pathGraph; infer_instance
  change (Set.Finite (support x) ∧ ∀ p : Block n × Vertex,
    Even (Set.ncard {a ∈ support x | Touches (pathEnds a) p})) ↔ _
  simp only [Set.toFinite, true_and, Prod.forall]
  constructor <;> intro h i v
  · intro hv
    have eqn : {a ∈ support x | Touches (pathEnds a) (i, v)} =
        {a ∈ support x | a ∈ Set.range (includeEdge i ∘ star v)} := by
      ext a
      simp [path_touches, hv, Set.range]
    have hi := h i v
    rw [eqn] at hi
    exact (even_range_iff _ ((include_injective i).comp (star_injective v)) x).mp hi
  · by_cases hv : Alive i v
    · have eqn : {a ∈ support x | Touches (pathEnds a) (i, v)} =
          {a ∈ support x | a ∈ Set.range (includeEdge i ∘ star v)} := by
        ext a
        simp [path_touches, hv, Set.range]
      rw [eqn]
      exact (even_range_iff _ ((include_injective i).comp (star_injective v)) x).mpr (h i v hv)
    · have eqn : {a ∈ support x | Touches (pathEnds a) (i, v)} = ∅ := by
        ext a
        simp [path_touches, hv]
      simp [eqn]


/-! ## Restriction and extension of binary cycles -/

private theorem sum_total (x : Edge → Bit) : ∑ v, total x v = 0 := by
  classical
  let slot : Vertex × Fin 3 → Edge := fun p => star p.1 p.2
  calc
    ∑ v, total x v = ∑ p, x (slot p) := by
      rw [Fintype.sum_prod_type]
      rfl
    _ = ∑ p, ∑ e, if slot p = e then x e else 0 := by
      simp [Finset.sum_ite_eq]
    _ = ∑ e, ∑ p, if slot p = e then x e else 0 := Finset.sum_comm
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro e _
      have hc : ∀ e : Edge, (Finset.univ.filter (fun p => slot p = e)).card = 2 := by
        decide +kernel
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, hc, two_nsmul]
      exact (by decide : ∀ a : Bit, a + a = 0) _

private theorem every_block_balanced {n : ℕ} {x : PathEdge n → Bit}
    (h : ∀ i v, Alive i v → total (x ∘ includeEdge i) v = 0) (i : Block n) :
    Balanced (x ∘ includeEdge i) := by
  have go (k : ℕ) : ∀ (i : Block n), i.val = k → Balanced (x ∘ includeEdge i) := by
    induction k with
    | zero =>
      intro i hi
      have h₁ (v : Vertex) (hv : v ≠ rightPort i) : total (x ∘ includeEdge i) v = 0 :=
        h i v ⟨fun hl => by omega, fun _ => hv⟩
      have hs := sum_total (x ∘ includeEdge i)
      rw [Finset.sum_eq_single (rightPort i) (fun v _ hv => h₁ v hv)
        (fun hv => (hv (Finset.mem_univ _)).elim)] at hs
      intro v
      by_cases hv : v = rightPort i
      · exact hv.symm ▸ hs
      · exact h₁ v hv
    | succ k ih =>
      intro i hi
      have hl : HasLeft i := by omega
      let j := prev i hl
      have hji : j.succ = i := prev_succ i hl
      have hj : j.castSucc.val = k := by
        change i.val - 1 = k
        omega
      have hleft : total (x ∘ includeEdge i) (leftPort i) = 0 := by
        rw [← hji]
        simpa only [total, Function.comp_apply, include_left, include_right] using
          ih j.castSucc hj (rightPort j.castSucc)
      have hv (v : Vertex) (hn : v ≠ rightPort i) : total (x ∘ includeEdge i) v = 0 := by
        by_cases he : v = leftPort i
        · exact he.symm ▸ hleft
        · exact h i v ⟨fun _ => he, fun _ => hn⟩
      have hs := sum_total (x ∘ includeEdge i)
      rw [Finset.sum_eq_single (rightPort i) (fun v _ hn => hv v hn)
        (fun hn => (hn (Finset.mem_univ _)).elim)] at hs
      intro v
      by_cases he : v = rightPort i
      · exact he.symm ▸ hs
      · exact hv v he
  exact go i.val i rfl

private def Compatible {n : ℕ} {A : Type*} (y : Block n → Edge → A) : Prop :=
  ∀ (j : Junction n) (k : Fin 3),
    y j.castSucc (star (rightPort j.castSucc) k) = y j.succ (star (leftPort j.succ) k)

private def glue {n : ℕ} {A : Type*} (y : Block n → Edge → A) : PathEdge n → A
  | .inl ⟨(i, e), _⟩ => y i e
  | .inr (j, k) => y j.castSucc (star (rightPort j.castSucc) k)

private theorem glue_include {n : ℕ} {A : Type*} {y : Block n → Edge → A}
    (hy : Compatible y) (i : Block n) (e : Edge) : glue y (includeEdge i e) = y i e := by
  cases ha : includeEdge i e with
  | inl p =>
    obtain ⟨⟨b, f⟩, h⟩ := p
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ((include_internal_iff i e ⟨(b, f), h⟩).mp ha)
    rfl
  | inr p =>
    obtain ⟨j, k⟩ := p
    rcases (include_join_iff i e j k).mp ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact hy j k

private theorem glue_cycle {n : ℕ} {y : Block n → Edge → Bit}
    (hy : ∀ i, Balanced (y i)) (hc : Compatible y) :
    support (glue y) ∈ cycleSpace (pathGraph n) := by
  apply (path_cycle_iff _).mpr
  intro i v _
  have he : glue y ∘ includeEdge i = y i := funext (glue_include hc i)
  rw [he]
  exact hy i v

private theorem map_preserves_balanced {m n : ℕ} {f : PathEdge m → PathEdge n}
    (hf : IsCycleContinuous (pathGraph m) (pathGraph n) f) {x : PathEdge n → Bit}
    (hx : support x ∈ cycleSpace (pathGraph n)) (i : Block m) :
    Balanced (x ∘ f ∘ includeEdge i) :=
  every_block_balanced ((path_cycle_iff (x ∘ f)).mp (hf _ hx)) i

private theorem realizeRight {n : ℕ} (i : Block n) (hr : HasRight i) (p : Fin 3 → Bit)
    (hp : ∑ k, p k = 0) :
    ∃ y : Edge → Bit, Balanced y ∧ (∀ k, y (star (rightPort i) k) = p k) ∧
      (HasLeft i → ∀ k, y (star (leftPort i) k) = 0) := by
  obtain ⟨y, hy, he, _, hzero⟩ := realizePort _ (right_isPort i) p hp
  refine ⟨y, hy, he, fun hl k => ?_⟩
  obtain ⟨h₀, h₃⟩ := active_ports i hl hr
  rw [h₀]
  exact hzero h₃ k

private theorem realizeLeft {n : ℕ} (i : Block n) (hl : HasLeft i) (p : Fin 3 → Bit)
    (hp : ∑ k, p k = 0) :
    ∃ y : Edge → Bit, Balanced y ∧ (∀ k, y (star (leftPort i) k) = p k) ∧
      (HasRight i → ∀ k, y (star (rightPort i) k) = 0) := by
  obtain ⟨y, hy, he, hzero, _⟩ := realizePort _ (left_isPort i) p hp
  refine ⟨y, hy, he, fun hr k => ?_⟩
  obtain ⟨h₀, h₃⟩ := active_ports i hl hr
  rw [h₃]
  exact hzero h₀ k

-- A cycle on a block extends to the whole path using only its immediate neighbors.
private theorem extendBlock {n : ℕ} (i : Block n) {x : Edge → Bit} (hx : Balanced x) :
    ∃ z : PathEdge n → Bit, support z ∈ cycleSpace (pathGraph n) ∧ z ∘ includeEdge i = x := by
  classical
  let l (j : Block n) (h : HasRight j) :=
    realizeRight j h (x ∘ star (leftPort i)) (hx (leftPort i))
  let r (j : Block n) (h : HasLeft j) :=
    realizeLeft j h (x ∘ star (rightPort i)) (hx (rightPort i))
  let y (j : Block n) : Edge → Bit :=
    if j.val = i.val then x
    else if h : j.val + 1 = i.val then (l j (by have hi := i.isLt; omega)).choose
    else if h : i.val + 1 = j.val then (r j (by omega)).choose
    else fun _ => 0
  have yp (j : Block n) (h : j.val + 1 = i.val) :
      y j = (l j (by have hi := i.isLt; omega)).choose := by
    dsimp only [y]
    split
    · omega
    · rfl
  have ys (j : Block n) (h : i.val + 1 = j.val) :
      y j = (r j (by omega)).choose := by
    dsimp only [y]
    split
    · omega
    split
    · omega
    · rfl
  have yi (j : Block n) (h : j.val = i.val) : y j = x := by
    exact ite_eq_left h
  have yz (j : Block n) (h₀ : j.val ≠ i.val) (h₁ : j.val + 1 ≠ i.val)
      (h₂ : i.val + 1 ≠ j.val) : y j = fun _ => 0 := by
    dsimp only [y]
    rw [ite_eq_right h₀, dite_eq_right h₁, dite_eq_right h₂]
  have hy (j : Block n) : Balanced (y j) := by
    by_cases h₀ : j.val = i.val
    · rw [yi j h₀]
      exact hx
    by_cases h₁ : j.val + 1 = i.val
    · rw [yp j h₁]
      exact (l _ (by have hi := i.isLt; omega)).choose_spec.1
    by_cases h₂ : i.val + 1 = j.val
    · rw [ys j h₂]
      exact (r _ (by omega)).choose_spec.1
    rw [yz j h₀ h₁ h₂]
    intro v
    simp [total]
  have hc : Compatible y := by
    intro j k
    have hval : j.castSucc.val = j.val := rfl
    have hsucc : j.succ.val = j.val + 1 := rfl
    by_cases h₀ : j.val = i.val
    · have hEq : j.castSucc = i := Fin.ext h₀
      rw [yi _ h₀, ys j.succ (by omega),
        (r j.succ (left_of_succ j)).choose_spec.2.1 k, hEq]
      rfl
    · by_cases h₁ : j.val + 1 = i.val
      · have hEq : j.succ = i := Fin.ext h₁
        rw [yp j.castSucc h₁, yi j.succ h₁,
          (l j.castSucc (right_of_castSucc j)).choose_spec.2.1 k, hEq]
        rfl
      · by_cases h₂ : j.val + 1 + 1 = i.val
        · rw [yz j.castSucc h₀ h₁ (by omega), yp j.succ h₂]
          exact ((l j.succ (by have hi := i.isLt; omega)).choose_spec.2.2
            (left_of_succ j) k).symm
        · by_cases h₃ : i.val + 1 = j.val
          · rw [ys j.castSucc h₃, yz j.succ h₁ h₂ (by omega)]
            exact (r j.castSucc (by omega)).choose_spec.2.2 (right_of_castSucc j) k
          · rw [yz j.castSucc h₀ h₁ h₃, yz j.succ h₁ h₂ (by omega)]
  refine ⟨glue y, glue_cycle hy hc, funext fun e => ?_⟩
  rw [Function.comp_apply, glue_include hc]
  rw [yi i rfl]

/-! ## Covering a proper edge range with two cycles -/

-- These six linear automorphisms permute the three nonzero colors.
private def recolor (j : Fin 6) (p : Color) : Color :=
  ![p, (p.2, p.1), (p.1, p.1 + p.2), (p.1 + p.2, p.1),
    (p.2, p.1 + p.2), (p.1 + p.2, p.2)] j

private theorem recolor_zero (j : Fin 6) (a : Color) : recolor j a = 0 ↔ a = 0 :=
  (by decide +kernel : ∀ j a, recolor j a = 0 ↔ a = 0) j a

private theorem flow_recolor (j : Fin 6) {x : Edge → Color} (hx : Flow x) :
    Flow (recolor j ∘ x) := by
  have hl : ∀ (j : Fin 6) (a b c : Color), a + b + c = 0 →
      recolor j a + recolor j b + recolor j c = 0 := by
    decide +kernel
  have hz (v : Vertex) : total (recolor j ∘ x) v = 0 := by
    simp only [total, Fin.sum_univ_three, Function.comp_apply]
    apply hl
    exact Prod.ext
      (by simpa only [total, Fin.sum_univ_three, Function.comp_apply, Prod.fst_add, Prod.snd_add,
        Prod.fst_zero, Prod.snd_zero] using hx.1 v)
      (by simpa only [total, Fin.sum_univ_three, Function.comp_apply, Prod.fst_add, Prod.snd_add,
        Prod.fst_zero, Prod.snd_zero] using hx.2 v)
  constructor <;> intro v
  · simpa only [total, Fin.sum_univ_three, Function.comp_apply, Prod.fst_add, Prod.snd_add,
      Prod.fst_zero, Prod.snd_zero] using congrArg Prod.fst (hz v)
  · simpa only [total, Fin.sum_univ_three, Function.comp_apply, Prod.fst_add, Prod.snd_add,
      Prod.fst_zero, Prod.snd_zero] using congrArg Prod.snd (hz v)

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation checks all pairs of triples of colors.
set_option synthInstance.maxSize 512 in
private theorem recolor_match (a b : Fin 3 → Color)
    (ha : a 0 + a 1 + a 2 = 0) (hb : b 0 + b 1 + b 2 = 0)
    (hz : ∀ k, a k = 0 ↔ b k = 0) : ∃ j : Fin 6, ∀ k, recolor j (a k) = b k := by
  have h : ∀ a₀ a₁ a₂ b₀ b₁ b₂ : Color,
      a₀ + a₁ + a₂ = 0 → b₀ + b₁ + b₂ = 0 →
      decide (a₀ = 0) = decide (b₀ = 0) →
      decide (a₁ = 0) = decide (b₁ = 0) →
      decide (a₂ = 0) = decide (b₂ = 0) →
      ∃ j, recolor j a₀ = b₀ ∧ recolor j a₁ = b₁ ∧ recolor j a₂ = b₂ := by
    decide +kernel
  have hc (k : Fin 3) : decide (a k = 0) = decide (b k = 0) := by
    by_cases he : a k = 0
    · simp [he, (hz k).mp he]
    · have hn : b k ≠ 0 := fun hb => he ((hz k).mpr hb)
      simp [he, hn]
  obtain ⟨j, h₀, h₁, h₂⟩ := h _ _ _ _ _ _ ha hb (hc 0) (hc 1) (hc 2)
  refine ⟨j, fun k => ?_⟩
  fin_cases k <;> assumption

private theorem flow_total {x : Edge → Color} (hx : Flow x) (v : Vertex) :
    x (star v 0) + x (star v 1) + x (star v 2) = 0 :=
  Prod.ext
    (by simpa only [total, Fin.sum_univ_three, Function.comp_apply, Prod.fst_add, Prod.snd_add,
        Prod.fst_zero, Prod.snd_zero] using hx.1 v)
    (by simpa only [total, Fin.sum_univ_three, Function.comp_apply, Prod.fst_add, Prod.snd_add,
        Prod.fst_zero, Prod.snd_zero] using hx.2 v)

-- Work left to right. Adjusting the next block leaves all earlier junctions unchanged.
private theorem align_family {n : ℕ} (x : Block n → Edge → Color)
    (hx : ∀ i, Flow (x i))
    (hz : ∀ (j : Junction n) k,
      x j.castSucc (star (rightPort j.castSucc) k) = 0 ↔
        x j.succ (star (leftPort j.succ) k) = 0) :
    ∃ y : Block n → Edge → Color, (∀ i, Flow (y i)) ∧
      (∀ i e, y i e = 0 ↔ x i e = 0) ∧ Compatible y := by
  classical
  have go (l : ℕ) : ∃ y : Block n → Edge → Color, (∀ i, Flow (y i)) ∧
      (∀ i e, y i e = 0 ↔ x i e = 0) ∧
      (∀ (j : Junction n), j.val < l → ∀ k,
        y j.castSucc (star (rightPort j.castSucc) k) =
          y j.succ (star (leftPort j.succ) k)) := by
    induction l with
    | zero => exact ⟨x, hx, fun _ _ => Iff.rfl, fun _ hj => (Nat.not_lt_zero _ hj).elim⟩
    | succ l ih =>
      obtain ⟨y, hy, hz', hc⟩ := ih
      by_cases hl : l < n + 2
      · let j : Junction n := ⟨l, hl⟩
        let a := y j.succ ∘ star (leftPort j.succ)
        let b := y j.castSucc ∘ star (rightPort j.castSucc)
        have ha : a 0 + a 1 + a 2 = 0 := flow_total (hy j.succ) _
        have hb : b 0 + b 1 + b 2 = 0 := flow_total (hy j.castSucc) _
        obtain ⟨t, ht⟩ := recolor_match a b ha hb fun k =>
          (hz' _ _).trans ((hz j k).symm.trans (hz' _ _).symm)
        let yy (i : Block n) : Edge → Color := if i = j.succ then recolor t ∘ y i else y i
        refine ⟨yy, ?_, ?_, ?_⟩
        · intro i
          unfold yy
          split
          · exact flow_recolor t (hy i)
          · exact hy i
        · intro i e
          unfold yy
          split
          · exact (recolor_zero t _).trans (hz' i e)
          · exact hz' i e
        · intro j' hj' k
          have hn : j'.castSucc ≠ j.succ := by
            intro h
            have eq := congrArg Fin.val h
            change j'.val = l + 1 at eq
            omega
          by_cases he : j' = j
          · subst j'
            simpa only [yy, hn, ite_false, ite_true, a, b, Function.comp_apply] using (ht k).symm
          · have hns : j'.succ ≠ j.succ := fun h => he (Fin.ext (by
              have eq := congrArg Fin.val h
              change j'.val + 1 = l + 1 at eq
              change j'.val = l
              omega))
            have hlt : j'.val < l := by
              have hne : j'.val ≠ l := fun h => he (Fin.ext h)
              omega
            simpa only [yy, hn, hns, ite_false] using hc j' hlt k
      · exact ⟨y, hy, hz', fun j _ k => hc j (by have hj := j.isLt; omega) k⟩
  obtain ⟨y, hy, hz', hc⟩ := go (n + 2)
  exact ⟨y, hy, hz', fun j => hc j j.isLt⟩

-- If a set of edges omits an edge of every block, there is a binary pair of
-- cycles whose union covers the set. At each incomplete junction, prescribe zero
-- on one missing edge and nowhere else on the junction.
private theorem cover_proper_range {n : ℕ} (P : PathEdge n → Prop)
    (hmiss : ∀ i : Block n, ∃ e, ¬P (includeEdge i e)) :
    ∃ z : PathEdge n → Color,
      (support (Prod.fst ∘ z) ∈ cycleSpace (pathGraph n)) ∧
      (support (Prod.snd ∘ z) ∈ cycleSpace (pathGraph n)) ∧ ∀ e, P e → z e ≠ 0 := by
  classical
  let missing (j : Junction n) : Option (Fin 3) :=
    if h : ∃ k : Fin 3, ¬P (.inr (j, k)) then some h.choose else none
  have missing_some (j : Junction n) (k : Fin 3) (h : missing j = some k) :
      ¬P (.inr (j, k)) := by
    unfold missing at h
    split at h
    · rename_i he
      exact (Option.some.inj h) ▸ he.choose_spec
    · cases h
  have missing_none (j : Junction n) (h : missing j = none) (k : Fin 3) :
      P (.inr (j, k)) := by
    by_contra hn
    have he : ∃ k : Fin 3, ¬P (.inr (j, k)) := ⟨k, hn⟩
    unfold missing at h
    rw [dite_eq_left he] at h
    cases h
  let l (i : Block n) : Option (Fin 3) := if h : HasLeft i then missing (prev i h) else none
  let r (i : Block n) : Option (Fin 3) := if h : HasRight i then missing (next i h) else none
  have l_active (i : Block n) (h : HasLeft i) : l i = missing (prev i h) := by
    unfold l
    rw [dite_eq_left h]
  have r_active (i : Block n) (h : HasRight i) : r i = missing (next i h) := by
    unfold r
    rw [dite_eq_left h]
  have l_some (i : Block n) (k : Fin 3) (h : l i = some k) : HasLeft i := by
    unfold l at h
    split at h
    · assumption
    · cases h
  have r_some (i : Block n) (k : Fin 3) (h : r i = some k) : HasRight i := by
    unfold r at h
    split at h
    · assumption
    · cases h
  have left_gap (i : Block n) (k : Fin 3) (h : l i = some k) :
      ¬P (includeEdge i (star (leftPort i) k)) := by
    have hl := l_some i k h
    rw [l_active i hl] at h
    rw [← prev_succ i hl, include_left]
    exact missing_some _ _ h
  have right_gap (i : Block n) (k : Fin 3) (h : r i = some k) :
      ¬P (includeEdge i (star (rightPort i) k)) := by
    have hr := r_some i k h
    rw [r_active i hr] at h
    rw [← next_castSucc i hr, include_right]
    exact missing_some _ _ h
  have localFlow (i : Block n) : ∃ (x : Edge → Color) (extra : Option Edge),
      Flow x ∧ (∀ e, extra = some e → ¬P (includeEdge i e) ∧ ¬LeftEdge i e ∧ ¬RightEdge i e) ∧
        ∀ e, x e = 0 ↔
          ((∃ k, l i = some k ∧ e = star (leftPort i) k) ∨
            (∃ k, r i = some k ∧ e = star (rightPort i) k) ∨ extra = some e) := by
    cases hL : l i with
    | none =>
      cases hR : r i with
      | none =>
        obtain ⟨e, he⟩ := hmiss i
        obtain ⟨x, hx, hz⟩ := singleDeletion_flow e
        have hnl : ¬LeftEdge i e := by
          rintro ⟨hl, k, rfl⟩
          rw [l_active i hl] at hL
          rw [← prev_succ i hl, include_left] at he
          exact he (missing_none _ hL k)
        have hnr : ¬RightEdge i e := by
          rintro ⟨hr, k, rfl⟩
          rw [r_active i hr] at hR
          rw [← next_castSucc i hr, include_right] at he
          exact he (missing_none _ hR k)
        refine ⟨x, some e, hx, fun f hf => ?_, fun f => ?_⟩
        · cases Option.some.inj hf
          exact ⟨he, hnl, hnr⟩
        · simpa [hL, hR, eq_comm] using hz f
      | some k =>
        obtain ⟨x, hx, hz⟩ := singleDeletion_flow (star (rightPort i) k)
        refine ⟨x, none, hx, (fun _ he => by cases he), fun e => ?_⟩
        simpa [hL, hR] using hz e
    | some j =>
      cases hR : r i with
      | none =>
        obtain ⟨x, hx, hz⟩ := singleDeletion_flow (star (leftPort i) j)
        refine ⟨x, none, hx, (fun _ he => by cases he), fun e => ?_⟩
        simpa [hL, hR] using hz e
      | some k =>
        obtain ⟨hl, hr⟩ := active_ports i (l_some i j hL) (r_some i k hR)
        obtain ⟨x, hx, hz⟩ := doubleDeletion_flow j k
        refine ⟨x, none, hx, (fun _ he => by cases he), fun e => ?_⟩
        simpa [hL, hR, hl, hr] using hz e
  choose x extra hx hex hz using localFlow
  have hP (i : Block n) (e : Edge) (hp : P (includeEdge i e)) : x i e ≠ 0 := by
    intro he
    rcases (hz i e).mp he with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | he
    · exact left_gap i k hk hp
    · exact right_gap i k hk hp
    · exact (hex i e he).1 hp
  have hLeft (i : Block n) (hl : HasLeft i) (k : Fin 3) :
      x i (star (leftPort i) k) = 0 ↔ l i = some k := by
    constructor
    · intro h
      rcases (hz _ _).mp h with ⟨k', hk', he⟩ | ⟨k', hk', he⟩ | he
      · exact star_injective _ he ▸ hk'
      · have hle : LeftEdge i (star (leftPort i) k) := ⟨hl, k, rfl⟩
        exact (left_not_right hle ⟨r_some i k' hk', k', he.symm⟩).elim
      · exact ((hex _ _ he).2.1 ⟨hl, k, rfl⟩).elim
    · exact fun h => (hz _ _).mpr (Or.inl ⟨k, h, rfl⟩)
  have hRight (i : Block n) (hr : HasRight i) (k : Fin 3) :
      x i (star (rightPort i) k) = 0 ↔ r i = some k := by
    constructor
    · intro h
      rcases (hz _ _).mp h with ⟨k', hk', he⟩ | ⟨k', hk', he⟩ | he
      · have hre : RightEdge i (star (rightPort i) k) := ⟨hr, k, rfl⟩
        exact (left_not_right ⟨l_some i k' hk', k', he.symm⟩ hre).elim
      · exact star_injective _ he ▸ hk'
      · exact ((hex _ _ he).2.2 ⟨hr, k, rfl⟩).elim
    · exact fun h => (hz _ _).mpr (Or.inr (Or.inl ⟨k, h, rfl⟩))
  have hpattern (j : Junction n) (k : Fin 3) :
      x j.castSucc (star (rightPort j.castSucc) k) = 0 ↔
        x j.succ (star (leftPort j.succ) k) = 0 := by
    rw [hRight _ (right_of_castSucc j), hLeft _ (left_of_succ j),
      l_active _ (left_of_succ j), r_active _ (right_of_castSucc j),
      prev_of_succ, next_of_castSucc]
  obtain ⟨y, hy, hcolors, hcy⟩ := align_family x hx hpattern
  have hp' (t : Color → Bit) (ht : ∀ i, Balanced (t ∘ y i)) :
      support (t ∘ glue y) ∈ cycleSpace (pathGraph n) := by
    apply (path_cycle_iff _).mpr
    intro i v _
    have he : (t ∘ glue y) ∘ includeEdge i = t ∘ y i := by
      funext e
      simp only [Function.comp_apply, glue_include hcy]
    rw [he]
    exact ht i v
  refine ⟨glue y, hp' _ fun i => (hy i).1, hp' _ fun i => (hy i).2, fun e he hz' => ?_⟩
  cases e with
  | inl p =>
    obtain ⟨⟨i, e⟩, h⟩ := p
    have hi : includeEdge i e = .inl ⟨(i, e), h⟩ := (include_internal_iff ..).mpr rfl
    exact hP i e (hi ▸ he) ((hcolors _ _).mp hz')
  | inr p =>
    obtain ⟨j, k⟩ := p
    exact hP j.castSucc (star (rightPort j.castSucc) k)
      (include_right j k ▸ he) ((hcolors _ _).mp hz')

private theorem covers_block {m n : ℕ} {f : PathEdge m → PathEdge n}
    (hf : IsCycleContinuous (pathGraph m) (pathGraph n) f) (i : Block m) :
    ∃ j : Block n, Set.range (includeEdge j) ⊆ Set.range (f ∘ includeEdge i) := by
  classical
  by_contra! hn
  obtain ⟨z, hz₁, hz₂, hp⟩ := cover_proper_range (fun e => e ∈ Set.range (f ∘ includeEdge i))
    fun j => by
      obtain ⟨_, ⟨e, rfl⟩, he⟩ := Set.not_subset.mp (hn j)
      exact ⟨e, he⟩
  obtain ⟨e, he⟩ := noFlow (z ∘ f ∘ includeEdge i)
    ⟨map_preserves_balanced hf hz₁ i, map_preserves_balanced hf hz₂ i⟩
  exact hp _ ⟨e, rfl⟩ he


/-! ## Distinguishing the three attachment vertices -/

-- The number of five-edge cycles meeting an edge set determines the three port
-- types. Using a cycle-space invariant avoids requiring an automorphism theorem.
private def fiveCycles (s : Set Edge) : Set (Edge → Bit) :=
  {x | Balanced x ∧ (support x).ncard = 5 ∧ (support x ∩ s).Nonempty}

private def bitCount (m : ℕ) : ℕ :=
  (Finset.univ.filter fun e : Edge => m.testBit e.val = true).card

private theorem ncard_support_bits (m : ℕ) : (support (bits m)).ncard = bitCount m := by
  classical
  have he : support (bits m) =
      ↑(Finset.univ.filter fun e : Edge => m.testBit e.val = true) := by
    ext e
    cases h : m.testBit e.val <;> simp [bits, support, h]
  rw [he, Set.ncard_coe_finset]
  rfl

private theorem touches_iff_nonempty (m : ℕ) (v : Vertex) :
    touches m v = true ↔ (support (bits m) ∩ Set.range (star v)).Nonempty := by
  have h : ∀ k : Fin 3, bits m (star v k) = 1 ↔ m.testBit (star v k).val = true := by
    intro k
    unfold bits
    cases m.testBit (star v k).val <;> decide
  simp only [Set.Nonempty, Set.mem_inter_iff, Set.mem_range]
  have hr : (∃ e, e ∈ support (bits m) ∧ ∃ k, star v k = e) ↔
      ∃ k, m.testBit (star v k).val = true := by
    constructor
    · rintro ⟨_, he, k, rfl⟩
      exact ⟨k, (h k).mp he⟩
    · rintro ⟨k, hk⟩
      exact ⟨_, (h k).mpr hk, k, rfl⟩
  rw [hr, Fin.exists_fin_succ]
  simp [touches, Bool.or_eq_true, or_assoc]

private def starMasks (v : Vertex) : Finset ℕ :=
  (cycleMasks.filter (fun m => bitCount m == 5 && touches m v)).toFinset

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation checks all 1024 masks in the binary cycle space.
private theorem masks_in_range : cycleMasks.all (fun m => decide (m < 2 ^ 27)) = true := by
  decide +kernel

private theorem bits_injective_on_masks : Set.InjOn bits (↑cycleMasks.toFinset : Set ℕ) := by
  intro m hm k hk he
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 27
  · have hv := congrFun he ⟨i, hi⟩
    simp only [bits] at hv
    cases hp : m.testBit i <;> cases hq : k.testBit i <;> simp_all
  · have hm' : m < 2 ^ 27 :=
      of_decide_eq_true (List.all_eq_true.mp masks_in_range _ (List.mem_toFinset.mp hm))
    have hk' : k < 2 ^ 27 :=
      of_decide_eq_true (List.all_eq_true.mp masks_in_range _ (List.mem_toFinset.mp hk))
    have hle : 2 ^ 27 ≤ 2 ^ i := pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) (by omega)
    rw [Nat.testBit_lt_two_pow (hm'.trans_le hle), Nat.testBit_lt_two_pow (hk'.trans_le hle)]

private theorem starMasks_spec (v : Vertex) (m : ℕ) :
    m ∈ starMasks v ↔ m ∈ cycleMasks ∧ bits m ∈ fiveCycles (Set.range (star v)) := by
  simp only [starMasks, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, beq_iff_eq,
    touches_iff_nonempty, fiveCycles, Set.mem_ofPred_eq, ncard_support_bits]
  constructor
  · rintro ⟨hm, hcount, ht⟩
    exact ⟨hm, closure_balanced _ hm, hcount, ht⟩
  · rintro ⟨hm, _, hcount, ht⟩
    exact ⟨hm, hcount, ht⟩

private theorem fiveCycles_ncard (v : Vertex) :
    (fiveCycles (Set.range (star v))).ncard = (starMasks v).card := by
  rw [← Set.ncard_coe_finset]
  symm
  apply Set.BijOn.ncard_eq (f := bits)
  refine ⟨fun m hm => ((starMasks_spec v m).mp hm).2, ?_, ?_⟩
  · intro m hm k hk
    exact bits_injective_on_masks
      (List.mem_toFinset.mpr ((starMasks_spec v m).mp hm).1)
      (List.mem_toFinset.mpr ((starMasks_spec v k).mp hk).1)
  · intro x hx
    obtain ⟨m, hm, rfl⟩ := exists_mask hx.1
    exact ⟨m, (starMasks_spec v m).mpr ⟨hm, hx⟩, rfl⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation counts five-edge cycles by filtering all 1024 masks.
private theorem port_masks_card :
    (starMasks 0).card = 2 ∧ (starMasks 3).card = 3 ∧ (starMasks 17).card = 4 := by
  decide +kernel

private theorem ncard_fiveCycles_image (g : Equiv.Perm Edge)
    (hg : ∀ x, Balanced x → Balanced (x ∘ g)) (s : Set Edge) :
    (fiveCycles (g '' s)).ncard = (fiveCycles s).ncard := by
  classical
  have hinj : Function.Injective (fun x : Edge → Bit => x ∘ g) := by
    intro x y h
    funext e
    obtain ⟨e', rfl⟩ := g.surjective e
    exact congrFun h e'
  let pb : {x : Edge → Bit // Balanced x} → {x : Edge → Bit // Balanced x} :=
    fun x => ⟨x.val ∘ g, hg _ x.property⟩
  have hsurj : Function.Surjective pb :=
    Finite.surjective_of_injective (fun x y h => Subtype.ext (hinj (congrArg Subtype.val h)))
  have hc (x : Edge → Bit) : (support (x ∘ g)).ncard = (support x).ncard := by
    exact (show Set.BijOn g (support (x ∘ g)) (support x) from
      ⟨fun _ h => h, g.injective.injOn, fun e he => ⟨g.symm e, by simpa [support] using he,
        g.apply_symm_apply e⟩⟩).ncard_eq
  have ht (x : Edge → Bit) :
      (support (x ∘ g) ∩ s).Nonempty ↔ (support x ∩ (g '' s)).Nonempty := by
    constructor
    · rintro ⟨e, he, hs⟩
      exact ⟨g e, he, ⟨e, hs, rfl⟩⟩
    · rintro ⟨_, he, e, hs, rfl⟩
      exact ⟨e, he, hs⟩
  apply Set.BijOn.ncard_eq (f := fun x : Edge → Bit => x ∘ g)
  refine ⟨fun x hx => ⟨hg x hx.1, (hc x).trans hx.2.1, (ht x).mpr hx.2.2⟩, hinj.injOn, ?_⟩
  intro y hy
  obtain ⟨⟨x, hx⟩, hxy⟩ := hsurj ⟨y, hy.1⟩
  have hp : x ∘ g = y := congrArg Subtype.val hxy
  refine ⟨x, ⟨hx, ?_, (ht x).mp (hp ▸ hy.2.2)⟩, hp⟩
  rw [← hc x, hp]
  exact hy.2.1

private theorem ports_eq_of_signature {v w : Vertex} (hv : IsPort v) (hw : IsPort w)
    (h : (fiveCycles (Set.range (star v))).ncard =
      (fiveCycles (Set.range (star w))).ncard) : v = w := by
  rw [fiveCycles_ncard, fiveCycles_ncard] at h
  obtain ⟨h₀, h₃, h₁₇⟩ := port_masks_card
  rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
    first | rfl | omega

private theorem per_block {m n : ℕ} {f : PathEdge m → PathEdge n}
    (hf : IsCycleContinuous (pathGraph m) (pathGraph n) f) (i : Block m) :
    ∃ (j : Block n) (g : Equiv.Perm Edge),
      (∀ e, f (includeEdge i e) = includeEdge j (g e)) ∧
        ∀ x : Edge → Bit, Balanced x → Balanced (x ∘ g) := by
  obtain ⟨j, hj⟩ := covers_block hf i
  have h (e : Edge) : ∃ t, f (includeEdge i t) = includeEdge j e := hj ⟨e, rfl⟩
  choose g hg using h
  have hinj : Function.Injective g := fun a b h => include_injective j (by rw [← hg a, h, hg b])
  let e := (Equiv.ofBijective g ⟨hinj, Finite.surjective_of_injective hinj⟩).symm
  have he (t : Edge) : f (includeEdge i t) = includeEdge j (e t) := by
    have ht : g (e t) = t := e.symm_apply_apply t
    rw [← hg (e t), ht]
  refine ⟨j, e, he, fun x hx => ?_⟩
  obtain ⟨z, hz, hzx⟩ := extendBlock j hx
  have h' : z ∘ f ∘ includeEdge i = x ∘ e := by
    funext t
    change z (f (includeEdge i t)) = x (e t)
    rw [he]
    exact congrFun hzx (e t)
  exact h' ▸ map_preserves_balanced hf hz i

/-! ## Comparing paths under cycle-continuous maps -/

private theorem common_edge {n : ℕ} {i j : Block n} {e f : Edge} (hne : i ≠ j)
    (h : includeEdge i e = includeEdge j f) :
    ∃ (q : Junction n) (k : Fin 3),
      (i = q.castSucc ∧ j = q.succ ∧ e = star (rightPort i) k ∧ f = star (leftPort j) k) ∨
        (i = q.succ ∧ j = q.castSucc ∧ e = star (leftPort i) k ∧ f = star (rightPort j) k) := by
  cases hi : includeEdge i e with
  | inl p =>
    have he := (include_internal_iff i e p).mp hi
    have hf := (include_internal_iff j f p).mp (h.symm.trans hi)
    exact (hne (congrArg Prod.fst (he.trans hf.symm))).elim
  | inr p =>
    obtain ⟨q, k⟩ := p
    have he := (include_join_iff i e q k).mp hi
    have hf := (include_join_iff j f q k).mp (h.symm.trans hi)
    rcases he with ⟨he, he'⟩ | ⟨he, he'⟩ <;> rcases hf with ⟨hf, hf'⟩ | ⟨hf, hf'⟩
    · exact (hne (he.trans hf.symm)).elim
    · exact ⟨q, k, Or.inl ⟨he, hf, he', hf'⟩⟩
    · exact ⟨q, k, Or.inr ⟨he, hf, he', hf'⟩⟩
    · exact (hne (he.trans hf.symm)).elim

private theorem port_eq_of_mapsTo {g : Equiv.Perm Edge}
    (hg : ∀ x, Balanced x → Balanced (x ∘ g))
    {v w : Vertex} (hv : IsPort v) (hw : IsPort w)
    (hm : Set.MapsTo g (Set.range (star v)) (Set.range (star w))) : v = w := by
  have h := Set.eq_of_subset_of_ncard_le (s := g '' Set.range (star v))
    (t := Set.range (star w)) (Set.image_subset_iff.mpr hm) (by
      rw [Set.ncard_image_of_injective _ g.injective,
        Set.ncard_range_of_injective (star_injective v),
        Set.ncard_range_of_injective (star_injective w)])
  apply ports_eq_of_signature hv hw
  rw [← ncard_fiveCycles_image g hg, h]

private theorem forward_matches {n : ℕ} (q : Junction n)
    {g h : Equiv.Perm Edge}
    (hg : ∀ x, Balanced x → Balanced (x ∘ g))
    (hh : ∀ x, Balanced x → Balanced (x ∘ h))
    {v w : Vertex} (hv : IsPort v) (hw : IsPort w)
    (hjoin : ∀ k : Fin 3,
      includeEdge q.castSucc (g (star v k)) = includeEdge q.succ (h (star w k))) :
    v = rightPort q.castSucc ∧ w = leftPort q.succ := by
  have hne : q.castSucc ≠ q.succ := fun he => by
    have hval := congrArg Fin.val he
    change q.val = q.val + 1 at hval
    omega
  have matching (k : Fin 3) : ∃ l : Fin 3,
      g (star v k) = star (rightPort q.castSucc) l ∧
        h (star w k) = star (leftPort q.succ) l := by
    obtain ⟨r, l, h⟩ := common_edge hne (hjoin k)
    rcases h with h | h
    · exact ⟨l, h.2.2⟩
    · obtain ⟨ha, hb, _, _⟩ := h
      have hav := congrArg Fin.val ha
      have hbv := congrArg Fin.val hb
      change q.val = r.val + 1 at hav
      change q.val + 1 = r.val at hbv
      omega
  exact ⟨port_eq_of_mapsTo hg hv (right_isPort _) (by
      rintro _ ⟨k, rfl⟩
      obtain ⟨l, hl, _⟩ := matching k
      exact ⟨l, hl.symm⟩),
    port_eq_of_mapsTo hh hw (left_isPort _) (by
      rintro _ ⟨k, rfl⟩
      obtain ⟨l, _, hl⟩ := matching k
      exact ⟨l, hl.symm⟩)⟩

private theorem port_pairs {n : ℕ} (j : Junction n) :
    (rightPort j.castSucc, leftPort j.succ) = (17, 0) ∨
      (rightPort j.castSucc, leftPort j.succ) = (3, 0) ∨
      (rightPort j.castSucc, leftPort j.succ) = (3, 17) := by
  have ha : j.castSucc.val = j.val := rfl
  have hb : j.succ.val = j.val + 1 := rfl
  unfold rightPort leftPort
  rw [ha, hb]
  by_cases h₀ : j.val = 0
  · have hn : j.val + 1 ≠ n + 2 := by omega
    exact Or.inl (by rw [ite_eq_left h₀, ite_eq_right hn])
  · by_cases hlast : j.val + 1 = n + 2
    · exact Or.inr (Or.inr (by rw [ite_eq_right h₀, ite_eq_left hlast]))
    · exact Or.inr (Or.inl (by rw [ite_eq_right h₀, ite_eq_right hlast]))

private theorem port_pair_ne {n : ℕ} (j : Junction n) :
    rightPort j.castSucc ≠ leftPort j.succ := by
  have h : ∀ a b : Vertex, (a, b) = (17, 0) ∨ (a, b) = (3, 0) ∨ (a, b) = (3, 17) →
      a ≠ b := by decide +kernel
  exact h _ _ (port_pairs j)

private theorem no_reverse {m n : ℕ} (i : Junction m) (j : Junction n) :
    ¬(rightPort i.castSucc = leftPort j.succ ∧ leftPort i.succ = rightPort j.castSucc) := by
  let ok (a b : Vertex) := (a, b) = (17, 0) ∨ (a, b) = (3, 0) ∨ (a, b) = (3, 17)
  have h : ∀ a b : Vertex, ¬(ok a b ∧ ok b a) := by
    dsimp [ok]
    decide +kernel
  rintro ⟨ha, hb⟩
  apply h (rightPort i.castSucc) (leftPort i.succ)
  exact ⟨port_pairs i, ha ▸ hb ▸ port_pairs j⟩

private theorem map_path_length {m n : ℕ} {f : PathEdge m → PathEdge n}
    (hf : IsCycleContinuous (pathGraph m) (pathGraph n) f) : m = n := by
  have he (i : Block m) := per_block hf i
  choose p g hp hgood using he
  have hj (j : Junction m) : ∃ q : Junction n,
      p j.castSucc = q.castSucc ∧ p j.succ = q.succ ∧
        rightPort j.castSucc = rightPort q.castSucc ∧ leftPort j.succ = leftPort q.succ := by
    have hjoin (k : Fin 3) :
        includeEdge (p j.castSucc) (g j.castSucc (star (rightPort j.castSucc) k)) =
          includeEdge (p j.succ) (g j.succ (star (leftPort j.succ) k)) := by
      rw [← hp, ← hp, include_right, include_left]
    have hn : p j.castSucc ≠ p j.succ := by
      intro hn
      have heq : g j.castSucc '' Set.range (star (rightPort j.castSucc)) =
          g j.succ '' Set.range (star (leftPort j.succ)) := by
        ext e
        constructor
        · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
          refine ⟨_, ⟨k, rfl⟩, (include_injective (p j.castSucc) ?_).symm⟩
          rw [hn]
          exact (hn ▸ hjoin k)
        · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
          refine ⟨_, ⟨k, rfl⟩, include_injective (p j.castSucc) ?_⟩
          rw [hn]
          exact (hn ▸ hjoin k)
      apply port_pair_ne j
      apply ports_eq_of_signature (right_isPort _) (left_isPort _)
      calc
        _ = (fiveCycles (g j.castSucc '' Set.range (star (rightPort j.castSucc)))).ncard :=
          (ncard_fiveCycles_image _ (hgood j.castSucc) _).symm
        _ = (fiveCycles (g j.succ '' Set.range (star (leftPort j.succ)))).ncard :=
          congrArg (fun s => (fiveCycles s).ncard) heq
        _ = _ := ncard_fiveCycles_image _ (hgood j.succ) _
    obtain ⟨q, k, h⟩ := common_edge hn (hjoin 0)
    rcases h with ⟨h₁, h₂, _, _⟩ | ⟨h₁, h₂, _, _⟩
    · refine ⟨q, h₁, h₂, forward_matches q (hgood j.castSucc) (hgood j.succ)
        (right_isPort _) (left_isPort _) (fun k => ?_)⟩
      rw [← h₁, ← h₂]
      exact hjoin k
    · have hc := forward_matches q (hgood j.succ) (hgood j.castSucc)
        (left_isPort j.succ) (right_isPort j.castSucc) (fun k => by
          rw [← h₂, ← h₁]
          exact (hjoin k).symm)
      exact (no_reverse j q ⟨hc.2, hc.1⟩).elim
  have step (j : Junction m) : (p j.succ).val = (p j.castSucc).val + 1 := by
    obtain ⟨q, h₁, h₂, _, _⟩ := hj j
    rw [h₁, h₂]
    rfl
  let first : Junction m := ⟨0, by omega⟩
  have beginning (i : Block m) (hi : i.val = 0) : (p i).val = 0 := by
    obtain ⟨q, h₁, _, h, _⟩ := hj first
    have he : first.castSucc = i := Fin.ext hi.symm
    rw [← he, h₁]
    change q.val = 0
    have h17 : rightPort q.castSucc = 17 := h.symm
    by_contra hn
    unfold rightPort at h17
    have hq : q.castSucc.val ≠ 0 := hn
    rw [ite_eq_right hq] at h17
    exact (by decide : (3 : Vertex) ≠ 17) h17
  have index (k : ℕ) : ∀ i : Block m, i.val = k → (p i).val = k := by
    induction k with
    | zero => exact beginning
    | succ k ih =>
      intro i hi
      have hl : HasLeft i := by omega
      let j := prev i hl
      have he : j.succ = i := prev_succ i hl
      have hv : j.castSucc.val = k := by
        change i.val - 1 = k
        omega
      rw [← he, step j, ih j.castSucc hv]
  let last : Junction m := ⟨m + 1, by omega⟩
  obtain ⟨q, _, h₂, _, h⟩ := hj last
  have hend : leftPort last.succ = 17 := ite_eq_left (show last.succ.val = m + 2 from rfl)
  have h17 : leftPort q.succ = 17 := h.symm.trans hend
  have hv : q.succ.val = n + 2 := by
    by_contra hn
    unfold leftPort at h17
    rw [ite_eq_right hn] at h17
    exact (by decide : (0 : Vertex) ≠ 17) h17
  have hh := index (m + 2) last.succ rfl
  rw [h₂, hv] at hh
  omega

private theorem path_nontrivial (n : ℕ) : IsFiniteNontrivial (pathGraph n) := by
  refine ⟨?_, ?_, ?_⟩
  · change Finite (Block n × Vertex)
    infer_instance
  · change Finite (PathEdge n)
    infer_instance
  · exact ⟨Sum.inr (⟨0, by omega⟩, 0)⟩

/-- **Samal's theorem: infinite antichains in the cycle-continuous order exist.** There is a
sequence $G_0, G_1, G_2, \dots$ of pairwise distinct finite multigraphs, each with at least one
edge, such that for all $i \ne j$ there is no cycle-continuous map from the edges of $G_i$ to
the edges of $G_j$.

Samal (Theorem 1.3) proves this with an infinite set of cubic bridgeless graphs that are
pairwise incomparable under cycle-continuous maps, answering the DeVos-Nesetril-Raspaud
antichain question positively.

Source: Robert Samal, Cycle-continuous
mappings - order structure, Journal of Graph Theory 85 (2017) 56-73, arXiv:1212.6909,
https://arxiv.org/abs/1212.6909. Moved from
`OpenConjectures/GraphTheory/CycleContinuousAntichain`.
-/
theorem conjecture_holds : conjecture := by
  refine ⟨pathGraph, path_nontrivial, ?_, ?_⟩
  · intro m n h
    have hid : ∃ f : (pathGraph m).E → (pathGraph n).E,
        IsCycleContinuous (pathGraph m) (pathGraph n) f := by
      rw [← h]
      exact ⟨id, fun _ hC => hC⟩
    obtain ⟨f, hf⟩ := hid
    exact map_path_length hf
  · rintro m n hn ⟨f, hf⟩
    exact hn (map_path_length hf)

end MathlibExt.GraphTheory.CycleContinuousAntichainWanted
