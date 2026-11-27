/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Parameterized.HardnessEncoding
public import CSLibExt.Computability.Complexity.PolynomialEncoding.Represented
import CSLibExt.Computability.Complexity.Parameterized.Identity

/-!
# Polynomial-time serialization of an explicit graph

Number a list of vertices in order, test the supplied adjacency predicate on
each ordered pair, and emit the accepted binary index pairs. This construction
allows the list to contain several representatives of the same graph vertex.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized.GraphWriter

open MetaMathlibExt BitstringEncoding ComplexityTheory
open Cslib.Complexity.PolynomialEncoding.BitScan
open Cslib.Complexity.PolynomialEncoding.Comprehension

local notation "Word" => List Bool

/-- All adjacent ordered pairs, labeled by their positions in the vertex list. -/
def edges {V : Type} (vs : List V) (adj : V → V → Bool) : List (ℕ × ℕ) :=
  vs.zipIdx.flatMap fun p => (vs.zipIdx.filter fun q => adj p.1 q.1).map fun q => (p.2, q.2)

/-- Encode edges in row order, using the position of each vertex as its name. -/
def writeGraph {V : Type} (vs : List V) (adj : V → V → Bool) :=
  bitEncode (vs.length, edges vs adj)

private theorem edgeBytes {V : Type} (vs : List V) (adj : V → V → Bool) :
    bitEncode (edges vs adj) =
      vs.zipIdx.flatMap fun p => vs.zipIdx.flatMap fun q =>
        if adj p.1 q.1 then delimit (pack (bitEncode p.2) (bitEncode q.2)) else [] := by
  rw [← frames_encode]
  simp only [frames, edges, List.map_flatMap, List.flatMap_assoc, List.map_map]
  apply List.flatMap_congr
  intro p _
  rw [List.flatMap_map]
  generalize vs.zipIdx = xs
  change ((xs.filter fun q => adj p.1 q.1).flatMap
    (fun q => delimit (pack (bitEncode p.2) (bitEncode q.2)))) = _
  induction xs with
  | nil => rfl
  | cons q qs ih =>
    cases h : adj p.1 q.1 <;> simp only [List.filter_cons, h, Bool.false_eq_true,
      ↓reduceIte, List.flatMap_cons, ih, List.nil_append]

/-- If listing the vertices and testing adjacency have polynomial-time
implementations, so does writing the complete serialized graph. -/
theorem represented_writeGraph {α V : Type} {e : α → Word} {r : V → Word}
    {vs : α → List V} {adj : α → V → V → Bool}
    (vertices : Represented e (fun a => frames r (vs a)))
    (neighbors : Represented (pair r (pair r e)) (fun p => [adj p.2.2 p.2.1 p.1])) :
    Represented e (fun a => writeGraph (vs a) (adj a)) := by
  let nr := Represented.numbered r
  let ctx := pair nr e
  let cell := pair nr ctx
  have payload : Represented nr (fun v => r v.1) :=
    ((Represented.input nr).after (polyField false true)).transport (fun p => by
      simp [nr, Represented.numbered, pack, field_delimit])
  have index : Represented nr (fun v => bitEncode v.2) :=
    ((Represented.input nr).after ((polyField true false).comp isPolyTime_encodeLength)).transport
      (fun p => by simp [nr, Represented.numbered, pack, field_delimit])
  have decoded := (payload.fst ctx).packed
    (((payload.fst e).snd nr).packed (((Represented.input e).snd nr).snd nr))
  obtain ⟨decideEdge, ht, he⟩ := neighbors
  have good : Represented cell (fun p => [adj p.2.2 p.2.1.1 p.1.1]) :=
    (decoded.after ht).transport (fun p => he (p.1.1, (p.2.1.1, p.2.2)))
  have emitEdge := (((index.fst e).snd nr).packed (index.fst ctx)).frame
  have matrix := vertices.enumerate.flatMap
    ((vertices.enumerate.snd nr).flatMap (good.cond emitEdge (Represented.const cell [])))
  have size := (vertices.count.after isPolyTime_encodeLength).transport
    (g := fun a => bitEncode (vs a).length) (fun _ => by simp)
  apply (size.packed matrix).transport
  intro a
  change pack _ _ = pack _ (bitEncode (edges (vs a) (adj a)))
  rw [edgeBytes]

private theorem zipIdx_fin {V : Type} (vs : List V) :
    vs.zipIdx = (List.finRange vs.length).map (fun i => (vs.get i, i.val)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [List.get_eq_getElem]

private theorem writeGraph_eq {A V : Type} (vs : List A) (G : SimpleGraph V)
    [DecidableRel G.Adj] (f : A → V) :
    writeGraph vs (fun a b => decide (G.Adj (f a) (f b))) =
      encodeNumberedGraph (G.comap (f ∘ vs.get)) (Equiv.refl _) := by
  unfold writeGraph encodeNumberedGraph
  congr 2
  simp only [edges, numberedEdges, zipIdx_fin, List.flatMap_map, List.filter_map,
    List.map_map, Function.comp_def, Equiv.refl_apply]
  rfl

private theorem comap_clique_iff {I V : Type*} (G : SimpleGraph V) (f : I → V)
    (cover : Function.Surjective f) (k : ℕ) :
    (∃ s, (G.comap f).IsNClique k s) ↔ ∃ s, G.IsNClique k s := by
  classical
  constructor
  · rintro ⟨s, hs⟩
    have inj : Set.InjOn f s := by
      intro i hi j hj he
      by_contra h
      have edge : G.Adj (f i) (f j) := hs.isClique hi hj h
      exact G.loopless.irrefl _ (he ▸ edge)
    refine ⟨s.image f, ?_, (Finset.card_image_of_injOn inj).trans hs.card_eq⟩
    intro u hu v hv hne
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
    exact hs.isClique hi hj (fun h => hne (congrArg f h))
  · rintro ⟨s, hs⟩
    choose g right using cover
    let emb : V ↪ I := ⟨g, fun _ _ h => by simpa only [right] using congrArg f h⟩
    refine ⟨s.map emb, ?_, by simpa using hs.card_eq⟩
    intro i hi j hj hne
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hj
    change G.Adj (f (g u)) (f (g v))
    rw [right, right]
    exact hs.isClique hu hv (fun h => hne (congrArg emb h))

/-- Reading a graph with an explicitly listed vertex set is equivalent to
choosing positions in that list. -/
theorem writeGraph_iff_indices {V : Type} (vs : List V) (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) :
    CliqueParam (writeGraph vs fun x y => decide (G.Adj x y)) k ↔
      ∃ s, (G.comap vs.get).IsNClique k s := by
  have he := writeGraph_eq vs G id
  simp only [id_eq, Function.id_comp] at he
  rw [he, cliqueParam_encodeNumberedGraph_iff]

/-- A clique as large as the number of colors in a proper coloring chooses
one vertex of each color. -/
theorem clique_iff_choice {I V : Type*} [Fintype I] (G : SimpleGraph V) (color : V → I)
    (proper : ∀ ⦃x y⦄, G.Adj x y → color x ≠ color y) :
    (∃ s, G.IsNClique (Fintype.card I) s) ↔
      ∃ f : I → V, (∀ i, color (f i) = i) ∧ ∀ i j, i ≠ j → G.Adj (f i) (f j) := by
  classical
  constructor
  · rintro ⟨s, hs⟩
    let c : s → I := fun i => color i.val
    have hinj : Function.Injective c := by
      intro i j h
      by_contra ne
      exact proper (hs.isClique i.property j.property (fun e => ne (Subtype.ext e))) h
    have bij := (Fintype.bijective_iff_injective_and_card c).mpr
      ⟨hinj, by simpa using hs.card_eq⟩
    let inv := Equiv.ofBijective c bij
    refine ⟨fun i => (inv.symm i).val, inv.apply_symm_apply, fun i j hij => ?_⟩
    exact hs.isClique (inv.symm i).property (inv.symm j).property
      (fun h => hij (inv.symm.injective (Subtype.ext h)))
  · rintro ⟨f, color_f, compatible⟩
    let emb : I ↪ V := ⟨f, fun _ _ h => by simpa only [color_f] using congrArg color h⟩
    refine ⟨Finset.univ.map emb, ?_, by simp⟩
    intro u hu v hv huv
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hv
    exact compatible i j (fun h => huv (congrArg emb h))

/-- A surjective vertex listing preserves all clique queries, including the
one-vertex and empty-clique queries, even if rows are repeated. -/
theorem writeGraph_correct {A V : Type} (vs : List A) (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : A → V) (cover : Function.Surjective (f ∘ vs.get)) (k : ℕ) :
    CliqueParam (writeGraph vs fun a b => decide (G.Adj (f a) (f b))) k ↔
      ∃ s, G.IsNClique k s := by
  rw [writeGraph_eq, cliqueParam_encodeNumberedGraph_iff]
  exact comap_clique_iff G _ cover k

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized.GraphWriter
