/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.Johnson.Basic
import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.Johnson.Basic
import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.Johnson.Construction
import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.Johnson.Augmentation
import CSLibExt.Algorithms.Lean.Graph.ShortestPath.Dijkstra
import Mathlib.Tactic.Ring

/-!
# Private weighted adapter for integer Johnson shortest paths

The one-time endpoint table attains the minimum over parallel edge occurrences. Stable buckets
preserve their order and multiplicity; weighted path refinement connects this actual adapter
to the canonical Bellman-Ford and Dijkstra specifications.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Johnson

open BellmanFord

private lemma vector_get_set {α : Type} {n : Nat} (values : Vector α n)
    (updated index : Fin n) (value : α) :
    (values.set updated.val value updated.isLt).get index =
      if updated = index then value else values.get index := by
  by_cases equality : updated = index
  · subst index
    simp only [↓reduceIte]
    change (values.set updated.val value updated.isLt)[updated.val] = value
    exact Vector.getElem_set_self updated.isLt
  · simp only [equality, ↓reduceIte]
    have unequal : updated.val ≠ index.val := by
      intro equal
      exact equality (Fin.ext equal)
    change (values.set updated.val value updated.isLt)[index.val] = values[index.val]
    exact Vector.getElem_set_ne updated.isLt index.isLt unequal

private lemma inserted_bucket {n : Nat} (prepared : Prepared n)
    (entry : Edge n × Edge (n + 1)) (source : Fin n) :
    (insertPrepared prepared entry).ret.buckets.get source =
      if entry.1.source = source then entry.1.target :: prepared.buckets.get source
      else prepared.buckets.get source := by
  by_cases source_eq : entry.1.source = source
  · subst source
    simp [insertPrepared, vector_get_set]
  · simp [insertPrepared, vector_get_set, source_eq]

private def minimumUpdate (cell : Option Nat) (weight : Nat) : Option Nat :=
  some (match cell with
    | none => weight
    | some value => min value weight)

private lemma inserted_cell {n : Nat} (prepared : Prepared n)
    (entry : Edge n × Edge (n + 1)) (source target : Fin n) :
    ((insertPrepared prepared entry).ret.minima.get source).get target =
      if entry.1.source = source ∧ entry.1.target = target then
        minimumUpdate ((prepared.minima.get source).get target) entry.2.weight.toNat
      else (prepared.minima.get source).get target := by
  by_cases source_eq : entry.1.source = source
  · subst source
    by_cases target_eq : entry.1.target = target
    · subst target
      simp only [insertPrepared, TimeM.ret_bind, TimeM.ret_pure,
        vector_get_set, ↓reduceIte, minimumUpdate]
      rfl
    · simp [insertPrepared, vector_get_set, target_eq]
  · simp [insertPrepared, vector_get_set, source_eq]

private def CellMinimum {n : Nat} (entries : List (Edge n × Edge (n + 1)))
    (source target : Fin n) (cell : Option Nat) : Prop :=
  match cell with
  | none => ∀ entry ∈ entries, entry.1.source = source → entry.1.target = target → False
  | some value =>
      (∃ entry ∈ entries, entry.1.source = source ∧ entry.1.target = target ∧
        entry.2.weight.toNat = value) ∧
      ∀ entry ∈ entries, entry.1.source = source → entry.1.target = target →
        value ≤ entry.2.weight.toNat

private lemma cellMinimum_insert {n : Nat} (entries : List (Edge n × Edge (n + 1)))
    (entry : Edge n × Edge (n + 1)) (source target : Fin n) (cell : Option Nat)
    (valid : CellMinimum entries source target cell) :
    CellMinimum (entries ++ [entry]) source target
      (if entry.1.source = source ∧ entry.1.target = target then
        minimumUpdate cell entry.2.weight.toNat
      else cell) := by
  by_cases endpoints : entry.1.source = source ∧ entry.1.target = target
  · simp only [endpoints]
    cases cell with
    | none =>
        simp only [minimumUpdate]
        refine ⟨⟨entry, by simp, endpoints.1, endpoints.2, rfl⟩, ?_⟩
        intro other member source_eq target_eq
        rcases List.mem_append.mp member with old | last
        · exact False.elim (valid other old source_eq target_eq)
        · have equal : other = entry := by simpa using last
          subst other
          exact le_rfl
    | some value =>
        simp only [minimumUpdate]
        obtain ⟨attained, lower⟩ := valid
        constructor
        · rcases le_total value entry.2.weight.toNat with before | after
          · obtain ⟨other, member, source_eq, target_eq, weight_eq⟩ := attained
            exact ⟨other, List.mem_append_left [entry] member, source_eq, target_eq,
              weight_eq.trans (min_eq_left before).symm⟩
          · exact ⟨entry, by simp, endpoints.1, endpoints.2, (min_eq_right after).symm⟩
        · intro other member source_eq target_eq
          rcases List.mem_append.mp member with old | last
          · exact (min_le_left _ _).trans (lower other old source_eq target_eq)
          · have equal : other = entry := by simpa using last
            subst other
            exact min_le_right _ _
  · simp only [endpoints, ↓reduceIte]
    cases cell with
    | none =>
        intro other member source_eq target_eq
        rcases List.mem_append.mp member with old | last
        · exact valid other old source_eq target_eq
        · have equal : other = entry := by simpa using last
          subst other
          exact endpoints ⟨source_eq, target_eq⟩
    | some value =>
        obtain ⟨attained, lower⟩ := valid
        constructor
        · obtain ⟨other, member, source_eq, target_eq, weight_eq⟩ := attained
          exact ⟨other, List.mem_append_left [entry] member, source_eq, target_eq, weight_eq⟩
        · intro other member source_eq target_eq
          rcases List.mem_append.mp member with old | last
          · exact lower other old source_eq target_eq
          · have equal : other = entry := by simpa using last
            subst other
            exact False.elim (endpoints ⟨source_eq, target_eq⟩)

private lemma empty_cell_minimum (n : Nat) (source target : Fin n) :
    CellMinimum [] source target (((emptyPrepared n).ret.minima.get source).get target) := by
  simp [emptyPrepared, buildVector_get, CellMinimum]

private lemma inserted_entries_minimum {n : Nat} (entries : List (Edge n × Edge (n + 1)))
    (processed : List (Edge n × Edge (n + 1))) (prepared : Prepared n)
    (valid : ∀ source target,
      CellMinimum processed source target ((prepared.minima.get source).get target)) :
    ∀ source target, CellMinimum (processed ++ entries) source target
      (((insertEntries entries prepared).ret.minima.get source).get target) := by
  induction entries generalizing processed prepared with
  | nil => simpa [insertEntries] using valid
  | cons entry rest induction =>
      have next_valid : ∀ source target, CellMinimum (processed ++ [entry]) source target
          (((insertPrepared prepared entry).ret.minima.get source).get target) := by
        intro source target
        rw [inserted_cell]
        exact cellMinimum_insert processed entry source target _ (valid source target)
      have next := induction (processed ++ [entry]) (insertPrepared prepared entry).ret next_valid
      simpa [insertEntries, List.append_assoc] using next

private lemma all_entries_minimum {n : Nat} (entries : List (Edge n × Edge (n + 1)))
    (source target : Fin n) :
    CellMinimum entries source target
      (((insertEntries entries (emptyPrepared n).ret).ret.minima.get source).get target) := by
  simpa using inserted_entries_minimum entries [] (emptyPrepared n).ret
    (empty_cell_minimum n) source target

private def occurrenceTargets {n : Nat} (entries : List (Edge n × Edge (n + 1)))
    (source : Fin n) : List (Fin n) :=
  (entries.filter (fun entry => decide (entry.1.source = source))).map
    (fun entry => entry.1.target)

private lemma empty_bucket (n : Nat) (source : Fin n) :
    (emptyPrepared n).ret.buckets.get source = [] := by
  simp [emptyPrepared, buildVector_get]

private lemma reverseBucket_ret {n : Nat} (vertices accumulator : List (Fin n)) :
    (reverseBucket vertices accumulator).ret = vertices.reverse ++ accumulator := by
  induction vertices generalizing accumulator with
  | nil => rfl
  | cons vertex rest induction =>
      simp [reverseBucket, induction, List.reverse_cons, List.append_assoc]

private lemma inserted_entries_buckets_reverse {n : Nat}
    (entries : List (Edge n × Edge (n + 1))) (prepared : Prepared n) (source : Fin n) :
    ((insertEntries entries prepared).ret.buckets.get source).reverse =
      (prepared.buckets.get source).reverse ++ occurrenceTargets entries source := by
  induction entries generalizing prepared with
  | nil => simp [insertEntries, occurrenceTargets]
  | cons entry rest induction =>
      simp only [insertEntries, TimeM.ret_bind]
      rw [induction, inserted_bucket]
      by_cases source_eq : entry.1.source = source
      · simp [source_eq, occurrenceTargets, List.reverse_cons, List.append_assoc]
      · simp [source_eq, occurrenceTargets]

private lemma prepare_bucket {n : Nat} (edges : List (Edge n))
    (reweighted : List (Edge (n + 1))) (source : Fin n) :
    (prepare edges reweighted).ret.buckets.get source =
      occurrenceTargets (edges.zip reweighted) source := by
  simp [prepare, buildVector_get, reverseBucket_ret, inserted_entries_buckets_reverse, empty_bucket]

private lemma prepare_cell_minimum {n : Nat} (edges : List (Edge n))
    (reweighted : List (Edge (n + 1))) (source target : Fin n) :
    CellMinimum (edges.zip reweighted) source target
      (((prepare edges reweighted).ret.minima.get source).get target) := by
  simpa [prepare] using all_entries_minimum (edges.zip reweighted) source target

private def shiftedEdge {n : Nat} (potential : Vector Int n) (edge : Edge n) : Edge n :=
  ⟨edge.source, edge.target,
    edge.weight + potential.get edge.source - potential.get edge.target⟩

private lemma reweightEdges_ret {n : Nat} (potential : Vector Int n) (edges : List (Edge n)) :
    (reweightEdges potential edges).ret = edges.map (shiftedEdge potential) := by
  induction edges with
  | nil => rfl
  | cons edge rest induction => simp [reweightEdges, shiftedEdge, induction]

private lemma shifted_path {n : Nat} (potential : Vector Int n) {edges : List (Edge n)}
    {source target : Fin n} {path : List (Edge n)}
    (valid : IsWeightedPath edges source target path) :
    IsWeightedPath (edges.map (shiftedEdge potential)) source target
      (path.map (shiftedEdge potential)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro edge member
    obtain ⟨original, original_mem, rfl⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨original, valid.1 original original_mem, rfl⟩
  · simpa only [List.isChain_map, shiftedEdge] using valid.2.1
  · cases path with
    | nil => exact valid.2.2
    | cons first rest =>
        refine ⟨valid.2.2.1, ?_⟩
        change ((first :: rest).map (shiftedEdge potential)).getLast?.map Edge.target = some target
        rw [List.getLast?_map, Option.map_map]
        simpa only [Function.comp_def, shiftedEdge] using valid.2.2.2

private lemma shifted_path_weight {n : Nat} (potential : Vector Int n)
    {edges : List (Edge n)} {source target : Fin n} {path : List (Edge n)}
    (valid : IsWeightedPath edges source target path) :
    pathWeight (path.map (shiftedEdge potential)) =
      pathWeight path + potential.get source - potential.get target := by
  induction path generalizing source with
  | nil =>
      have endpoints : source = target := valid.2.2
      simp [pathWeight, endpoints]
  | cons first rest induction =>
      change (first.weight + potential.get first.source - potential.get first.target) +
        pathWeight (rest.map (shiftedEdge potential)) =
          first.weight + pathWeight rest + potential.get source - potential.get target
      rw [induction (isWeightedPath_tail valid), valid.2.2.1]
      ring

private lemma shifted_cycle_weight {n : Nat} (potential : Vector Int n)
    {edges : List (Edge n)} {base : Fin n} {cycle : List (Edge n)}
    (valid : IsWeightedPath edges base base cycle) :
    pathWeight (cycle.map (shiftedEdge potential)) = pathWeight cycle := by
  simpa using shifted_path_weight potential valid

private lemma zip_self_map_append {α β : Type} (entries : List α) (weight : α → β)
    (tail : List β) :
    entries.zip (entries.map weight ++ tail) =
      entries.map (fun entry => (entry, weight entry)) := by
  have expanded := List.zip_append (l₁ := entries) (r₁ := [])
    (l₂ := entries.map weight) (r₂ := tail) (by simp)
  simpa [← List.map_prod_left_eq_zip] using expanded

private lemma zip_reweighted_augment {n : Nat} (edges : List (Edge n))
    (potential : Vector Int (n + 1)) :
    edges.zip (reweightEdges potential (augment edges).ret).ret =
      edges.map (fun edge => (edge, shiftedEdge potential (liftEdge edge))) := by
  simp [reweightEdges_ret, augment_ret, List.map_append, List.map_map, zip_self_map_append]

private def reweightedInput {n : Nat} (potential : Vector Int (n + 1)) (edge : Edge n) : Nat :=
  (shiftedEdge potential (liftEdge edge)).weight.toNat

private lemma prepare_edge_iff {n : Nat} (edges : List (Edge n))
    (potential : Vector Int (n + 1)) (source target : Fin n) :
    (prepare edges (reweightEdges potential (augment edges).ret).ret).ret.graph.Edge source target ↔
      ∃ edge ∈ edges, edge.source = source ∧ edge.target = target := by
  simp [Prepared.graph, DirectedAdjacency.Edge, prepare_bucket, occurrenceTargets,
    zip_reweighted_augment, and_assoc]

private lemma prepare_reachable_iff {n : Nat} (edges : List (Edge n))
    (potential : Vector Int (n + 1)) (source target : Fin n) :
    (prepare edges (reweightEdges potential (augment edges).ret).ret).ret.graph.Reachable
        source target ↔ (toDirectedAdjacency edges).Reachable source target := by
  apply DirectedAdjacency.SemanticallyEquivalent.reachable_iff
  intro first last
  exact (prepare_edge_iff edges potential first last).trans edge_toDirectedAdjacency_iff.symm

private lemma prepare_minimum {n : Nat} (edges : List (Edge n))
    (potential : Vector Int (n + 1)) (source target : Fin n) :
    let prepared := (prepare edges (reweightEdges potential (augment edges).ret).ret).ret
    prepared.graph.Edge source target →
      (∃ edge ∈ edges, edge.source = source ∧ edge.target = target ∧
        reweightedInput potential edge = prepared.weight source target) ∧
      ∀ edge ∈ edges, edge.source = source → edge.target = target →
        prepared.weight source target ≤ reweightedInput potential edge := by
  let prepared := (prepare edges (reweightEdges potential (augment edges).ret).ret).ret
  change prepared.graph.Edge source target → _
  intro adjacent
  have minimum := prepare_cell_minimum edges
    (reweightEdges potential (augment edges).ret).ret source target
  rw [zip_reweighted_augment] at minimum
  change CellMinimum (edges.map (fun edge => (edge, shiftedEdge potential (liftEdge edge))))
    source target ((prepared.minima.get source).get target) at minimum
  cases cell_eq : (prepared.minima.get source).get target with
  | none =>
      rw [cell_eq] at minimum
      obtain ⟨edge, member, source_eq, target_eq⟩ :=
        (prepare_edge_iff edges potential source target).mp adjacent
      exact False.elim (minimum (edge, shiftedEdge potential (liftEdge edge))
        (List.mem_map.mpr ⟨edge, member, rfl⟩) source_eq target_eq)
  | some value =>
      rw [cell_eq] at minimum
      obtain ⟨attained, lower⟩ := minimum
      have weight_eq : prepared.weight source target = value := by
        simp [Prepared.weight, cell_eq]
      constructor
      · obtain ⟨entry, entry_mem, source_eq, target_eq, entry_weight⟩ := attained
        obtain ⟨edge, edge_mem, rfl⟩ := List.mem_map.mp entry_mem
        exact ⟨edge, edge_mem, source_eq, target_eq, entry_weight.trans weight_eq.symm⟩
      · intro edge edge_mem source_eq target_eq
        change prepared.weight source target ≤ reweightedInput potential edge
        rw [weight_eq]
        exact lower (edge, shiftedEdge potential (liftEdge edge))
          (List.mem_map.mpr ⟨edge, edge_mem, rfl⟩) source_eq target_eq

private lemma vertex_path_cons {n : Nat} (prepared : Prepared n)
    {source next target : Fin n} {distance : Nat} (adjacent : prepared.graph.Edge source next)
    (valid : DirectedAdjacency.HasPathWeight prepared.graph prepared.weight next target distance) :
    DirectedAdjacency.HasPathWeight prepared.graph prepared.weight source target
      (prepared.weight source next + distance) := by
  obtain ⟨vertices, chain, weight_eq⟩ := valid
  refine ⟨source :: vertices, chain.cons adjacent, ?_⟩
  cases vertices with
  | nil => exact False.elim (chain.ne_nil rfl)
  | cons first rest =>
      change prepared.weight source first + DirectedAdjacency.pathWeight prepared.weight
        (first :: rest) = prepared.weight source next + distance
      have head_eq : first = next := chain.head_eq
      rw [weight_eq, head_eq]

private lemma reweightedInput_cast {n : Nat} (potential : Vector Int (n + 1))
    (edge : Edge n) (nonnegative : 0 ≤ (shiftedEdge potential (liftEdge edge)).weight) :
    (reweightedInput potential edge : Int) = edge.weight +
      potential.get edge.source.castSucc - potential.get edge.target.castSucc := by
  exact Int.toNat_of_nonneg nonnegative

private lemma prepared_path_of_weighted {n : Nat} (edges : List (Edge n))
    (potential : Vector Int (n + 1))
    (nonnegative : ∀ edge ∈ edges, 0 ≤ (shiftedEdge potential (liftEdge edge)).weight)
    {source target : Fin n} {path : List (Edge n)}
    (valid : IsWeightedPath edges source target path) :
    let prepared := (prepare edges (reweightEdges potential (augment edges).ret).ret).ret
    ∃ distance, DirectedAdjacency.HasPathWeight prepared.graph prepared.weight
      source target distance ∧ (distance : Int) ≤ pathWeight path +
        potential.get source.castSucc - potential.get target.castSucc := by
  let prepared := (prepare edges (reweightEdges potential (augment edges).ret).ret).ret
  change ∃ distance, DirectedAdjacency.HasPathWeight prepared.graph prepared.weight
    source target distance ∧ _
  induction path generalizing source with
  | nil =>
      have endpoints : source = target := valid.2.2
      subst target
      exact ⟨0, ⟨[source], List.isChainFromTo_singleton, rfl⟩, by simp [pathWeight]⟩
  | cons first rest induction =>
      obtain ⟨distance, tail, bound⟩ := induction (isWeightedPath_tail valid)
      have edge_mem : first ∈ edges := valid.1 first (by simp)
      have adjacent : prepared.graph.Edge source first.target := by
        exact (prepare_edge_iff edges potential source first.target).mpr
          ⟨first, edge_mem, valid.2.2.1, rfl⟩
      refine ⟨prepared.weight source first.target + distance,
        vertex_path_cons prepared adjacent tail, ?_⟩
      have lower := (prepare_minimum edges potential source first.target adjacent).2
        first edge_mem valid.2.2.1 rfl
      change prepared.weight source first.target ≤ reweightedInput potential first at lower
      have cast_eq := reweightedInput_cast potential first (nonnegative first edge_mem)
      change (_ : Int) ≤ first.weight + pathWeight rest +
        potential.get source.castSucc - potential.get target.castSucc
      have source_cast : first.source.castSucc = source.castSucc :=
        congrArg Fin.castSucc valid.2.2.1
      rw [source_cast] at cast_eq
      omega

private lemma weighted_path_of_prepared {n : Nat} (edges : List (Edge n))
    (potential : Vector Int (n + 1))
    (nonnegative : ∀ edge ∈ edges, 0 ≤ (shiftedEdge potential (liftEdge edge)).weight)
    {source target : Fin n} {distance : Nat}
    (valid : DirectedAdjacency.HasPathWeight
      (prepare edges (reweightEdges potential (augment edges).ret).ret).ret.graph
      (prepare edges (reweightEdges potential (augment edges).ret).ret).ret.weight
      source target distance) :
    ∃ path, IsWeightedPath edges source target path ∧
      pathWeight path + potential.get source.castSucc - potential.get target.castSucc =
        (distance : Int) := by
  let prepared := (prepare edges (reweightEdges potential (augment edges).ret).ret).ret
  change DirectedAdjacency.HasPathWeight prepared.graph prepared.weight source target distance
    at valid
  obtain ⟨vertices, chain, weight_eq⟩ := valid
  induction chain using List.IsChainFromTo.head_induction_on generalizing distance with
  | h_refl =>
      refine ⟨[], by simp [IsWeightedPath], ?_⟩
      have zero : distance = 0 := weight_eq.symm
      simp [pathWeight, zero]
  | @h_head first second last tail adjacent chainTail induction =>
      obtain ⟨path, path_valid, path_weight⟩ := induction rfl
      obtain ⟨edge, member, edge_source, edge_target, edge_weight⟩ :=
        (prepare_minimum edges potential first second adjacent).1
      change reweightedInput potential edge = prepared.weight first second at edge_weight
      refine ⟨edge :: path, weightedPath_cons member edge_source
        (edge_target.symm ▸ path_valid), ?_⟩
      have cast_eq := reweightedInput_cast potential edge (nonnegative edge member)
      rw [edge_source, edge_target, edge_weight] at cast_eq
      have vertex_weight : distance = prepared.weight first second +
          DirectedAdjacency.pathWeight prepared.weight tail := by
        rw [← weight_eq]
        cases tail with
        | nil => exact False.elim (chainTail.ne_nil rfl)
        | cons next rest =>
            change prepared.weight first next + _ = prepared.weight first second + _
            have head_eq : next = second := chainTail.head_eq
            rw [head_eq]
      change edge.weight + pathWeight path + potential.get first.castSucc -
        potential.get last.castSucc = (distance : Int)
      rw [vertex_weight]
      push_cast
      omega

end Cslib.Algorithms.Lean.Johnson
