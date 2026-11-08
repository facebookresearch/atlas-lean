/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Graph.ShortestPath.BellmanFord
import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.Johnson.Basic
import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.Johnson.Construction

/-!
# Private fresh-source augmentation facts for Johnson shortest paths

The actual augmented edge list preserves each old occurrence and adds zero edges from
the fresh source. Canonical weighted paths lift and project with unchanged weights;
the augmented graph has a reachable negative cycle exactly when the original graph
has one at some source, including when the original vertex set is empty.

Lean proof author: Codex, explicitly authorized by Adam Kiezun.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Johnson

open BellmanFord

private lemma augment_lift_mem {n : Nat} {edges : List (Edge n)}
    {edge : Edge n} (mem : edge ∈ edges) : liftEdge edge ∈ (augment edges).ret := by
  simp only [augment_ret, List.mem_append, List.mem_map]
  exact Or.inl ⟨edge, mem, rfl⟩

private lemma augment_source_mem {n : Nat} (edges : List (Edge n)) (vertex : Fin n) :
    (⟨Fin.last n, vertex.castSucc, 0⟩ : Edge (n + 1)) ∈ (augment edges).ret := by
  rw [augment_ret]
  exact List.mem_append_right _ (List.mem_map.mpr ⟨vertex, List.mem_finRange vertex, rfl⟩)

private lemma augmented_target_ne_last {n : Nat} {edges : List (Edge n)}
    {edge : Edge (n + 1)} (mem : edge ∈ (augment edges).ret) :
    edge.target ≠ Fin.last n := by
  rw [augment_ret] at mem
  rcases List.mem_append.mp mem with lifted | zero
  · obtain ⟨old, _, rfl⟩ := List.mem_map.mp lifted
    exact Fin.castSucc_ne_last old.target
  · obtain ⟨vertex, _, rfl⟩ := List.mem_map.mp zero
    exact Fin.castSucc_ne_last vertex

private lemma augment_reachable {n : Nat} (edges : List (Edge n)) (vertex : Fin (n + 1)) :
    (toDirectedAdjacency (augment edges).ret).Reachable (Fin.last n) vertex := by
  refine Fin.lastCases ?_ (fun old => ?_) vertex
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single
      (edge_toDirectedAdjacency_iff.mpr ⟨_, augment_source_mem edges old, rfl, rfl⟩)

private lemma lift_path {n : Nat} {edges : List (Edge n)} {source target : Fin n}
    {path : List (Edge n)} (valid : IsWeightedPath edges source target path) :
    IsWeightedPath (augment edges).ret source.castSucc target.castSucc
      (path.map liftEdge) := by
  refine ⟨?_, ?_, ?_⟩
  · intro edge mem
    obtain ⟨old, old_mem, rfl⟩ := List.mem_map.mp mem
    exact augment_lift_mem (valid.1 old old_mem)
  · simpa only [List.isChain_map, liftEdge, Fin.castSucc_inj] using valid.2.1
  · cases path with
    | nil => exact congrArg Fin.castSucc valid.2.2
    | cons first rest =>
      refine ⟨congrArg Fin.castSucc valid.2.2.1, ?_⟩
      change Option.map Edge.target ((first :: rest).map liftEdge).getLast? =
        some target.castSucc
      rw [List.getLast?_map, Option.map_map]
      simpa only [Option.map_map, Option.map_some, Function.comp_def, liftEdge]
        using congrArg (Option.map Fin.castSucc) valid.2.2.2

private lemma lift_pathWeight {n : Nat} (path : List (Edge n)) :
    pathWeight (path.map liftEdge) = pathWeight path := by
  simp only [pathWeight, List.map_map]
  rfl

private lemma weightedPath_cons {n : Nat} {edges : List (Edge n)}
    {source target : Fin n} {first : Edge n} {rest : List (Edge n)}
    (first_mem : first ∈ edges) (first_source : first.source = source)
    (rest_valid : IsWeightedPath edges first.target target rest) :
    IsWeightedPath edges source target (first :: rest) := by
  cases rest <;> simp_all [IsWeightedPath]

private lemma project_path {n : Nat} {edges : List (Edge n)} {source target : Fin n}
    {path : List (Edge (n + 1))}
    (valid : IsWeightedPath (augment edges).ret source.castSucc target.castSucc path) :
    ∃ original, IsWeightedPath edges source target original ∧ original.map liftEdge = path := by
  induction path generalizing source with
  | nil =>
    exact ⟨[], by simpa only [IsWeightedPath, List.not_mem_nil, false_implies,
      implies_true, List.isChain_nil, true_and, Fin.castSucc_inj] using valid, rfl⟩
  | cons first rest induction =>
    have first_mem := valid.1 first (by simp)
    rw [augment_ret] at first_mem
    rcases List.mem_append.mp first_mem with lifted | zero
    · obtain ⟨old, old_mem, old_eq⟩ := List.mem_map.mp lifted
      subst first
      have old_source : old.source = source := Fin.castSucc_inj.mp valid.2.2.1
      obtain ⟨original, original_valid, original_eq⟩ :=
        induction (isWeightedPath_tail valid)
      exact ⟨old :: original, weightedPath_cons old_mem old_source original_valid,
        by simp only [List.map_cons, original_eq]⟩
    · obtain ⟨vertex, _, zero_eq⟩ := List.mem_map.mp zero
      subst first
      exact False.elim (Fin.castSucc_ne_last source valid.2.2.1.symm)

private lemma closed_path_base_ne_last {n : Nat} {edges : List (Edge n)}
    {base : Fin (n + 1)} {path : List (Edge (n + 1))}
    (valid : IsWeightedPath (augment edges).ret base base path) (nonempty : path ≠ []) :
    base ≠ Fin.last n := by
  cases path with
  | nil => exact (nonempty rfl).elim
  | cons first rest =>
    obtain ⟨last, last_eq, target_eq⟩ := Option.map_eq_some_iff.mp valid.2.2.2
    obtain ⟨initial, path_eq⟩ := List.getLast?_eq_some_iff.mp last_eq
    have last_mem : last ∈ first :: rest := by rw [path_eq]; simp
    simpa only [target_eq] using augmented_target_ne_last (valid.1 last last_mem)

private lemma exists_old_of_ne_last {n : Nat} (vertex : Fin (n + 1))
    (different : vertex ≠ Fin.last n) : ∃ old : Fin n, old.castSucc = vertex := by
  refine Fin.lastCases (motive := fun vertex =>
    vertex ≠ Fin.last n → ∃ old : Fin n, old.castSucc = vertex) ?_ ?_ vertex different
  · intro impossible
    exact (impossible rfl).elim
  · intro old _
    exact ⟨old, rfl⟩

private lemma fresh_negativeCycle_iff {n : Nat} (edges : List (Edge n)) :
    HasReachableNegativeCycle (augment edges).ret (Fin.last n) ↔
      ∃ source : Fin n, HasReachableNegativeCycle edges source := by
  constructor
  · rintro ⟨witness⟩
    obtain ⟨base, base_eq⟩ := exists_old_of_ne_last witness.base
      (closed_path_base_ne_last witness.cycle_valid witness.cycle_nonempty)
    have valid : IsWeightedPath (augment edges).ret base.castSucc base.castSucc
        witness.cycle := by simpa only [base_eq] using witness.cycle_valid
    obtain ⟨original, original_valid, original_eq⟩ := project_path valid
    refine ⟨base, ⟨{
      base := base
      «prefix» := []
      cycle := original
      prefix_valid := by simp [IsWeightedPath]
      prefix_simple := by simp [pathVertices]
      cycle_valid := original_valid
      cycle_nonempty := ?_
      cycle_simple := ?_
      cycle_negative := ?_ }⟩⟩
    · intro empty
      apply witness.cycle_nonempty
      simpa only [empty, List.map_nil] using original_eq.symm
    · apply List.Nodup.of_map Fin.castSucc
      have mapped : (original.map Edge.source).map Fin.castSucc =
          witness.cycle.map Edge.source := by
        rw [← original_eq, List.map_map, List.map_map]
        rfl
      exact mapped ▸ witness.cycle_simple
    · rw [← lift_pathWeight original, original_eq]
      exact witness.cycle_negative
  · rintro ⟨source, ⟨witness⟩⟩
    refine ⟨{
      base := witness.base.castSucc
      «prefix» := [⟨Fin.last n, witness.base.castSucc, 0⟩]
      cycle := witness.cycle.map liftEdge
      prefix_valid := ?_
      prefix_simple := ?_
      cycle_valid := lift_path witness.cycle_valid
      cycle_nonempty := ?_
      cycle_simple := ?_
      cycle_negative := ?_ }⟩
    · simpa [IsWeightedPath] using augment_source_mem edges witness.base
    · simp [pathVertices, (Fin.castSucc_ne_last witness.base).symm]
    · intro empty
      exact witness.cycle_nonempty (List.map_eq_nil_iff.mp empty)
    · have mapped : (witness.cycle.map liftEdge).map Edge.source =
          (witness.cycle.map Edge.source).map Fin.castSucc := by
        rw [List.map_map, List.map_map]
        rfl
      rw [mapped]
      exact witness.cycle_simple.map (Fin.castSucc_injective n)
    · simpa only [lift_pathWeight] using witness.cycle_negative

end Cslib.Algorithms.Lean.Johnson
