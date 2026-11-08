/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Stefan Trandafir
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.AlgebraicGraphTheory.Homomorphisms
public import Mathlib.Tactic.FinCases

@[expose] public section

open SimpleGraph

namespace MathlibExtTest.Combinatorics.SimpleGraph.AlgebraicGraphTheory.Homomorphisms

open MetaMathlibExt

-- Combinatorics 2: Retract

-- Sanity check: the triangle K_3 is a retraction of K_4 minus an edge

abbrev K4_minus_edge : SimpleGraph (Fin 4) :=
  (completeGraph (Fin 4)).deleteEdges {s((2 : Fin 4), (3 : Fin 4))}
/-- The triangle induced on vertices {0, 1, 2} (the deleted edge touches
    3 ∉ {0,1,2}, so all three pairs among {0,1,2} stay adjacent). -/

abbrev K3_as_induced : K4_minus_edge.Subgraph :=
  (⊤ : K4_minus_edge.Subgraph).induce {0, 1, 2}

def retractToTriFun (v : Fin 4) : K3_as_induced.verts :=
  if hv : v = 3 then ⟨2, by simp [K3_as_induced, Subgraph.induce_verts]⟩
  else ⟨v, by
    fin_cases v
    · simp [K3_as_induced, Subgraph.induce_verts]
    · simp [K3_as_induced, Subgraph.induce_verts]
    · simp [K3_as_induced, Subgraph.induce_verts]
    · exact (hv rfl).elim⟩

/-- The explicit homomorphism from K4 minus an edge to K3. -/

def retractToTri : K4_minus_edge →g K3_as_induced.coe where
  toFun := retractToTriFun
  map_rel' := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [retractToTriFun, K3_as_induced,
      Subgraph.coe_adj, Subgraph.induce_adj,
      Subgraph.top_adj, K4_minus_edge, deleteEdges_adj, top_adj]

example : K3_as_induced.IsRetract := by
  refine ⟨retractToTri, fun h => ?_⟩
  obtain ⟨v, hv⟩ := h
  have hv3 : v ≠ 3 := by
    rintro rfl
    simp [K3_as_induced, Subgraph.induce_verts] at hv
  have hval : (retractToTri v).val = v := by
    show (retractToTriFun v).val = v
    simp [retractToTriFun, hv3]
  exact Subtype.ext hval

-- Combinatorics 20: Core/has core

abbrev K₂ := completeBipartiteGraph (Fin 1) (Fin 1)

abbrev K₂₂ := completeBipartiteGraph (Fin 2) (Fin 2)

-- Proving that K2 is a core.

theorem K2_isCore : K₂.IsCore := by
  intro f
  apply Finite.injective_iff_bijective.mp
  intro a b hab
  by_contra hne
  have hadj : K₂.Adj a b := by
    match a, b with
    | Sum.inl _, Sum.inr _ => simp [K₂]
    | Sum.inr _, Sum.inl _ => simp [K₂]
    | Sum.inl x, Sum.inl y =>
      exfalso
      -- hne : ¬ inl x = inl y, not ¬ x = y, so lift first
      exact hne (congrArg Sum.inl (Subsingleton.elim x y))
    | Sum.inr x, Sum.inr y =>
      exfalso
      exact hne (congrArg Sum.inr (Subsingleton.elim x y))
  have hmap := f.map_rel' hadj
  have hab' : f.toFun a = f.toFun b := hab
  rw [hab'] at hmap
  exact K₂.irrefl hmap

/-- Homomorphism from K22 to K2 -/

def K22_to_K2 : K₂₂ →g K₂ where
  toFun
    | Sum.inl _ => Sum.inl 0
    | Sum.inr _ => Sum.inr 0
  map_rel' := by
    intro a b hab
    -- opposite sides map to inl 0 ∼ inr 0; same sides contradict hab
    cases a <;> cases b <;> simp_all [K₂₂, K₂]

/-- Next two parts give injective homomorphism from K2 to K22 (i.e., K2 is a subgraph of K22). -/

def K2_to_K22 : K₂ →g K₂₂ where
  toFun
    | Sum.inl _ => Sum.inl 0
    | Sum.inr _ => Sum.inr 0
  map_rel' := by
    intro a b hab
    match a, b with
    | Sum.inl _, Sum.inr _ => simp [K₂₂]
    | Sum.inr _, Sum.inl _ => simp [K₂₂]
    | Sum.inl x, Sum.inl y => simp [K₂] at hab
    | Sum.inr x, Sum.inr y => simp [K₂] at hab

theorem K2_to_K22_injective : Function.Injective K2_to_K22 := by
  intro a b h
  match a, b with
  | Sum.inl x, Sum.inl y =>
    exact congrArg Sum.inl (Subsingleton.elim x y)
  | Sum.inr x, Sum.inr y =>
    exact congrArg Sum.inr (Subsingleton.elim x y)
  | Sum.inl _, Sum.inr _ => simp [K2_to_K22] at h
  | Sum.inr _, Sum.inl _ => simp [K2_to_K22] at h

-- Finally the proof that K2 is a core of K22.

example : K₂₂.HasCore K₂ :=
  ⟨K2_isCore, ⟨K22_to_K2⟩, K2_to_K22, K2_to_K22_injective⟩

-- Combinatorics 23: Local injection

/-- Sanity check 1: The homomorphism from K_{1,2} to K_2 sending the two right vertices to a single vertex is NOT a local injection.-/

abbrev K2 : SimpleGraph (Fin 2) := ⊤

abbrev K12 : SimpleGraph (Fin 3) :=
  SimpleGraph.fromRel fun u v => u.val + v.val = 1 ∨ u.val + v.val = 3

instance K12_decidableAdj : DecidableRel K12.Adj := fun a b => by
  unfold K12 SimpleGraph.fromRel
  infer_instance

abbrev K12_to_K2 : K12 →g K2 where
  toFun u := if u = 0 then 0 else if u = 1 then 1 else 0
  map_rel' := by decide

example : ¬ K12.IsLocalInjection K2 K12_to_K2 := by
  intro h
  have hfab : K12_to_K2 0 = K12_to_K2 2 := by decide
  have hne : (0 : Fin 3) ≠ 2 := by decide
  have h3 := h 0 2 hfab hne
  have hed : K12.edist 0 2 = 2 := by
    rw [edist_eq_two_iff]
    refine ⟨by decide, by decide, 1, ?_⟩
    rw [mem_commonNeighbors]
    exact ⟨by decide, by decide⟩
  rw [hed] at h3
  exact absurd h3 (by decide)

/- Sanity check 2: the identity automorphism of `K₂` is (vacuously) a local
    injection, since each fibre is a singleton. -/

example : K2.IsLocalInjection K2 SimpleGraph.Hom.id :=
  fun _ _ hab hne => absurd hab hne

-- Combinatorics 24: Local isomorphism

/-- Sanity check: `2K₂`, two disjoint edges on `Fin 2 × Fin 2`. -/

abbrev twoK2 : SimpleGraph (Fin 2 × Fin 2) :=
  SimpleGraph.fromRel fun u v => u.2 = v.2

instance twoK2_decidableAdj : DecidableRel twoK2.Adj := fun a b => by
  unfold twoK2 SimpleGraph.fromRel
  infer_instance

/-- Decidability of the `K₂` adjacency relation, by unfolding the definition. -/

instance K2_decidableAdj : DecidableRel K2.Adj := fun a b => by
  unfold K2
  infer_instance

/-- The homomorphism folding each edge of `2K₂` onto `K₂`:
    `(0, j) ↦ 0` and `(1, j) ↦ 1`. -/

abbrev twoK2_to_K2 : twoK2 →g K2 where
  toFun u := u.1
  map_rel' := by decide

/-- Sanity check: the folding map `2K₂ → K₂` is a local isomorphism. -/

theorem twoK2_to_K2_localIso :
    twoK2.IsLocalIsomorphism K2 twoK2_to_K2 := by
  simp only [SimpleGraph.IsLocalIsomorphism, Set.BijOn, Set.MapsTo, Set.InjOn,
    Set.SurjOn, Set.subset_def, Set.mem_image, SimpleGraph.mem_neighborSet]
  decide

-- Combinatorics 429: Covers (graph)

-- NOTE: this sanity check builds trivially on the local isomorphism sanity check.

example : twoK2.Covers K2 := by
  refine ⟨twoK2_to_K2, twoK2_to_K2_localIso, ?_⟩
  change ∀ b : Fin 2, ∃ a : Fin 2 × Fin 2, twoK2_to_K2 a = b
  decide

-- Combinatorics 441: Folding

/- Sanity check: the path `0 — 1 — 2` maps onto `K₂` by a simple folding,
    identifying the two endpoints at distance two. -/

example : (SimpleGraph.fromRel fun u v : Fin 3 => u.val + v.val = 1 ∨ u.val + v.val = 3).IsSimpleFolding
    (⊤ : SimpleGraph (Fin 2))
    { toFun := fun u => if u = 1 then 1 else 0
      map_rel' := by decide } := by
  refine ⟨0, 2, by decide, ?_, by decide, ?_⟩
  · rw [edist_eq_two_iff]
    refine ⟨by decide, by decide, 1, ?_⟩
    rw [mem_commonNeighbors]
    exact ⟨by decide, by decide⟩
  · decide

/- The path hence folds onto `K₂`. -/

example : (SimpleGraph.fromRel fun u v : Fin 3 => u.val + v.val = 1 ∨ u.val + v.val = 3).IsFolding
    (⊤ : SimpleGraph (Fin 2))
    { toFun := fun u => if u = 1 then 1 else 0
      map_rel' := by decide } := by
  refine IsFolding.simple _ ⟨0, 2, by decide, ?_, by decide, ?_⟩
  · rw [edist_eq_two_iff]
    refine ⟨by decide, by decide, 1, ?_⟩
    rw [mem_commonNeighbors]
    exact ⟨by decide, by decide⟩
  · decide

end MathlibExtTest.Combinatorics.SimpleGraph.AlgebraicGraphTheory.Homomorphisms

end
