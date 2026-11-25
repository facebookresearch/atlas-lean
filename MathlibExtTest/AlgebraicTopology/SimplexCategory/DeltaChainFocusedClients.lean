/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplexCategory.GeneratorsRelations.DeltaChain
import MathlibExt.AlgebraicTopology.SimplexCategory.GeneratorsRelations.Equivalence

/-!
# Concrete simplex normal forms and generator round trips

The three-face chain `[2,0,1]` from degree one to degree four is not admissible.
Insertion normalization produces `[0,1,4]`, not just the sorted original list: moving a
face past another face increments its index. Both evaluations send the two source
vertices to `2` and `3`, independently pinning the generator orientation.

The face and degeneracy examples below check both actual presentation functors and
literal vertex images. The degree-zero boundary distinguishes the two faces of a
one-simplex, and a split face/degeneracy pair is a left inverse, not a right inverse.
-/

noncomputable section

open CategoryTheory
open SimplexCategoryGenRel

namespace DeltaChainFocusedClients

private abbrev unsorted : DeltaChain 1 4 :=
  (((DeltaChain.nil (n := 1)).snoc (2 : Fin 3)).snoc (0 : Fin 4)).snoc (1 : Fin 5)

private abbrev expected : DeltaChain 1 4 :=
  (((DeltaChain.nil (n := 1)).snoc (0 : Fin 3)).snoc (1 : Fin 4)).snoc (4 : Fin 5)

example : unsorted.toNatList = [2, 0, 1] := rfl

example : ¬ DeltaChain.Admissible unsorted := by
  intro h
  have hpair := h.toNatList_pairwise_lt
  change ([2, 0, 1] : List ℕ).Pairwise (· < ·) at hpair
  have h20 := (List.pairwise_cons.mp hpair).1 0 (by simp)
  omega

private lemma normalized_exact : unsorted.normalize = expected := by
  rfl

-- Exact output order, shifted index and endpoint bound are checked concretely.
example : unsorted.normalize.toNatList = [0, 1, 4] := by
  rw [normalized_exact]
  rfl

example : DeltaChain.Admissible unsorted.normalize :=
  DeltaChain.normalize_admissible unsorted

example : unsorted.normalize.toNatList.Pairwise (· < ·) := by
  rw [normalized_exact]
  decide

example : DeltaChain.AllValsLt unsorted.normalize 5 := by
  rw [normalized_exact]
  change ((True ∧ (0 : ℕ) < 5) ∧ (1 : ℕ) < 5) ∧ (4 : ℕ) < 5
  decide

example : unsorted.normalize.toNatList.length = 3 := by
  rw [normalized_exact]
  rfl

example : unsorted.normalize.toNatList ≠ [0, 1, 3] := by
  rw [normalized_exact]
  decide

example : unsorted.normalize.eval = unsorted.eval :=
  DeltaChain.normalize_eval unsorted

private lemma raw_vertex_zero : unsorted.evalOrderHom (0 : Fin 2) = (2 : Fin 5) := by
  simp only [unsorted, DeltaChain.evalOrderHom_snoc_apply]
  rfl

private lemma raw_vertex_one : unsorted.evalOrderHom (1 : Fin 2) = (3 : Fin 5) := by
  simp only [unsorted, DeltaChain.evalOrderHom_snoc_apply]
  rfl

example : [unsorted.evalOrderHom 0, unsorted.evalOrderHom 1] = [2, 3] := by
  rw [raw_vertex_zero, raw_vertex_one]

example : unsorted.normalize.evalOrderHom (0 : Fin 2) = (2 : Fin 5) := by
  rw [normalized_exact]
  simp only [expected, DeltaChain.evalOrderHom_snoc_apply]
  rfl

example : unsorted.normalize.evalOrderHom (1 : Fin 2) = (3 : Fin 5) := by
  rw [normalized_exact]
  simp only [expected, DeltaChain.evalOrderHom_snoc_apply]
  rfl

example : unsorted.evalOrderHom (0 : Fin 2) ≠ (0 : Fin 5) := by
  rw [raw_vertex_zero]
  decide

-- Equal successive indices exercise the insertion branch that increments an index.
private abbrev repeated : DeltaChain 0 2 :=
  ((DeltaChain.nil (n := 0)).snoc (1 : Fin 2)).snoc (1 : Fin 3)

example : ¬ DeltaChain.Admissible repeated := by
  intro h
  have hpair := h.toNatList_pairwise_lt
  change ([1, 1] : List ℕ).Pairwise (· < ·) at hpair
  have h11 := (List.pairwise_cons.mp hpair).1 1 (by simp)
  omega

example : repeated.normalize.toNatList = [1, 2] := rfl

example : repeated.normalize.evalOrderHom (0 : Fin 1) = (0 : Fin 3) := rfl

example : (DeltaChain.nil (n := 0)).normalize.toNatList = [] := rfl

-- These are nonidentity generators: the face skips vertex one, the degeneracy
-- identifies vertices zero and one. All listed values use the actual functors.
private abbrev face : SimplexCategoryGenRel.mk 1 ⟶ SimplexCategoryGenRel.mk 2 :=
  SimplexCategoryGenRel.δ (1 : Fin 3)

private abbrev degeneracy : SimplexCategoryGenRel.mk 2 ⟶ SimplexCategoryGenRel.mk 1 :=
  SimplexCategoryGenRel.σ (0 : Fin 2)

example : fromSimplexCategory.map (toSimplexCategory.map face) = face := by
  change fromSimplexCategory.map (SimplexCategory.δ (1 : Fin 3)) =
    SimplexCategoryGenRel.δ (1 : Fin 3)
  exact fromSimplexCategory_map_δ _

example : fromSimplexCategory.map (toSimplexCategory.map degeneracy) = degeneracy := by
  change fromSimplexCategory.map (SimplexCategory.σ (0 : Fin 2)) =
    SimplexCategoryGenRel.σ (0 : Fin 2)
  exact fromSimplexCategory_map_σ _

example : toSimplexCategory.map (fromSimplexCategory.map
    (SimplexCategory.δ (1 : Fin 3))) = SimplexCategory.δ (1 : Fin 3) :=
  fromSimplexCategory_map_preimage _

example : toSimplexCategory.map (fromSimplexCategory.map
    (SimplexCategory.σ (0 : Fin 2))) = SimplexCategory.σ (0 : Fin 2) :=
  fromSimplexCategory_map_preimage _

private lemma face_images :
    [(toSimplexCategory.map face).toOrderHom 0,
      (toSimplexCategory.map face).toOrderHom 1] = [0, 2] := by
  rfl

private lemma degeneracy_images :
    [(toSimplexCategory.map degeneracy).toOrderHom 0,
      (toSimplexCategory.map degeneracy).toOrderHom 1,
      (toSimplexCategory.map degeneracy).toOrderHom 2] = [0, 0, 1] := by
  rfl

example : [(toSimplexCategory.map (fromSimplexCategory.map
    (SimplexCategory.δ (1 : Fin 3)))).toOrderHom 0,
    (toSimplexCategory.map (fromSimplexCategory.map
      (SimplexCategory.δ (1 : Fin 3)))).toOrderHom 1] = [0, 2] := by
  simp only [fromSimplexCategory_map_preimage]
  rfl

example : [(toSimplexCategory.map (fromSimplexCategory.map
    (SimplexCategory.σ (0 : Fin 2)))).toOrderHom 0,
    (toSimplexCategory.map (fromSimplexCategory.map
      (SimplexCategory.σ (0 : Fin 2)))).toOrderHom 1,
    (toSimplexCategory.map (fromSimplexCategory.map
      (SimplexCategory.σ (0 : Fin 2)))).toOrderHom 2] = [0, 0, 1] := by
  simp only [fromSimplexCategory_map_preimage]
  rfl

example : (toSimplexCategory.map face).toOrderHom (1 : Fin 2) ≠ (1 : Fin 3) := by
  change (2 : Fin 3) ≠ 1
  decide

example : (toSimplexCategory.map degeneracy).toOrderHom (1 : Fin 3) ≠ (1 : Fin 2) := by
  change (0 : Fin 2) ≠ 1
  decide

-- At the smallest source degree the two face indices have different images.
example : (toSimplexCategory.map (SimplexCategoryGenRel.δ (0 : Fin 2))).toOrderHom
    (0 : Fin 1) = (1 : Fin 2) := rfl

example : (toSimplexCategory.map (SimplexCategoryGenRel.δ (1 : Fin 2))).toOrderHom
    (0 : Fin 1) = (0 : Fin 2) := rfl

example : fromSimplexCategory.map (SimplexCategory.δ (0 : Fin 2)) ≠
    fromSimplexCategory.map (SimplexCategory.δ (1 : Fin 2)) := by
  intro h
  have presentedEquality : SimplexCategoryGenRel.δ (0 : Fin 2) =
      SimplexCategoryGenRel.δ (1 : Fin 2) :=
    (fromSimplexCategory_map_δ (0 : Fin 2)).symm.trans
      (h.trans (fromSimplexCategory_map_δ (1 : Fin 2)))
  have h10 : (1 : Fin 2) = 0 := congrArg
    (fun f : SimplexCategoryGenRel.mk 0 ⟶ SimplexCategoryGenRel.mk 1 =>
      (toSimplexCategory.map f).toOrderHom 0) presentedEquality
  exact (by decide : (1 : Fin 2) ≠ 0) h10

example : (toSimplexCategory.map (fromSimplexCategory.map
    (SimplexCategory.σ (0 : Fin 1)))).toOrderHom (1 : Fin 2) = (0 : Fin 1) := by
  simp only [fromSimplexCategory_map_preimage]
  rfl

example : SimplexCategoryGenRel.δ (0 : Fin 2) ≫
    SimplexCategoryGenRel.σ (0 : Fin 1) = 𝟙 (SimplexCategoryGenRel.mk 0) :=
  SimplexCategoryGenRel.δ_comp_σ_self

-- Reversing that split pair gives the constant-one map, not the identity.
example : [(toSimplexCategory.map (SimplexCategoryGenRel.σ (0 : Fin 1) ≫
    SimplexCategoryGenRel.δ (0 : Fin 2))).toOrderHom 0,
    (toSimplexCategory.map (SimplexCategoryGenRel.σ (0 : Fin 1) ≫
      SimplexCategoryGenRel.δ (0 : Fin 2))).toOrderHom 1] = [1, 1] := by
  rfl

example : SimplexCategoryGenRel.σ (0 : Fin 1) ≫
    SimplexCategoryGenRel.δ (0 : Fin 2) ≠ 𝟙 (SimplexCategoryGenRel.mk 1) := by
  intro h
  have hm := congrArg (fun f => (toSimplexCategory.map f).toOrderHom (0 : Fin 2)) h
  have h10 : (1 : Fin 2) = 0 := hm
  exact (by decide : (1 : Fin 2) ≠ 0) h10

end DeltaChainFocusedClients
