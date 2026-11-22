/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCoordinateHornWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootBoundarySupport

/-!
# The SAME original root-horn support in the original whole cone

At the original root retain all original upper coordinate faces and all
original lower coordinate faces except the actual omitted coordinate.
Above the root retain the entire original cone coefficient. Every whole
original path action preserves these supports: incoming positive paths
retain that positive coordinate in an original upper face, and the
original self-path acts by its exact original identity.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The original root keeps its SAME entire horn of upper and eligible lower coordinates, and every positive
coefficient keeps the whole original cone. -/
def coneRootHornSupport {n : ℕ} (k : Fin (n + 2)) (i : Vertex.{u} (n + 1)) :
    (nerve (ConeSubset i)).Subcomplex :=
  if i = ⊥ then
    ⨆ c : Sum {c : Vertex.{u} (n + 1) // i < c}
        {c : Vertex.{u} (n + 1) // i < c ∧ c ≠ ULift.up k},
      match c with
      | .inl c => coneCoordinateFace i c.val true
      | .inr c => coneCoordinateFace i c.val false
  else ⊤

/-- At the actual original root the supported carrier is precisely the SAME entire original root-coordinate horn. -/
theorem coneRootHornSupport_root {n : ℕ} (k : Fin (n + 2)) :
    coneRootHornSupport k (⊥ : Vertex.{u} (n + 1)) = coneRootCoordinateHorn.{u} k := by
  ext q a
  refine Iff.trans ?_ (mem_coneRootCoordinateHorn_iff k q a).symm
  simp only [coneRootHornSupport]
  split_ifs with hi
  · simp only [Subfunctor.iSup_obj, Set.mem_iUnion, Sum.exists, coneCoordinateFace,
      Bool.false_eq_true, iff_false, iff_true]
    rfl
  · exact (hi True.intro).elim

/-- Every positive original coefficient retains its whole unchanged original cone. -/
theorem coneRootHornSupport_above {n : ℕ} (k : Fin (n + 2)) {i : Vertex.{u} (n + 1)}
    (hi : (⊥ : Vertex.{u} (n + 1)) < i) : coneRootHornSupport k i = ⊤ := by
  simp [coneRootHornSupport, ne_of_gt hi]

/-- All whole original path actions retain the SAME original supported horn at root and complete original
coefficients above root. -/
theorem coneRootHornSupport_action_mem {n : ℕ} (k : Fin (n + 2)) (i j : Vertex.{u} (n + 1))
    (q : SimplexCategoryᵒᵖ) (p : (nerve (SimplicialThickening.Path i j)).obj q)
    (a : (nerve (ConeSubset j)).obj q) (ha : a ∈ (coneRootHornSupport k j).obj q) :
    (coneAction i j).hom.app q (p, a) ∈ (coneRootHornSupport k i).obj q := by
  by_cases hi : i = ⊥
  · subst i
    by_cases hj : j = ⊥
    · subst j
      have h : (coneAction (⊥ : Vertex.{u} (n + 1)) ⊥).hom.app q (p, a) = a := by
        refine CategoryTheory.Functor.ext (fun t => ?_) (fun _ _ _ => Subsingleton.elim _ _)
        change (a.obj t).prepend (p.obj t) = a.obj t
        exact (congrArg
          (fun x : SimplicialThickening.Path (⊥ : Vertex.{u} (n + 1)) ⊥ => (a.obj t).prepend x)
          (coneSelfPath_eq_id (p.obj t))).trans (ConeSubset.prepend_id (a.obj t))
      exact h.symm ▸ ha
    · have hpos : (⊥ : Vertex.{u} (n + 1)) < j := lt_of_le_of_ne bot_le (Ne.symm hj)
      have hroot := coneRootHornSupport_root.{u} k
      apply (congrArg (fun A => (coneAction (⊥ : Vertex.{u} (n + 1)) j).hom.app q (p, a) ∈ A.obj q) hroot).to_iff.mpr
      apply (mem_coneRootCoordinateHorn_iff k q _).mpr
      left
      refine ⟨⟨j, hpos⟩, fun t => ?_⟩
      change j ∈ (p.obj t).I.toFinite.toFinset ∪ (a.obj t).vertices
      exact Finset.mem_union_right _ (a.obj t).mem
  · have hs : coneRootHornSupport k i = ⊤ := by simp [coneRootHornSupport, hi]
    rw [hs]
    exact Set.mem_univ _

/-- Every original supported horn coefficient inherits precisely its SAME original full cone maximum marking. -/
def coneRootHornMarked {n : ℕ} (k : Fin (n + 2)) (i : Vertex.{u} (n + 1)) : Marked.{u} :=
  comap (coneWeight i) (coneRootHornSupport k i).ι

/-- The SAME original supported marked coefficient enters the entire original cone by its literal original inclusion. -/
def coneRootHornInclusion {n : ℕ} (k : Fin (n + 2)) (i : Vertex.{u} (n + 1)) :
    coneRootHornMarked k i ⟶ coneWeight i := comapHom (coneWeight i) (coneRootHornSupport k i).ι

/-- Every actual original supported coefficient inclusion is monic on its unchanged whole simplicial carrier. -/
instance {n : ℕ} (k : Fin (n + 2)) (i : Vertex.{u} (n + 1)) : Mono (coneRootHornInclusion k i) :=
  (mono_iff_underlying _).mpr (inferInstance : Mono (coneRootHornSupport k i).ι)

/-- Above the original root the SAME original support is the whole original marked coefficient isomorphism. -/
def coneRootHornAboveIso {n : ℕ} (k : Fin (n + 2)) {i : Vertex.{u} (n + 1)}
    (hi : (⊥ : Vertex.{u} (n + 1)) < i) : coneRootHornMarked k i ≅ coneWeight i :=
  isoMk (Subcomplex.eqToIso (coneRootHornSupport_above k hi) ≪≫ Subcomplex.topIso (nerve (ConeSubset i)))
    (fun _ => Iff.rfl)

/-- The whole original positive coefficient isomorphism retains exactly its literal original supported inclusion. -/
theorem coneRootHornAboveIso_hom {n : ℕ} (k : Fin (n + 2)) {i : Vertex.{u} (n + 1)}
    (hi : (⊥ : Vertex.{u} (n + 1)) < i) : (coneRootHornAboveIso k hi).hom = coneRootHornInclusion k i :=
  Hom.ext rfl

/-- The original root supported coefficient is exactly the SAME entire original marked coordinate horn. -/
def coneRootHornRootIso {n : ℕ} (k : Fin (n + 2)) :
    coneRootHornMarked k (⊥ : Vertex.{u} (n + 1)) ≅ coneRootCoordinateHornMarked k :=
  isoMk (Subcomplex.eqToIso (coneRootHornSupport_root k)) (fun _ => Iff.rfl)

/-- The SAME original root coefficient isomorphism retains precisely its literal original horn attaching map. -/
theorem coneRootHornRootIso_inclusion {n : ℕ} (k : Fin (n + 2)) :
    (coneRootHornRootIso.{u} k).hom ≫ coneRootCoordinateHornMap k =
      coneRootHornInclusion k (⊥ : Vertex.{u} (n + 1)) := Hom.ext rfl

end SSet.Marked.CoherentWeight
