/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidCoverParentEdges
import MathlibExt.AlgebraicTopology.SimplicialSet.FreePathNerveGraphWeak
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Full native original covering-graph rank filtration

Each stage keeps the SAME original generating graph simplex and every
individual original vertex of rank bounded by the supplied stage.
Every ordinal operator and the full native sequential union retain
the original vertices, paths and coefficient maps.
-/

noncomputable section
universe u v
open CategoryTheory Limits Opposite
open scoped Simplicial
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V] (z : V)
/-- The SAME original generating cover quiver used by the native rank diagram. -/
private local instance coverQuiverForRank : Quiver.{v} (CoverVertex V z) := coverQuiver V z

/-- The SAME complete original covering generating graph in its native free-path nerve. -/
abbrev coverGraph : (nerve (Paths (CoverVertex V z))).Subcomplex :=
  CategoryTheory.FreePathNerveCoordinates.generatingGraph (CoverVertex V z)

/-- Original generating graph words with EVERY actual original vertex rank bounded. -/
def coverRankStage (k : ℕ) : (nerve (Paths (CoverVertex V z))).Subcomplex where
  obj q := {w | w ∈ (coverGraph V z).obj q ∧
    ∀ i : Fin (q.unop.len + 1), CoverVertex.rank V z (w.obj i) ≤ k}
  map {q r} f w hw := by
    change (nerve (Paths (CoverVertex V z))).map f w ∈ (coverGraph V z).obj r ∧
      ∀ i : Fin (r.unop.len + 1),
        CoverVertex.rank V z (((nerve (Paths (CoverVertex V z))).map f w).obj i) ≤ k
    have hg : w ∈ (coverGraph V z).obj q := hw.1
    exact ⟨(coverGraph V z).map f hg, fun i => hw.2 (f.unop.toOrderHom i)⟩

/-- Stage membership retains the original graph word and every actual original vertex rank. -/
lemma mem_coverRankStage (k : ℕ) (q : SimplexCategoryᵒᵖ)
    (w : (nerve (Paths (CoverVertex V z))).obj q) :
    w ∈ (coverRankStage V z k).obj q ↔ w ∈ (coverGraph V z).obj q ∧
      ∀ i : Fin (q.unop.len + 1), CoverVertex.rank V z (w.obj i) ≤ k := Iff.rfl

/-- Every SAME original stage word retains all its original coefficients in later stages. -/
lemma coverRankStage_mono {k l : ℕ} (h : k ≤ l) : coverRankStage V z k ≤ coverRankStage V z l := by
  intro q w hw
  exact (mem_coverRankStage V z l q w).mpr
    ⟨((mem_coverRankStage V z k q w).mp hw).1,
      fun i => (((mem_coverRankStage V z k q w).mp hw).2 i).trans h⟩

/-- Every entire original rank stage is contained in the SAME full native original graph. -/
lemma coverRankStage_le_graph (k : ℕ) : coverRankStage V z k ≤ coverGraph V z := by
  intro q w hw
  exact ((mem_coverRankStage V z k q w).mp hw).1

/-- The entire native original rank-stage union is the SAME complete original generating graph. -/
lemma coverRankStage_iSup : (⨆ k : ℕ, coverRankStage V z k) = coverGraph V z := by
  ext q w
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion]
  constructor
  · rintro ⟨k, hw⟩
    exact coverRankStage_le_graph V z k q hw
  · intro hw
    let k := Finset.univ.sup (fun i : Fin (q.unop.len + 1) => CoverVertex.rank V z (w.obj i))
    exact ⟨k, (mem_coverRankStage V z k q w).mpr
      ⟨hw, fun i => Finset.le_sup (f := fun j : Fin (q.unop.len + 1) => CoverVertex.rank V z (w.obj j))
        (Finset.mem_univ i)⟩⟩

/-- The actual entire original cover rank diagram uses only native full stage inclusions. -/
def coverRankDiagram : ℕ ⥤ SSet.{max u v} :=
  (show Monotone (coverRankStage V z) from fun _ _ h => coverRankStage_mono V z h).functor ⋙
    SSet.Subcomplex.toSSetFunctor

/-- Every original rank-diagram transition is the SAME full native monomorphism. -/
instance coverRankDiagram_map_mono {n m : ℕ} (f : n ⟶ m) : Mono ((coverRankDiagram V z).map f) :=
  SSet.Subcomplex.mono_homOfLE (coverRankStage_mono V z (leOfHom f))

/-- The actual rank-diagram cocone lands in the SAME original native cover graph. -/
def coverRankCocone : Cocone (coverRankDiagram V z) where
  pt := coverGraph V z
  ι.app n := SSet.Subcomplex.homOfLE (coverRankStage_le_graph V z n)
  ι.naturality := fun {_ _} _ => rfl

/-- The complete original rank cocone is a genuine full native colimit. -/
def coverRankCoconeIsColimit : IsColimit (coverRankCocone V z) := by
  let F : ℕ ⥤ (nerve (Paths (CoverVertex V z))).Subcomplex :=
    (show Monotone (coverRankStage V z) from fun _ _ h => coverRankStage_mono V z h).functor
  exact IsColimit.ofIsoColimit (isColimitOfPreserves SSet.Subcomplex.toSSetFunctor
    (CompleteLattice.colimitCocone F).isColimit)
      (Cocone.ext (SSet.Subcomplex.eqToIso (coverRankStage_iSup V z)))

end Quiver.FreeGroupoid.OriginalWords
