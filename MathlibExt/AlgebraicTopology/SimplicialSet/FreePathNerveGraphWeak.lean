/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreePathNerveStagePreimageWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceSequentialMono
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexEvaluation

/-!
# The SAME original generating graph and full native free-path nerve

Every original nonzero length-stage inclusion is weak from its actual
all-word pushout and full original cell preimage. The entire original
word-length diagram has monic transitions and its native union is the
SAME full path-category nerve. The actual sequential-mono colimit
weak theorem proves weakness of the original graph inclusion.
-/

noncomputable section
universe u v
open CategoryTheory Limits Opposite
open scoped Simplicial
namespace CategoryTheory.FreePathNerveCoordinates
variable (V : Type u) [Quiver.{v} V]

/-- The SAME entire original nonzero word-length filtration as a native sequential diagram. -/
def lengthDiagram : ℕ ⥤ SSet.{max u v} :=
  (show Monotone (fun n : ℕ => lengthStage V (n + 1)) from
    fun _ _ h => lengthStage_mono V (Nat.add_le_add_right h 1)).functor ⋙ SSet.Subcomplex.toSSetFunctor

/-- Every transition keeps the SAME complete original word and native inclusion. -/
instance lengthDiagram_map_mono {n m : ℕ} (f : n ⟶ m) : Mono ((lengthDiagram V).map f) :=
  SSet.Subcomplex.mono_homOfLE (lengthStage_mono V (Nat.add_le_add_right (leOfHom f) 1))

/-- The actual original graph-to-stage comparison retains every complete original graph coefficient. -/
def graphToLengthDiagram : (Functor.const ℕ).obj (generatingGraph V : SSet.{max u v}) ⟶ lengthDiagram V where
  app n := SSet.Subcomplex.homOfLE (lengthStage_mono V (Nat.le_add_left 1 n))
  naturality := fun {_ _} _ => rfl

/-- The SAME actual original graph-to-stage map is weak at every original finite length. -/
lemma graphToLengthDiagram_weak (n : ℕ) : SSet.realizationWeakEquivalences ((graphToLengthDiagram V).app n) := by
  induction n with
  | zero => exact SSet.realizationWeakEquivalences.id_mem _
  | succ n ih =>
    have hf : (graphToLengthDiagram V).app (n + 1) =
        (graphToLengthDiagram V).app n ≫ SSet.Subcomplex.homOfLE
          (lengthStage_mono V (Nat.le_succ (n + 1))) := rfl
    exact hf ▸ SSet.realizationWeakEquivalences.comp_mem _ _ ih (original_stage_inclusion_weak V n)

/-- The SAME full native original path nerve is the original length-diagram cocone. -/
def lengthCocone : Cocone (lengthDiagram V) where
  pt := nerve (Paths V)
  ι.app n := (lengthStage V (n + 1)).ι
  ι.naturality := fun {_ _} _ => rfl

/-- All original words occur in the nonzero native length stages. -/
lemma lengthStage_nonzero_iSup : (⨆ n : ℕ, lengthStage V (n + 1)) = ⊤ := by
  ext q w
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion, Subfunctor.top_obj, Set.mem_univ, iff_true]
  exact ⟨(totalPath V q.unop.len w).length,
    show (totalPath V q.unop.len w).length ≤ (totalPath V q.unop.len w).length + 1 from Nat.le_succ _⟩

/-- The full original length-diagram cocone is a genuine native colimit. -/
def lengthCoconeIsColimit : IsColimit (lengthCocone V) := by
  let F : ℕ ⥤ (nerve (Paths V)).Subcomplex :=
    (show Monotone (fun n : ℕ => lengthStage V (n + 1)) from
      fun _ _ h => lengthStage_mono V (Nat.add_le_add_right h 1)).functor
  exact IsColimit.ofIsoColimit (isColimitOfPreserves SSet.Subcomplex.toSSetFunctor
    (CompleteLattice.colimitCocone F).isColimit)
      (Cocone.ext (SSet.Subcomplex.eqToIso (lengthStage_nonzero_iSup V) ≪≫ SSet.Subcomplex.topIso _))

/-- The actual original constant graph cocone retains the SAME complete native graph object. -/
def graphCocone : Cocone ((Functor.const ℕ).obj (generatingGraph V : SSet.{max u v})) where
  pt := generatingGraph V
  ι.app _ := 𝟙 _
  ι.naturality := fun {_ _} _ => rfl

/-- The actual original constant graph cocone is a genuine full colimit. -/
def graphCoconeIsColimit : IsColimit (graphCocone V) where
  desc c := c.ι.app 0
  fac c n := by
    have h := c.w (homOfLE (Nat.zero_le n))
    change c.ι.app n = c.ι.app 0 at h
    exact (Category.id_comp _).trans h.symm
  uniq c f h := (Category.id_comp f).symm.trans (h 0)

/-- The SAME actual original generating-graph inclusion into the full native
free-path-category nerve is a realization weak equivalence, at ALL arities. -/
theorem generatingGraph_inclusion_weak :
    SSet.realizationWeakEquivalences (generatingGraph V).ι := by
  apply SSet.realizationWeakEquivalences.of_isColimit_nat_mono (graphToLengthDiagram V)
    (graphCoconeIsColimit V) (lengthCoconeIsColimit V) (generatingGraph V).ι
    (fun _ => rfl)
  · intro i j f
    change Mono (𝟙 (generatingGraph V : SSet.{max u v}))
    infer_instance
  · intro i j f
    exact lengthDiagram_map_mono V f
  · exact graphToLengthDiagram_weak V

end CategoryTheory.FreePathNerveCoordinates
