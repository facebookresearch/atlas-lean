/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.IteratedStageReindex

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Waldhausen.SConstruction

namespace MathlibExtTest.IteratedStageReindex

variable (C : Type (max u v)) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- An arbitrary number of original simplex directions earn exactness. -/
theorem originalTupleMapExact {r : ℕ} {a b : StageSimplexTuple r} (α : a ⟶ b) :
    (reindexIteratedStage C α).IsWaldhausenExact :=
  reindexIteratedStage_isWaldhausenExact C α

/-- No directions retain the original identity functor. -/
theorem originalEmptyReindex (a : StageSimplexTuple 0) (α : a ⟶ a) :
    reindexIteratedStage C α = 𝟭 (StageAtTuple C a) :=
  reindexIteratedStage_zero C a α

/-- A single original direction retains the head ordinal reindex and the zero-direction tail. -/
theorem originalOneReindex {a b : StageSimplexTuple 1} (α : a ⟶ b) :
    reindexIteratedStage C α =
      (iteratedStageOfFnSuccEquivalence C (fun i => (a i).unop.len)).functor ⋙
        (reindexStage (C := StageAtTuple C (fun i : Fin 0 => a i.succ)) (α 0).unop ⋙
          (reindexIteratedStage_isWaldhausenExact C (fun i : Fin 0 => α i.succ)).mapStage
            (b 0).unop.len) ⋙
        (iteratedStageOfFnSuccEquivalence C (fun i => (b i).unop.len)).inverse :=
  reindexIteratedStage_succ C α

/-- The full original one-direction object readout is exposed to a direct client. -/
theorem originalOneObject {a b : StageSimplexTuple 1} (α : a ⟶ b) (X : StageAtTuple C a) :
    (reindexIteratedStage C α).obj X =
      (iteratedStageOfFnSuccEquivalence C (fun i => (b i).unop.len)).inverse.obj
        (((reindexIteratedStage_isWaldhausenExact C (fun i : Fin 0 => α i.succ)).mapStage
          (b 0).unop.len).obj
          ((reindexStage (C := StageAtTuple C (fun i : Fin 0 => a i.succ)) (α 0).unop).obj
            ((iteratedStageOfFnSuccEquivalence C (fun i => (a i).unop.len)).functor.obj X))) :=
  reindexIteratedStage_succ_obj C α X

/-- The original single-direction morphism readout uses the same head and tail component maps. -/
theorem originalOneMorphism {a b : StageSimplexTuple 1} (α : a ⟶ b)
    {X Y : StageAtTuple C a} (f : X ⟶ Y) :
    HEq ((reindexIteratedStage C α).map f)
      ((iteratedStageOfFnSuccEquivalence C (fun i => (b i).unop.len)).inverse.map
        (((reindexIteratedStage_isWaldhausenExact C (fun i : Fin 0 => α i.succ)).mapStage
          (b 0).unop.len).map
          ((reindexStage (C := StageAtTuple C (fun i : Fin 0 => a i.succ)) (α 0).unop).map
            ((iteratedStageOfFnSuccEquivalence C (fun i => (a i).unop.len)).functor.map f)))) :=
  reindexIteratedStage_succ_map C α f

end MathlibExtTest.IteratedStageReindex
