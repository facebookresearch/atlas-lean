/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantHomotopyGeneratorDetection
import MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftKanWeak
import Batteries.Tactic.Lint

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe w u v t s

open CategoryTheory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.CofibrantHomotopyGeneratorClients

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

open CofibrantHomotopyGeneratorDetection

/-- The complete generic native detector retains arbitrary original arrow endpoints. -/
theorem original_all_cofibrant_tests {X Y : C} (f : X ⟶ Y) :
    weakEquivalences C f ↔
      ∀ A : C, IsCofibrant A → IsIso (GeneratedRightMappingEnrichment.postcomp d A f) :=
  weak_iff_native_postcomp_cofibrant d f

/-- Actual cofibrant-source raw calculations use the original right frame at arbitrary targets. -/
theorem original_raw_calculation (A : C) [IsCofibrant A] {X Y : C} (f : X ⟶ Y) :
    IsIso (GeneratedRightMappingEnrichment.postcomp d A f) ↔ WeakEquivalence (rawPostcomp d A f) :=
  nativePostcomp_iff_raw d A f

/-- Both original input actions retain the complete degreewise source/frame composite. -/
theorem original_all_coordinates {A B X Y : C} (i : A ⟶ B) (f : X ⟶ Y)
    (n : SimplexCategoryᵒᵖ) (g : (rawSpace d B X).obj n) :
    (rawPostcomp d A f).app n ((rawPrecomp d i X).app n g) =
      i ≫ g ≫ ((GeneratedFramings.rightFrame d).map f).app n := by
  change B ⟶ ((GeneratedFramings.rightFrame d).obj X).obj n at g
  rw [rawPostcomp_app, rawPrecomp_app]
  exact Category.assoc _ _ _

/-- Source continuity is tested at independent original diagram object and Hom universes. -/
theorem original_source_continuity (Y : C) :
    CategoryTheory.Limits.PreservesLimitsOfSize.{t, s} ((rawBifunctor d).flip.obj Y) :=
  rawSource_preservesLimits d Y

end HomotopicalAlgebra.CofibrantHomotopyGeneratorClients

namespace SSet.OriginalKanLiftClient

/-- The whole actual source map, with independent value and lift universes,
preserves and reflects the original Kan weak predicate. -/
theorem original_map_weak_iff {X Y : SSet.{v}} [KanComplex X] [KanComplex Y] (f : X ⟶ Y) :
    KanComplex.W (SSet.uliftFunctor.{w, v}.map f) ↔ KanComplex.W f :=
  KanComplex.W_ulift_map_iff f

end SSet.OriginalKanLiftClient

#print axioms HomotopicalAlgebra.CofibrantHomotopyGeneratorDetection.rawBifunctor
#print axioms HomotopicalAlgebra.CofibrantHomotopyGeneratorDetection.rawSpace
#print axioms HomotopicalAlgebra.CofibrantHomotopyGeneratorDetection.rawPrecomp
#print axioms HomotopicalAlgebra.CofibrantHomotopyGeneratorDetection.rawPostcomp
#print axioms HomotopicalAlgebra.CofibrantHomotopyGeneratorDetection.rawSpace_obj
#print axioms HomotopicalAlgebra.CofibrantHomotopyGeneratorDetection.rawPrecomp_app
#print axioms HomotopicalAlgebra.CofibrantHomotopyGeneratorDetection.rawPostcomp_app
#print axioms HomotopicalAlgebra.CofibrantHomotopyGeneratorDetection.raw_naturality
#print axioms HomotopicalAlgebra.CofibrantHomotopyGeneratorDetection.rawSource_preservesLimits
#print axioms HomotopicalAlgebra.CofibrantHomotopyGeneratorDetection.rawSpace_Q
#print axioms HomotopicalAlgebra.CofibrantHomotopyGeneratorDetection.rawPostcomp_Q
#print axioms HomotopicalAlgebra.CofibrantHomotopyGeneratorDetection.rawPrecomp_weak
#print axioms HomotopicalAlgebra.CofibrantHomotopyGeneratorDetection.rawPrecomp_fibration
#print axioms HomotopicalAlgebra.CofibrantHomotopyGeneratorDetection.rawSpace_kanComplex
#print axioms HomotopicalAlgebra.CofibrantHomotopyGeneratorDetection.nativePostcomp_iff_raw_Q
#print axioms HomotopicalAlgebra.CofibrantHomotopyGeneratorDetection.nativePostcomp_iff_raw
#print axioms HomotopicalAlgebra.CofibrantHomotopyGeneratorDetection.nativePostcomp_weak_source_iff
#print axioms HomotopicalAlgebra.CofibrantHomotopyGeneratorDetection.nativePostcomp_hom_bijective
#print axioms HomotopicalAlgebra.CofibrantHomotopyGeneratorDetection.weak_iff_native_postcomp_all
#print axioms HomotopicalAlgebra.CofibrantHomotopyGeneratorDetection.weak_iff_native_postcomp_cofibrant
#print axioms SSet.KanComplex.W_ulift_map_iff
#print axioms SSet.OriginalKanLiftClient.original_map_weak_iff

#lint only unusedArguments in MathlibExt.AlgebraicTopology.ModelCategory.CofibrantHomotopyGeneratorDetection
#lint only unusedArguments in MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftStandardIso
#lint only unusedArguments in MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftHomEquiv
#lint only unusedArguments in MathlibExt.AlgebraicTopology.SimplicialSet.ULiftKan
#lint only unusedArguments in MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftPointedSimplex
#lint only unusedArguments in MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftPointedRelation
#lint only unusedArguments in MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftPiEquivalence
#lint only unusedArguments in MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftPiNaturality
#lint only unusedArguments in MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftFundamentalGroupoid
#lint only unusedArguments in MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftGroupoidNaturality
#lint only unusedArguments in MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftKanWeak
