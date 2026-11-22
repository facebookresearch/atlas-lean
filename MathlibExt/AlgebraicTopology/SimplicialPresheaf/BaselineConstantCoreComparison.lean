/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.TransferredCoreReplacements

/-!
# The actual baseline constant-source comparison

Replace the raw constant source using the existing original baseline R and
its actual unit. The chosen local derived end from that source maps to the
transferred scalar mapping model by original derived precomposition followed
by the previously proved projection. Both factors are weak. For the full and
normalized ordered families, the existing constant-baseline locality theorem
identifies this source as groupoidal and local-fibrant at every height.
No independent scalar replacement factors or universal property are assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w i

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
  HomotopicalAlgebra MonoidalClosed Opposite
open SimplicialPresheaf.InjectiveKan SimplicialPresheaf.OriginalLocalDerived
open scoped SSet.modelCategoryQuillen

attribute [local instance] SimplicialPresheaf.InjectiveKan.modelCategory

namespace SimplicialPresheaf.BaselineConstantCoreComparison

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]

/-- Use the existing baseline R after the literal constant extension. -/
def constantReplacement : SSet.{u} ⥤ SimplicialPresheaf.{u} D :=
  ConstantEvaluation.constant ⋙ originalR D

/-- The source unit is the actual baseline unit, whiskered by constant extension. -/
def unit : ConstantEvaluation.constant (D := D) ⟶ constantReplacement :=
  Functor.whiskerLeft ConstantEvaluation.constant (originalRUnit D)

/-- The baseline constant object retains the original baseline R choice. -/
theorem constantReplacement_obj (K : SSet.{u}) :
    (constantReplacement (D := D)).obj K =
      (originalR D).obj (ConstantEvaluation.constant.obj K) := rfl

/-- The source unit is exactly the existing original R unit component. -/
theorem unit_app (K : SSet.{u}) :
    (unit (D := D)).app K = (originalRUnit D).app (ConstantEvaluation.constant.obj K) := rfl

/-- The existing baseline unit is weak on the unchanged original presheaf carrier. -/
theorem unit_baselineWeak (K : SSet.{u}) :
    weakEquivalences (SimplicialPresheaf.{u} D) ((unit (D := D)).app K) :=
  (originalRUnit_trivialCofibration (ConstantEvaluation.constant.obj K)).2

variable {I : Type i}

/-- The baseline unit passes the original local weak tests for every original family. -/
theorem unit_originalLocalWeak (S : I → Arrow (SimplicialPresheaf.{u} D)) (K : SSet.{u}) :
    originalLocalEquivalences S ((unit (D := D)).app K) :=
  weakEquivalences_le_originalLocalEquivalences S _ (unit_baselineWeak K)

variable [Small.{u} I]

/-- The groupoidal-source comparison is the actual unit precomposition followed by gamma. -/
def comparison (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D) (K : SSet.{u})
    (C : SimplicialPresheaf.{u} D) :
    ((localDerivedEnd S).obj (op ((constantReplacement (D := D)).obj K))).obj C ⟶
      TransferredCoreReplacements.mappingModel S z K C :=
  localDerivedPrecomp S ((unit (D := D)).app K) C ≫
    TransferredCoreReplacements.comparison S z K C

/-- The defining composite retains the two actual prescribed maps. -/
theorem comparison_eq (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (K : SSet.{u}) (C : SimplicialPresheaf.{u} D) :
    comparison S z K C = localDerivedPrecomp S ((unit (D := D)).app K) C ≫
      DerivedZeroProjection.gamma S z K C := rfl

/-- Source naturality uses the actual baseline and localized Q actions. -/
theorem comparison_source (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    {K L : SSet.{u}} (k : K ⟶ L) (C : SimplicialPresheaf.{u} D) :
    localDerivedPrecomp S ((constantReplacement (D := D)).map k) C ≫ comparison S z K C =
      comparison S z L C ≫
        (pre ((TransferredCoreReplacements.qReplacement S z).map k)).app
          ((TransferredCoreReplacements.rReplacement S z).obj C) := by
  have hcomp₁ := (localDerivedEnd_laws S).2.1 ((unit (D := D)).app K)
    ((constantReplacement (D := D)).map k) C
  have hcomp₂ := (localDerivedEnd_laws S).2.1 (ConstantEvaluation.constant.map k)
    ((unit (D := D)).app L) C
  have hn := (unit (D := D)).naturality k
  simp only [comparison]
  rw [← Category.assoc, ← hcomp₁, ← hn, hcomp₂, Category.assoc,
    TransferredCoreReplacements.comparison_source]
  exact (Category.assoc _ _ _).symm

/-- Target naturality uses the actual localized R action after unit precomposition. -/
theorem comparison_target (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D) (K : SSet.{u})
    {C C' : SimplicialPresheaf.{u} D} (f : C ⟶ C') :
    localDerivedPostcomp S ((constantReplacement (D := D)).obj K) f ≫ comparison S z K C' =
      comparison S z K C ≫
        (ihom ((TransferredCoreReplacements.qReplacement S z).obj K)).map
          ((TransferredCoreReplacements.rReplacement S z).map f) := by
  have hexchange := (localDerivedEnd_laws S).2.2.2.2.1 ((unit (D := D)).app K) f
  simp only [comparison]
  rw [← Category.assoc, ← hexchange, Category.assoc,
    TransferredCoreReplacements.comparison_target]
  exact (Category.assoc _ _ _).symm

/-- The actual groupoidal-source comparison is weak, without input Kan or local-fibrancy premises. -/
theorem comparison_weak (S : I → Arrow (SimplicialPresheaf.{u} D))
    {z : D} (hz : IsTerminal z) (K : SSet.{u}) (C : SimplicialPresheaf.{u} D) :
    SSet.realizationWeakEquivalences (comparison S z K C) :=
  SSet.realizationWeakEquivalences.comp_mem _ _
    (localDerivedPrecomp_localWeak S _ (unit_originalLocalWeak S K) C)
    (TransferredCoreReplacements.comparison_weak S hz K C)

end SimplicialPresheaf.BaselineConstantCoreComparison
