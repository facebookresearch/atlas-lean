/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.SelectedDayInstances
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.SphereOperatorCategory
public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.DayFunctorClosedSymmetric
public import MathlibExt.CategoryTheory.Monoidal.Mod.Closed
public import MathlibExt.CategoryTheory.Monoidal.Mod.DayEvaluation
public import MathlibExt.Topology.Category.PointedCGWH.EnrichedMappingEnds
public import MathlibExt.CategoryTheory.Monoidal.Mod.EquivalenceFunction

/-!
# Closed structure and free-module adjunctions for symmetric spectra

Transports internal Hom from free sphere modules through the module/operator equivalence.
Records the balanced smash adjunction and contravariant precomposition maps using the
symmetric-sequence closed, equalizer and coequalizer structures.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory Limits
open scoped MonoidalClosed CategoryTheory.MonObj

namespace NativeOmegaPreparation.SymmetricFunction
attribute [local instance] PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits

/-- The actual ordinary Day end adjunction supplies the selected symmetric-sequence closed
structure. -/
@[instance_reducible]
def sequenceClosed : MonoidalClosed PointedCGWH.SymmetricSequence.{u, v} :=
  inferInstance

/-- The original full Day-wrapper equivalence transports the actual pointwise sequence
coequalizers. -/
theorem sequenceCoequalizers : HasCoequalizers PointedCGWH.SymmetricSequence.{u, v} :=
  Adjunction.hasColimitsOfShape_of_equivalence
    (MonoidalCategory.DayFunctor.equiv Operad.SmallFinBijGroupoid PointedCGWH.{u, v}).functor

/-- The original full Day-wrapper equivalence transports the actual pointwise sequence
equalizers. -/
theorem sequenceEqualizers : HasEqualizers PointedCGWH.SymmetricSequence.{u, v} :=
  Adjunction.hasLimitsOfShape_of_equivalence
    (MonoidalCategory.DayFunctor.equiv Operad.SmallFinBijGroupoid PointedCGWH.{u, v}).functor

attribute [local instance] sequenceClosed sequenceCoequalizers sequenceEqualizers

/-- The original left sphere Day-module carrier, with its actual selected monoid structure. -/
abbrev Module := CategoryTheory.Mod
  (C := PointedCGWH.SymmetricSequence.{u, v}) PointedCGWH.SymmetricSequence.{u, v}
    PointedCGWH.sphereSequence.{u, v}

/-- The complete existing carrier equivalence retains every original operator Hom action and module
morphism. -/
abbrev carrierEquivalence : Module.{u, v} ≌
    EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v} :=
  PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}

/-- The original free sphere module uses the unchanged ordinary free diagram, Day wrapper and module
free. -/
def freeObject (n : Operad.SmallFinBijGroupoid) (M : PointedCGWH.{u, v}) : Module.{u, v} :=
  (Mod.dayFreeAt PointedCGWH.sphereSequence.{u, v} n).obj M

/-- The original full module internal Hom and both actual carrier whiskering functors provide lawful
source and target variance on the native carrier. -/
def sourceFunctor :
    (CategoryTheory.Mod (C := PointedCGWH.SymmetricSequence.{u, v})
      PointedCGWH.SymmetricSequence.{u, v} PointedCGWH.sphereSequence.{u, v})ᵒᵖ ⥤
    (EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v} ⥤
      EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}) :=
  ModuleFunctionTransport.sourceFunctor PointedCGWH.sphereSequenceCommMon.{u, v}
    carrierEquivalence.{u, v}

/-- The actual symmetric function spectrum from the original free source is the existing module
internal Hom carried through the full original carrier equivalence. -/
def functor (n : Operad.SmallFinBijGroupoid) (M : PointedCGWH.{u, v}) :
    EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v} ⥤
      EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v} :=
  sourceFunctor.{u, v}.obj (.op (freeObject n M))

/-- The actual left source functor is balanced smash with that unchanged original free module, on
the same complete native carrier. -/
def smashFunctor (n : Operad.SmallFinBijGroupoid) (M : PointedCGWH.{u, v}) :
    EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v} ⥤
      EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v} :=
  carrierEquivalence.{u, v}.inverse ⋙
    (Mod.relativeTensor PointedCGWH.sphereSequenceCommMon.{u, v}).obj (freeObject n M) ⋙
      carrierEquivalence.{u, v}.functor

/-- The existing original balanced module adjunction and both original carrier adjunctions give the
actual free-smash/function-spectrum adjunction. -/
def adjunction (n : Operad.SmallFinBijGroupoid) (M : PointedCGWH.{u, v}) :
    smashFunctor n M ⊣ functor n M :=
  ModuleFunctionTransport.sourceAdjunction PointedCGWH.sphereSequenceCommMon.{u, v}
    carrierEquivalence.{u, v} (freeObject n M)

/-- Every unchanged original free-source map acts contravariantly through the existing full module
internal-Hom transformation. -/
def precompose {n k : Operad.SmallFinBijGroupoid} {M N : PointedCGWH.{u, v}}
    (f : (Mod.dayFreeAt PointedCGWH.sphereSequence.{u, v} k).obj N ⟶
      (Mod.dayFreeAt PointedCGWH.sphereSequence.{u, v} n).obj M) :
    functor n M ⟶ functor k N :=
  sourceFunctor.{u, v}.map f.op

end NativeOmegaPreparation.SymmetricFunction
