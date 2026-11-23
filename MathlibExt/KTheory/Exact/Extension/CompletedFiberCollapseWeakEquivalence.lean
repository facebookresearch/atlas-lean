/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.NerveHomotopy
public import MathlibExt.KTheory.Exact.Extension.CompletedFiberWeakEquivalence
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Realization.SplitComparison
public import MathlibExt.Topology.Category.TopCat.WeakHomotopyEquivalenceHomotopy

/-!
# Weak equivalences of the original collapse and split inclusion

The original completed-fiber inclusion, collapse section and kernel identity
give weakness of the collapse and kernel maps on their whole native nerves.
The complete collapse-to-split natural Iso then gives weakness of the literal
split inclusion. The projective specialization uses only an associative unital
ring and the original projective quotient.

The middle projection, full span transport and based Q comparison have their
own remaining obligations.
-/

universe u v uRing vModule

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory

namespace AlgebraicKTheory.FixedTargetExtension.IteratedAction.Collapse

section General

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction denominatorLeftAction

/-- The actual completed inclusion, section and kernel identity make the
original collapse and kernel nerve maps weak on all components. -/
theorem collapse_and_kernelNerveMaps_mem_of_originalBase_conull
    (hBase : TopCat.weakHomotopyEquivalences
      (terminal.from (SSet.toTop.obj
        (nerve (MonoidalActionCategory (Core C) (FixedTargetExtension C X)) :
          SSet.{max u v})))) :
    SSet.realizationWeakEquivalences (nerveMap (collapseFunctor (C := C) (X := X))) ∧
      SSet.realizationWeakEquivalences (nerveMapCommonHom.{u, max u v, 0} (localizedKernelFunctor
        X)) := by
  let K : SSet.{max u v} := nerve (SInverse (Core C) (Core C))
  let N : SSet.{max u v} := nerve (iteratedLocalizedRows (C := C) (X := X))
  let V : SSet.{max u v} := nerve (localizedRows (C := C) X)
  let j : K ⟶ N :=
    nerveMapCommonHomUp.{u, max u v, 0} (completedFiberFunctor
      (AlgebraicKTheory.AuxiliaryExtension.unitRow X))
  let gamma : N ⟶ V := nerveMap (collapseFunctor (C := C) (X := X))
  let kappa : V ⟶ K := nerveMapCommonHom.{u, max u v, 0} (localizedKernelFunctor X)
  let i : V ⟶ N := nerveMap (SInverse.inclusion (Core C) (localizedRows (C := C) X))
  have hJ : SSet.realizationWeakEquivalences j :=
    completedFiberNerveMap_mem_of_originalBase_conull (C := C) (X := X)
      (AlgebraicKTheory.AuxiliaryExtension.unitRow X) hBase
  have hSection : SSet.Homotopy (i ≫ gamma) (𝟙 V) :=
    collapseInclusionNerveHomotopy (C := C) (X := X)
  have hKernel : SSet.Homotopy (j ≫ gamma ≫ kappa) (𝟙 K) :=
    collapseFiberKernelNerveHomotopy (C := C) (X := X)
  have hGamma : SSet.realizationWeakEquivalences gamma :=
    SSet.RealizationCWUpgrade.realizationWeakEquivalence_of_section_comparison
      gamma kappa i j hJ hSection hKernel
  have hTotal : SSet.realizationWeakEquivalences (j ≫ gamma ≫ kappa) := by
    let H := SSet.realizeHomotopy K K (j ≫ gamma ≫ kappa) (𝟙 K) hKernel
    change TopCat.weakHomotopyEquivalences (SSet.toTop.map (j ≫ gamma ≫ kappa))
    have hId : TopCat.weakHomotopyEquivalences (SSet.toTop.map (𝟙 K)) := by
      rw [SSet.toTop.map_id]
      exact TopCat.weakHomotopyEquivalences.id_mem (SSet.toTop.obj K)
    exact (TopCat.weakHomotopyEquivalences_iff_of_homotopy H).2 hId
  have hTotal' : SSet.realizationWeakEquivalences ((j ≫ gamma) ≫ kappa) := by
    rw [Category.assoc]
    exact hTotal
  have hJG : SSet.realizationWeakEquivalences (j ≫ gamma) :=
    SSet.realizationWeakEquivalences.comp_mem j gamma hJ hGamma
  have hKappa : SSet.realizationWeakEquivalences kappa :=
    SSet.realizationWeakEquivalences.of_precomp (j ≫ gamma) kappa hJG hTotal'
  exact ⟨hGamma, hKappa⟩

/-- The actual collapse-to-split natural Iso transfers completed-inclusion
weakness to the literal positive-first split inclusion, retaining every K component. -/
theorem splitInclusionNerveMap_mem_of_originalBase_conull
    (hBase : TopCat.weakHomotopyEquivalences
      (terminal.from (SSet.toTop.obj
        (nerve (MonoidalActionCategory (Core C) (FixedTargetExtension C X)) :
          SSet.{max u v})))) :
    SSet.realizationWeakEquivalences
      (nerveMapCommonHomUp.{u, max u v, 0} (SplitInclusion.splitLocalizedFunctor X)) := by
  let K : SSet.{max u v} := nerve (SInverse (Core C) (Core C))
  let N : SSet.{max u v} := nerve (iteratedLocalizedRows (C := C) (X := X))
  let V : SSet.{max u v} := nerve (localizedRows (C := C) X)
  let j : K ⟶ N :=
    nerveMapCommonHomUp.{u, max u v, 0} (completedFiberFunctor
      (AlgebraicKTheory.AuxiliaryExtension.unitRow X))
  let gamma : N ⟶ V := nerveMap (collapseFunctor (C := C) (X := X))
  let q : K ⟶ V := nerveMapCommonHomUp.{u, max u v, 0}
    (completedFiberFunctor (AlgebraicKTheory.AuxiliaryExtension.unitRow X) ⋙ collapseFunctor)
  let eta : K ⟶ V := nerveMapCommonHomUp.{u, max u v, 0} (SplitInclusion.splitLocalizedFunctor X)
  have hJ : SSet.realizationWeakEquivalences j :=
    completedFiberNerveMap_mem_of_originalBase_conull (C := C) (X := X)
      (AlgebraicKTheory.AuxiliaryExtension.unitRow X) hBase
  have hGamma : SSet.realizationWeakEquivalences gamma :=
    (collapse_and_kernelNerveMaps_mem_of_originalBase_conull (C := C) (X := X) hBase).1
  have hComposite : SSet.realizationWeakEquivalences (j ≫ gamma) :=
    SSet.realizationWeakEquivalences.comp_mem j gamma hJ hGamma
  have hMap : j ≫ gamma = q :=
    nerveMapCommonHomUp_nerveMap_comp.{u, max u v, 0}
      (completedFiberFunctor (AlgebraicKTheory.AuxiliaryExtension.unitRow X)) collapseFunctor
  have hQ : SSet.realizationWeakEquivalences q := hMap ▸ hComposite
  have hSimplicial : SSet.Homotopy q eta :=
    NatTrans.nerveHomotopyCommonHomUp.{u, max u v, 0} (collapseFiberEtaNatIso (C := C) (X := X)).hom
  let H := SSet.realizeHomotopy K V q eta hSimplicial
  change TopCat.weakHomotopyEquivalences (SSet.toTop.map eta)
  exact (TopCat.weakHomotopyEquivalences_iff_of_homotopy H).1 hQ

end General

section Projective

attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction denominatorLeftAction

/-- For every associative unital ring and original projective quotient,
the actual collapse, kernel and split maps are weak on their complete native spaces. -/
theorem projective_collapse_kernel_splitNerveMaps_mem_realizationWeakEquivalences
    {R : Type uRing} [Ring R] (X : FGProjectiveCat.{vModule} R) :
    SSet.realizationWeakEquivalences
        (nerveMap (collapseFunctor (C := FGProjectiveCat.{vModule} R) (X := X))) ∧
      SSet.realizationWeakEquivalences (nerveMapCommonHom.{max uRing (vModule + 1), max uRing
        (vModule + 1), 0} (localizedKernelFunctor X)) ∧
        SSet.realizationWeakEquivalences
          (nerveMapCommonHomUp.{max uRing (vModule + 1), max uRing (vModule + 1), 0}
            (SplitInclusion.splitLocalizedFunctor X)) := by
  have hBase := AlgebraicKTheory.AuxiliaryExtension.projectiveAuxiliary_realization_conull X
  have hGK := collapse_and_kernelNerveMaps_mem_of_originalBase_conull
    (C := FGProjectiveCat.{vModule} R) (X := X) hBase
  have hEta := splitInclusionNerveMap_mem_of_originalBase_conull
    (C := FGProjectiveCat.{vModule} R) (X := X) hBase
  exact ⟨hGK.1, hGK.2, hEta⟩

end Projective

end AlgebraicKTheory.FixedTargetExtension.IteratedAction.Collapse

end
