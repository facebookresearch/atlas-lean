/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.RightTransfer
public import MathlibExt.AlgebraicTopology.ModelCategory.MonoidAxiom
public import MathlibExt.AlgebraicTopology.ModelCategory.MonoidalQuillen
public import MathlibExt.CategoryTheory.SmallObject.Image
public import MathlibExt.CategoryTheory.SmallObject.CellularNormalization.Closure
public import MathlibExt.CategoryTheory.Monoidal.Mod.ColimitsFree
public import MathlibExt.CategoryTheory.Monoidal.RightModuleFree
public import MathlibExt.CategoryTheory.Monoidal.RightModuleLimits
public import MathlibExt.CategoryTheory.Monoidal.Bimod.Free
public import MathlibExt.CategoryTheory.Monoidal.Bimod.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Preorder

/-!
# Full transferred models on the existing internal module categories

The actual free module images of the original I and J sets generate the model.
For every J cell its underlying free map is a tensor of that same original
trivial cofibration. Forgetting preserves the entire source cell diagram and
its endpoint cocone, so the monoid axiom proves acyclicity. For a cofibrant
scalar, the pushout-product axiom instead proves that all these maps are
trivial cofibrations. Uniform relative source smallness supplies the two full
small-object arguments and their common regular cardinal.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w u v

open CategoryTheory Limits MonoidalCategory BraidedCategory MorphismProperty MonoidalOpposite
open CategoryTheory.SmallObject
open scoped MonoidalCategory

namespace HomotopicalAlgebra.ModuleTransfer

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [HasColimitsOfSize.{w, w} C]

local instance : (CellularNormalization.cellularClosure.{w, w}
    (tensorTrivialCofibrationsRight C)).IsStableUnderCobaseChange := by
  let E : Discrete PEmpty.{w + 1} ⥤ C := Discrete.functor (fun i => i.elim)
  exact (CellularNormalization.cellularClosure_stable.{w, w}
    (tensorTrivialCofibrationsRight C) (colimit.cocone E) (colimit.cocone E)
    (colimit.isColimit E) (colimit.isColimit E)).1
local instance : (CellularNormalization.cellularClosure.{w, w}
    (tensorTrivialCofibrationsRight C)).IsStableUnderCoproducts.{w} := by
  let E : Discrete PEmpty.{w + 1} ⥤ C := Discrete.functor (fun i => i.elim)
  exact (CellularNormalization.cellularClosure_stable.{w, w}
    (tensorTrivialCofibrationsRight C) (colimit.cocone E) (colimit.cocone E)
    (colimit.isColimit E) (colimit.isColimit E)).2.1
local instance : (CellularNormalization.cellularClosure.{w, w}
    (tensorTrivialCofibrationsRight C)).IsStableUnderTransfiniteComposition.{w} := by
  let E : Discrete PEmpty.{w + 1} ⥤ C := Discrete.functor (fun i => i.elim)
  exact (CellularNormalization.cellularClosure_stable.{w, w}
    (tensorTrivialCofibrationsRight C) (colimit.cocone E) (colimit.cocone E)
    (colimit.isColimit E) (colimit.isColimit E)).2.2

local instance : (CellularNormalization.cellularClosure.{w, w}
    (tensorTrivialCofibrationsRight C)).RespectsIso := by
  apply RespectsIso.of_respects_arrow_iso
  intro a b e ha
  obtain ⟨T, _, _, _, _, ⟨d⟩⟩ := (transfiniteCompositions_iff _ a.hom).mp ha
  exact transfiniteCompositionsOfShape_le_transfiniteCompositions _ T b.hom ⟨d.ofArrowIso e⟩

omit [MonoidalClosed C] [HasColimitsOfSize.{w, w} C] in
/-- A left scalar tensor of an original trivial cofibration is in the literal tensor-cell closure. -/
theorem whiskerLeft_mem_tensorCellularClass (A : C) {X Y : C} (j : X ⟶ Y)
    (hj : trivialCofibrations C j) :
    CellularNormalization.cellularClosure.{w, w} (tensorTrivialCofibrationsRight C) (A ◁ j) := by
  have hRight : CellularNormalization.cellularClosure.{w, w} (tensorTrivialCofibrationsRight C) (j ▷ A) :=
    ((tensorTrivialCofibrationsRight C).le_coproducts.trans
      ((tensorTrivialCofibrationsRight C).coproducts.{w}).le_pushouts).trans
        ((tensorTrivialCofibrationsRight C).coproducts.{w}).pushouts.le_transfiniteCompositions _
      (whiskerRight_mem_tensorTrivialCofibrationsRight C j hj A)
  let e : Arrow.mk (j ▷ A) ≅ Arrow.mk (A ◁ j) :=
    Arrow.isoMk (β_ X A) (β_ Y A) (braiding_naturality_left j A).symm
  exact ((CellularNormalization.cellularClosure.{w, w}
    (tensorTrivialCofibrationsRight C)).arrow_mk_iso_iff e).mp hRight

variable (A : Mon C)

/-- The original free-I or free-J family on the existing left-module carrier. -/
abbrev leftGenerators (P : MorphismProperty C) : MorphismProperty (Mod C A.X) :=
  P.strictMap (Mod.free A.X)

omit [ModelCategory C] [SymmetricCategory C] in
/-- The actual module forgetful functor preserves all required source colimits. -/
theorem leftForgetPreservesColimits : PreservesColimitsOfSize.{w, w} (Mod.forget (D := C) A.X) := by
  let : CreatesColimitsOfSize.{w, w} (Mod.forget (D := C) A.X) := Mod.forgetCreatesColimits.{w} A.X
  let : HasColimitsOfSize.{w, w} (Mod C A.X) := Mod.hasColimits.{w} A.X
  infer_instance

omit [MonoidalClosed C] [HasColimitsOfSize.{w, w} C] in
/-- Every original free-J generator forgets into the actual source tensor-cell closure. -/
theorem leftFreeJ_generators_tensorCellular (J : MorphismProperty C)
    (hJ : J.rlp = fibrations C) :
    leftGenerators A J ≤ (CellularNormalization.cellularClosure.{w, w}
      (tensorTrivialCofibrationsRight C)).inverseImage (Mod.forget (D := C) A.X) := by
  intro X Y f hf
  cases hf with
  | map hj =>
    change CellularNormalization.cellularClosure.{w, w} (tensorTrivialCofibrationsRight C) (A.X ◁ _)
    have hSource := J.le_llp_rlp
    rw [hJ, fibrations_llp] at hSource
    exact whiskerLeft_mem_tensorCellularClass.{w} A.X _ (hSource _ hj)

/-- Forget the actual free-J SOA cells, then apply the original source monoid axiom. -/
theorem leftFreeJLeft_underlying_weak [MonoidAxiom.{w} C]
    (J : MorphismProperty C) (hJ : J.rlp = fibrations C)
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [(leftGenerators A J).IsCardinalForSmallObjectArgument κ] :
    (leftGenerators A J).rlp.llp ≤ (weakEquivalences C).inverseImage (Mod.forget (D := C) A.X) := by
  let : PreservesColimitsOfSize.{w, w} (Mod.forget (D := C) A.X) := leftForgetPreservesColimits.{w} A
  let : CategoryTheory.Limits.PreservesWellOrderContinuousOfShape κ.ord.ToType
      (Mod.forget (D := C) A.X) := by
    refine CategoryTheory.Limits.PreservesWellOrderContinuousOfShape.mk
      (G := Mod.forget (D := C) A.X) (J := κ.ord.ToType) ?_
    intro j _
    infer_instance
  apply rlp_llp_le_inverseImage_of_cardinal_cells (leftGenerators A J) (weakEquivalences C)
    (Mod.forget (D := C) A.X) κ
  intro X Y f c
  exact MonoidAxiom.cellularClosure_le_weakEquivalences _
    (c.map_mem_of_le (Mod.forget (D := C) A.X) (leftGenerators A J)
      (CellularNormalization.cellularClosure.{w, w} (tensorTrivialCofibrationsRight C))
      (leftFreeJ_generators_tensorCellular.{w} A J hJ))

variable [HasLimitsOfSize.{w, w} C] [LocallySmall.{w} C]
  (I J : MorphismProperty C) [I.IsSmall.{w}] [J.IsSmall.{w}]
  (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)
  (hSourceI : UniformRelativeSourceSmallness.{w} (leftGenerators A I))
  (hSourceJ : UniformRelativeSourceSmallness.{w} (leftGenerators A J))

/-- The full model on the existing left-module category from the original monoid axiom and source smallness. -/
def fullLeftModuleModelTransfer [MonoidAxiom.{w} C] :
    RightTransfer.FullModelTransfer (Mod.free A.X) (Mod.forget (D := C) A.X) I J hSourceI hSourceJ := by
  letI : HasLimitsOfSize.{w, w} (Mod C A.X) := Mod.hasLimits.{w} A.X
  letI : HasColimitsOfSize.{w, w} (Mod C A.X) := Mod.hasColimits.{w} A.X
  letI : (Mod.forget (D := C) A.X).Faithful :=
    { map_injective := fun h => Mod.hom_ext _ _ h }
  letI : LocallySmall.{w} (Mod C A.X) := locallySmall_of_faithful (Mod.forget (D := C) A.X)
  exact RightTransfer.fullModelTransfer (Mod.free A.X) (Mod.forget (D := C) A.X) (Mod.freeForgetAdjunction A.X)
    I J hI hJ hSourceI hSourceJ (by
      intro κ _ _ _
      exact leftFreeJLeft_underlying_weak.{w} A J hJ κ)

/-- The actual original right free-I or free-J family on the existing right-action carrier. -/
abbrev rightGenerators (P : MorphismProperty C) : MorphismProperty (RightModuleFree.Carrier A.X) :=
  P.strictMap (RightModuleFree.functor A.X)

omit [MonoidalClosed C] [HasColimitsOfSize.{w, w} C] [HasLimitsOfSize.{w, w} C]
  [LocallySmall.{w} C] [SymmetricCategory C] [J.IsSmall.{w}] in
/-- Each original free-J right-module map is a literal tensor-trivial-cofibration cell. -/
theorem rightFreeJ_generators_tensorCellular (hJ : J.rlp = fibrations C) :
    rightGenerators A J ≤ (CellularNormalization.cellularClosure.{w, w}
      (tensorTrivialCofibrationsRight C)).inverseImage (Mod.forget (D := C) (mop A.X)) := by
  intro X Y f hf
  cases hf with
  | map hj =>
    change CellularNormalization.cellularClosure.{w, w} (tensorTrivialCofibrationsRight C) (_ ▷ A.X)
    have hSource := J.le_llp_rlp
    rw [hJ, fibrations_llp] at hSource
    exact ((tensorTrivialCofibrationsRight C).le_coproducts.trans
      ((tensorTrivialCofibrationsRight C).coproducts.{w}).le_pushouts).trans
        ((tensorTrivialCofibrationsRight C).coproducts.{w}).pushouts.le_transfiniteCompositions _
      (whiskerRight_mem_tensorTrivialCofibrationsRight C _ (hSource _ hj) A.X)

omit [HasLimitsOfSize.{w, w} C] [LocallySmall.{w} C] [J.IsSmall.{w}] in
/-- The original monoid axiom gives the entire free-J right-module left class underlying weakness. -/
theorem rightFreeJLeft_underlying_weak [MonoidAxiom.{w} C]
    (hJ : J.rlp = fibrations C)
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [(rightGenerators A J).IsCardinalForSmallObjectArgument κ] :
    (rightGenerators A J).rlp.llp ≤ (weakEquivalences C).inverseImage (Mod.forget (D := C) (mop A.X)) := by
  let : PreservesColimitsOfSize.{w, w} (Mod.forget (D := C) (mop A.X)) :=
    RightModuleFree.forgetPreservesColimits.{w} A.X
  let : CategoryTheory.Limits.PreservesWellOrderContinuousOfShape κ.ord.ToType
      (Mod.forget (D := C) (mop A.X)) := by
    refine CategoryTheory.Limits.PreservesWellOrderContinuousOfShape.mk
      (G := Mod.forget (D := C) (mop A.X)) (J := κ.ord.ToType) ?_
    intro j _
    infer_instance
  apply rlp_llp_le_inverseImage_of_cardinal_cells (rightGenerators A J) (weakEquivalences C)
    (Mod.forget (D := C) (mop A.X)) κ
  intro X Y f c
  exact MonoidAxiom.cellularClosure_le_weakEquivalences _
    (c.map_mem_of_le (Mod.forget (D := C) (mop A.X)) (rightGenerators A J)
      (CellularNormalization.cellularClosure.{w, w} (tensorTrivialCofibrationsRight C))
      (rightFreeJ_generators_tensorCellular.{w} A J hJ))

/-- Full right-module transfer on the original right-action carrier, from original source hypotheses. -/
def fullRightModuleModelTransfer [MonoidAxiom.{w} C]
    (hRightSourceI : UniformRelativeSourceSmallness.{w} (rightGenerators A I))
    (hRightSourceJ : UniformRelativeSourceSmallness.{w} (rightGenerators A J)) :
    RightTransfer.FullModelTransfer (RightModuleFree.functor A.X) (Mod.forget (D := C) (mop A.X))
      I J hRightSourceI hRightSourceJ := by
  letI : HasLimitsOfSize.{w, w} (RightModuleFree.Carrier A.X) := RightModuleFree.hasLimits.{w} A.X
  letI : HasColimitsOfSize.{w, w} (RightModuleFree.Carrier A.X) := RightModuleFree.hasColimits.{w} A.X
  letI : LocallySmall.{w} (RightModuleFree.Carrier A.X) :=
    locallySmall_of_faithful (Mod.forget (D := C) (mop A.X))
  exact RightTransfer.fullModelTransfer (RightModuleFree.functor A.X) (Mod.forget (D := C) (mop A.X))
    (RightModuleFree.adjunction A.X) I J hI hJ hRightSourceI hRightSourceJ (by
      intro κ _ _ _
      exact rightFreeJLeft_underlying_weak.{w} A J hJ κ)

omit [HasColimitsOfSize.{w, w} C] [HasLimitsOfSize.{w, w} C] [LocallySmall.{w} C] in
/-- A cofibrant scalar sends the actual free-J generators to underlying trivial cofibrations. -/
theorem leftFreeJ_generators_trivial [IsClosedSymmetricMonoidalModelCategory C] [IsCofibrant A.X]
    (J : MorphismProperty C) (hJ : J.rlp = fibrations C) :
    leftGenerators A J ≤ (trivialCofibrations C).inverseImage (Mod.forget (D := C) A.X) := by
  intro X Y f hf
  cases hf with
  | map hj =>
    change trivialCofibrations C (A.X ◁ _)
    have hSource := J.le_llp_rlp
    rw [hJ, fibrations_llp] at hSource
    exact (ihomAdjunction_isQuillenAdjunction_of_isCofibrant A.X).preservesTrivialCofibrations _ (hSource _ hj)

omit [HasLimitsOfSize.{w, w} C] [LocallySmall.{w} C] in
/-- Original free-J cells are underlying trivial cofibrations for a cofibrant scalar, without a monoid axiom. -/
theorem leftFreeJLeft_underlying_trivial [IsClosedSymmetricMonoidalModelCategory C] [IsCofibrant A.X]
    (J : MorphismProperty C) (hJ : J.rlp = fibrations C)
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [(leftGenerators A J).IsCardinalForSmallObjectArgument κ] :
    (leftGenerators A J).rlp.llp ≤ (trivialCofibrations C).inverseImage (Mod.forget (D := C) A.X) := by
  let : PreservesColimitsOfSize.{w, w} (Mod.forget (D := C) A.X) := leftForgetPreservesColimits.{w} A
  let : CategoryTheory.Limits.PreservesWellOrderContinuousOfShape κ.ord.ToType
      (Mod.forget (D := C) A.X) := by
    refine CategoryTheory.Limits.PreservesWellOrderContinuousOfShape.mk
      (G := Mod.forget (D := C) A.X) (J := κ.ord.ToType) ?_
    intro j _
    infer_instance
  let : (trivialCofibrations C).IsStableUnderCoproducts.{w} := by
    rw [← fibrations_llp C]
    infer_instance
  let : (trivialCofibrations C).IsStableUnderCobaseChange := by
    rw [← fibrations_llp C]
    infer_instance
  let : (trivialCofibrations C).IsStableUnderTransfiniteCompositionOfShape κ.ord.ToType := by
    rw [← fibrations_llp C]
    infer_instance
  let : (trivialCofibrations C).IsStableUnderRetracts := by
    rw [← fibrations_llp C]
    infer_instance
  exact rlp_llp_le_inverseImage_of_cardinal_closure (leftGenerators A J) (trivialCofibrations C)
    (Mod.forget (D := C) A.X) κ (leftFreeJ_generators_trivial A J hJ)

/-- The full original left-module model for a cofibrant scalar needs no global monoid axiom. -/
def fullLeftModuleModelTransferOfCofibrantScalar
    [IsClosedSymmetricMonoidalModelCategory C] [IsCofibrant A.X] :
    RightTransfer.FullModelTransfer (Mod.free A.X) (Mod.forget (D := C) A.X) I J hSourceI hSourceJ := by
  letI : HasLimitsOfSize.{w, w} (Mod C A.X) := Mod.hasLimits.{w} A.X
  letI : HasColimitsOfSize.{w, w} (Mod C A.X) := Mod.hasColimits.{w} A.X
  letI : (Mod.forget (D := C) A.X).Faithful :=
    { map_injective := fun h => Mod.hom_ext _ _ h }
  letI : LocallySmall.{w} (Mod C A.X) := locallySmall_of_faithful (Mod.forget (D := C) A.X)
  exact RightTransfer.fullModelTransfer (Mod.free A.X) (Mod.forget (D := C) A.X) (Mod.freeForgetAdjunction A.X)
    I J hI hJ hSourceI hSourceJ (by
      intro κ _ _ _ X Y f hf
      exact (leftFreeJLeft_underlying_trivial.{w} A J hJ κ f hf).2)

omit [HasColimitsOfSize.{w, w} C] [HasLimitsOfSize.{w, w} C] [LocallySmall.{w} C] in
/-- The original free right-module generator is trivial for a cofibrant scalar. -/
theorem rightFreeJ_generators_trivial [IsClosedSymmetricMonoidalModelCategory C] [IsCofibrant A.X]
    (J : MorphismProperty C) (hJ : J.rlp = fibrations C) :
    rightGenerators A J ≤ (trivialCofibrations C).inverseImage (Mod.forget (D := C) (mop A.X)) := by
  intro X Y f hf
  cases hf with
  | @map X Y j hj =>
    change trivialCofibrations C (j ▷ A.X)
    have hSource := J.le_llp_rlp
    rw [hJ, fibrations_llp] at hSource
    have hLeft : trivialCofibrations C (A.X ◁ j) :=
      (ihomAdjunction_isQuillenAdjunction_of_isCofibrant A.X).preservesTrivialCofibrations j (hSource j hj)
    let e : Arrow.mk (A.X ◁ j) ≅ Arrow.mk (j ▷ A.X) :=
      Arrow.isoMk (β_ A.X X) (β_ A.X Y) (braiding_naturality_right A.X j).symm
    exact ((trivialCofibrations C).arrow_mk_iso_iff e).mp hLeft

omit [HasLimitsOfSize.{w, w} C] [LocallySmall.{w} C] in
/-- The actual original free-J right-module cells are trivial without a global monoid axiom. -/
theorem rightFreeJLeft_underlying_trivial [IsClosedSymmetricMonoidalModelCategory C] [IsCofibrant A.X]
    (J : MorphismProperty C) (hJ : J.rlp = fibrations C)
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [(rightGenerators A J).IsCardinalForSmallObjectArgument κ] :
    (rightGenerators A J).rlp.llp ≤ (trivialCofibrations C).inverseImage (Mod.forget (D := C) (mop A.X)) := by
  let : PreservesColimitsOfSize.{w, w} (Mod.forget (D := C) (mop A.X)) :=
    RightModuleFree.forgetPreservesColimits.{w} A.X
  let : CategoryTheory.Limits.PreservesWellOrderContinuousOfShape κ.ord.ToType
      (Mod.forget (D := C) (mop A.X)) := by
    refine CategoryTheory.Limits.PreservesWellOrderContinuousOfShape.mk
      (G := Mod.forget (D := C) (mop A.X)) (J := κ.ord.ToType) ?_
    intro j _
    infer_instance
  let : (trivialCofibrations C).IsStableUnderCoproducts.{w} := by
    rw [← fibrations_llp C]
    infer_instance
  let : (trivialCofibrations C).IsStableUnderCobaseChange := by
    rw [← fibrations_llp C]
    infer_instance
  let : (trivialCofibrations C).IsStableUnderTransfiniteCompositionOfShape κ.ord.ToType := by
    rw [← fibrations_llp C]
    infer_instance
  let : (trivialCofibrations C).IsStableUnderRetracts := by
    rw [← fibrations_llp C]
    infer_instance
  exact rlp_llp_le_inverseImage_of_cardinal_closure (rightGenerators A J) (trivialCofibrations C)
    (Mod.forget (D := C) (mop A.X)) κ (rightFreeJ_generators_trivial A J hJ)

/-- Full transfer on the existing right-module carrier from a cofibrant scalar, without a monoid axiom. -/
def fullRightModuleModelTransferOfCofibrantScalar
    [IsClosedSymmetricMonoidalModelCategory C] [IsCofibrant A.X]
    (hRightSourceI : UniformRelativeSourceSmallness.{w} (rightGenerators A I))
    (hRightSourceJ : UniformRelativeSourceSmallness.{w} (rightGenerators A J)) :
    RightTransfer.FullModelTransfer (RightModuleFree.functor A.X) (Mod.forget (D := C) (mop A.X))
      I J hRightSourceI hRightSourceJ := by
  letI : HasLimitsOfSize.{w, w} (RightModuleFree.Carrier A.X) := RightModuleFree.hasLimits.{w} A.X
  letI : HasColimitsOfSize.{w, w} (RightModuleFree.Carrier A.X) := RightModuleFree.hasColimits.{w} A.X
  letI : LocallySmall.{w} (RightModuleFree.Carrier A.X) :=
    locallySmall_of_faithful (Mod.forget (D := C) (mop A.X))
  exact RightTransfer.fullModelTransfer (RightModuleFree.functor A.X) (Mod.forget (D := C) (mop A.X))
    (RightModuleFree.adjunction A.X) I J hI hJ hRightSourceI hRightSourceJ (by
      intro κ _ _ _ X Y f hf
      exact (rightFreeJLeft_underlying_trivial.{w} A J hJ κ f hf).2)

/-- The literal original free-I or free-J family on the existing bimodule carrier. -/
abbrev bimoduleGenerators (B : Mon C) (P : MorphismProperty C) : MorphismProperty (Bimod A B) :=
  P.strictMap (Bimod.free A B)

omit [MonoidalClosed C] [HasLimitsOfSize.{w, w} C] [HasColimitsOfSize.{w, w} C] [LocallySmall.{w} C] in
/-- The original two-sided free-J tensor is in the literal source monoid-axiom closure. -/
theorem bimoduleFreeJ_generators_tensorCellular (B : Mon C)
    (J : MorphismProperty C) (hJ : J.rlp = fibrations C) :
    bimoduleGenerators A B J ≤ (CellularNormalization.cellularClosure.{w, w}
      (tensorTrivialCofibrationsRight C)).inverseImage (Bimod.forget (B := B) A) := by
  intro X Y f hf
  cases hf with
  | @map X Y j hj =>
    change CellularNormalization.cellularClosure.{w, w}
      (tensorTrivialCofibrationsRight C) ((A.X ◁ j) ▷ B.X)
    have hSource := J.le_llp_rlp
    rw [hJ, fibrations_llp] at hSource
    have hRight : CellularNormalization.cellularClosure.{w, w}
        (tensorTrivialCofibrationsRight C) (j ▷ (A.X ⊗ B.X)) :=
      ((tensorTrivialCofibrationsRight C).le_coproducts.trans
        ((tensorTrivialCofibrationsRight C).coproducts.{w}).le_pushouts).trans
          ((tensorTrivialCofibrationsRight C).coproducts.{w}).pushouts.le_transfiniteCompositions _
        (whiskerRight_mem_tensorTrivialCofibrationsRight C j (hSource j hj) (A.X ⊗ B.X))
    let e : Arrow.mk ((A.X ◁ j) ▷ B.X) ≅ Arrow.mk (j ▷ (A.X ⊗ B.X)) :=
      Arrow.isoMk ((tensorRight B.X).mapIso (β_ A.X X) ≪≫ α_ X A.X B.X)
        ((tensorRight B.X).mapIso (β_ A.X Y) ≪≫ α_ Y A.X B.X) (by
          change (((β_ A.X X).hom ▷ B.X) ≫ (α_ X A.X B.X).hom) ≫ (j ▷ (A.X ⊗ B.X)) =
            ((A.X ◁ j) ▷ B.X) ≫ ((β_ A.X Y).hom ▷ B.X) ≫ (α_ Y A.X B.X).hom
          rw [Category.assoc]
          rw [← associator_naturality_left j A.X B.X, ← Category.assoc, ← comp_whiskerRight,
            ← braiding_naturality_right A.X j, comp_whiskerRight, Category.assoc])
    exact ((CellularNormalization.cellularClosure.{w, w}
      (tensorTrivialCofibrationsRight C)).arrow_mk_iso_iff e).mpr hRight

omit [HasLimitsOfSize.{w, w} C] [LocallySmall.{w} C] in
/-- The original monoid axiom proves weakness of every whole actual free-J bimodule cell. -/
theorem bimoduleFreeJLeft_underlying_weak [MonoidAxiom.{w} C] (B : Mon C)
    (J : MorphismProperty C) (hJ : J.rlp = fibrations C)
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [(bimoduleGenerators A B J).IsCardinalForSmallObjectArgument κ] :
    (bimoduleGenerators A B J).rlp.llp ≤ (weakEquivalences C).inverseImage (Bimod.forget (B := B) A) := by
  let : PreservesColimitsOfSize.{w, w} (Bimod.forget (B := B) A) := inferInstance
  let : CategoryTheory.Limits.PreservesWellOrderContinuousOfShape κ.ord.ToType
      (Bimod.forget (B := B) A) := by
    refine CategoryTheory.Limits.PreservesWellOrderContinuousOfShape.mk
      (G := Bimod.forget (B := B) A) (J := κ.ord.ToType) ?_
    intro j _
    infer_instance
  apply rlp_llp_le_inverseImage_of_cardinal_cells (bimoduleGenerators A B J) (weakEquivalences C)
    (Bimod.forget (B := B) A) κ
  intro X Y f c
  exact MonoidAxiom.cellularClosure_le_weakEquivalences _
    (c.map_mem_of_le (Bimod.forget (B := B) A) (bimoduleGenerators A B J)
      (CellularNormalization.cellularClosure.{w, w} (tensorTrivialCofibrationsRight C))
      (bimoduleFreeJ_generators_tensorCellular.{w} A B J hJ))

/-- Full transferred model on the existing bimodules, from the actual tensor monad source conditions. -/
def fullBimoduleModelTransfer [MonoidAxiom.{w} C] (B : Mon C)
    (hBimoduleSourceI : UniformRelativeSourceSmallness.{w} (bimoduleGenerators A B I))
    (hBimoduleSourceJ : UniformRelativeSourceSmallness.{w} (bimoduleGenerators A B J)) :
    RightTransfer.FullModelTransfer (Bimod.free A B) (Bimod.forget (B := B) A)
      I J hBimoduleSourceI hBimoduleSourceJ := by
  letI : HasLimitsOfSize.{w, w} (Bimod A B) := by apply Bimod.hasLimits
  letI : HasColimitsOfSize.{w, w} (Bimod A B) := by apply Bimod.hasColimits
  letI : LocallySmall.{w} (Bimod A B) := locallySmall_of_faithful (Bimod.forget (B := B) A)
  exact RightTransfer.fullModelTransfer (Bimod.free A B) (Bimod.forget (B := B) A)
    (Bimod.freeForgetAdjunction A B) I J hI hJ hBimoduleSourceI hBimoduleSourceJ (by
      intro κ _ _ _
      exact bimoduleFreeJLeft_underlying_weak.{w} A B J hJ κ)

omit [HasLimitsOfSize.{w, w} C] [HasColimitsOfSize.{w, w} C] [LocallySmall.{w} C] in
/-- A cofibrant actual paired coefficient makes each original free-J bimodule generator trivial. -/
theorem bimoduleFreeJ_generators_trivial [IsClosedSymmetricMonoidalModelCategory C] (B : Mon C)
    [IsCofibrant (A.X ⊗ B.X)] (J : MorphismProperty C) (hJ : J.rlp = fibrations C) :
    bimoduleGenerators A B J ≤ (trivialCofibrations C).inverseImage (Bimod.forget (B := B) A) := by
  intro X Y f hf
  cases hf with
  | @map X Y j hj =>
    change trivialCofibrations C ((A.X ◁ j) ▷ B.X)
    have hSource := J.le_llp_rlp
    rw [hJ, fibrations_llp] at hSource
    have hLeft : trivialCofibrations C ((A.X ⊗ B.X) ◁ j) :=
      (ihomAdjunction_isQuillenAdjunction_of_isCofibrant (A.X ⊗ B.X)).preservesTrivialCofibrations
        j (hSource j hj)
    let p : Arrow.mk ((A.X ⊗ B.X) ◁ j) ≅ Arrow.mk (j ▷ (A.X ⊗ B.X)) :=
      Arrow.isoMk (β_ (A.X ⊗ B.X) X) (β_ (A.X ⊗ B.X) Y)
        (braiding_naturality_right (A.X ⊗ B.X) j).symm
    have hRight : trivialCofibrations C (j ▷ (A.X ⊗ B.X)) :=
      ((trivialCofibrations C).arrow_mk_iso_iff p).mp hLeft
    let e : Arrow.mk ((A.X ◁ j) ▷ B.X) ≅ Arrow.mk (j ▷ (A.X ⊗ B.X)) :=
      Arrow.isoMk ((tensorRight B.X).mapIso (β_ A.X X) ≪≫ α_ X A.X B.X)
        ((tensorRight B.X).mapIso (β_ A.X Y) ≪≫ α_ Y A.X B.X) (by
          change (((β_ A.X X).hom ▷ B.X) ≫ (α_ X A.X B.X).hom) ≫ (j ▷ (A.X ⊗ B.X)) =
            ((A.X ◁ j) ▷ B.X) ≫ ((β_ A.X Y).hom ▷ B.X) ≫ (α_ Y A.X B.X).hom
          rw [Category.assoc]
          rw [← associator_naturality_left j A.X B.X, ← Category.assoc, ← comp_whiskerRight,
            ← braiding_naturality_right A.X j, comp_whiskerRight, Category.assoc])
    exact ((trivialCofibrations C).arrow_mk_iso_iff e).mpr hRight

omit [HasLimitsOfSize.{w, w} C] [LocallySmall.{w} C] in
/-- The whole original free-J bimodule left class is trivial from the cofibrant paired scalar. -/
theorem bimoduleFreeJLeft_underlying_trivial [IsClosedSymmetricMonoidalModelCategory C] (B : Mon C)
    [IsCofibrant (A.X ⊗ B.X)] (J : MorphismProperty C) (hJ : J.rlp = fibrations C)
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [(bimoduleGenerators A B J).IsCardinalForSmallObjectArgument κ] :
    (bimoduleGenerators A B J).rlp.llp ≤ (trivialCofibrations C).inverseImage (Bimod.forget (B := B) A) := by
  let : PreservesColimitsOfSize.{w, w} (Bimod.forget (B := B) A) := inferInstance
  let : CategoryTheory.Limits.PreservesWellOrderContinuousOfShape κ.ord.ToType
      (Bimod.forget (B := B) A) := by
    refine CategoryTheory.Limits.PreservesWellOrderContinuousOfShape.mk
      (G := Bimod.forget (B := B) A) (J := κ.ord.ToType) ?_
    intro j _
    infer_instance
  let : (trivialCofibrations C).IsStableUnderCoproducts.{w} := by
    rw [← fibrations_llp C]
    infer_instance
  let : (trivialCofibrations C).IsStableUnderCobaseChange := by
    rw [← fibrations_llp C]
    infer_instance
  let : (trivialCofibrations C).IsStableUnderTransfiniteCompositionOfShape κ.ord.ToType := by
    rw [← fibrations_llp C]
    infer_instance
  let : (trivialCofibrations C).IsStableUnderRetracts := by
    rw [← fibrations_llp C]
    infer_instance
  exact rlp_llp_le_inverseImage_of_cardinal_closure (bimoduleGenerators A B J) (trivialCofibrations C)
    (Bimod.forget (B := B) A) κ (bimoduleFreeJ_generators_trivial A B J hJ)

/-- Full transfer on the original bimodule carrier from its cofibrant paired scalar, without a monoid axiom. -/
def fullBimoduleModelTransferOfCofibrantScalarPair [IsClosedSymmetricMonoidalModelCategory C] (B : Mon C)
    [IsCofibrant (A.X ⊗ B.X)]
    (hBimoduleSourceI : UniformRelativeSourceSmallness.{w} (bimoduleGenerators A B I))
    (hBimoduleSourceJ : UniformRelativeSourceSmallness.{w} (bimoduleGenerators A B J)) :
    RightTransfer.FullModelTransfer (Bimod.free A B) (Bimod.forget (B := B) A)
      I J hBimoduleSourceI hBimoduleSourceJ := by
  letI : HasLimitsOfSize.{w, w} (Bimod A B) := by apply Bimod.hasLimits
  letI : HasColimitsOfSize.{w, w} (Bimod A B) := by apply Bimod.hasColimits
  letI : LocallySmall.{w} (Bimod A B) := locallySmall_of_faithful (Bimod.forget (B := B) A)
  exact RightTransfer.fullModelTransfer (Bimod.free A B) (Bimod.forget (B := B) A)
    (Bimod.freeForgetAdjunction A B) I J hI hJ hBimoduleSourceI hBimoduleSourceJ (by
      intro κ _ _ _ X Y f hf
      exact (bimoduleFreeJLeft_underlying_trivial.{w} A B J hJ κ f hf).2)

omit [ModelCategory C] [HasLimitsOfSize.{w, w} C] [HasColimitsOfSize.{w, w} C] [LocallySmall.{w} C] in
/-- The actual free-adjunction tensor monad retains its original filtered-colimit preservation. -/
theorem bimoduleTensorMonadPreservesFilteredColimits (B : Mon C) :
    PreservesFilteredColimitsOfSize.{w, w} ((Bimod.freeForgetAdjunction A B).toMonad : C ⥤ C) := by
  change PreservesFilteredColimitsOfSize.{w, w} (tensorLeft A.X ⋙ tensorRight B.X)
  infer_instance

/-- All three original module carriers have full source-derived models and actual generating factors. -/
def fullModuleModelTransfers [MonoidAxiom.{w} C] (B : Mon C)
    (hRightSourceI : UniformRelativeSourceSmallness.{w} (rightGenerators A I))
    (hRightSourceJ : UniformRelativeSourceSmallness.{w} (rightGenerators A J))
    (hBimoduleSourceI : UniformRelativeSourceSmallness.{w} (bimoduleGenerators A B I))
    (hBimoduleSourceJ : UniformRelativeSourceSmallness.{w} (bimoduleGenerators A B J)) :
    RightTransfer.FullModelTransfer (Mod.free A.X) (Mod.forget (D := C) A.X) I J hSourceI hSourceJ ×
      RightTransfer.FullModelTransfer (RightModuleFree.functor A.X) (Mod.forget (D := C) (mop A.X))
        I J hRightSourceI hRightSourceJ ×
      RightTransfer.FullModelTransfer (Bimod.free A B) (Bimod.forget (B := B) A)
        I J hBimoduleSourceI hBimoduleSourceJ :=
  ⟨fullLeftModuleModelTransfer A I J hI hJ hSourceI hSourceJ,
    fullRightModuleModelTransfer A I J hI hJ hRightSourceI hRightSourceJ,
    fullBimoduleModelTransfer A I J hI hJ B hBimoduleSourceI hBimoduleSourceJ⟩

end HomotopicalAlgebra.ModuleTransfer
