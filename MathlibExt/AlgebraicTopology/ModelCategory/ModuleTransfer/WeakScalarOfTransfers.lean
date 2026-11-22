/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.FreeCellFlatness
import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.WeakScalarDerived

/-!
Weak scalar invariance from the actual full module transfers.

The two original generator universes and source bounds are independent.
The source module cell proof uses precisely its returned generation
cardinal, ordinal bottom and original free-I class.  Its base coefficient
and closure inputs prove flatness; no module flatness conclusion is given
as a producer premise.  The actual M4 replacements, functors, unit and
counit are retained in both resulting derived equivalences.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v wA wB

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MorphismProperty CategoryTheory.SmallObject HomotopicalAlgebra
open scoped CategoryTheory.MonObj

namespace HomotopicalAlgebra.ModuleTransfer.WeakScalarOfTransfers

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  [ModelCategory C] [HasColimitsOfSize.{0, 0} C]
  {A B : C} [MonObj A] [MonObj B]
  {IA JA IB JB : MorphismProperty C}
  {sIA : UniformRelativeSourceSmallness.{wA} (IA.strictMap (Mod.free A))}
  {sJA : UniformRelativeSourceSmallness.{wA} (JA.strictMap (Mod.free A))}
  {sIB : UniformRelativeSourceSmallness.{wB} (IB.strictMap (Mod.free B))}
  {sJB : UniformRelativeSourceSmallness.{wB} (JB.strictMap (Mod.free B))}
  (tA : RightTransfer.FullModelTransfer (Mod.free A) (Mod.forget (D := C) A) IA JA sIA sJA)
  (tB : RightTransfer.FullModelTransfer (Mod.free B) (Mod.forget (D := C) B) IB JB sIB sJB)

omit [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] in
/-- Both original target weak/fibration classes are the actual created classes, without rewriting the scalar action. -/
theorem source_created_classes :
    let : ModelCategory (Mod C A) := tA.model
    weakEquivalences (Mod C A) = (weakEquivalences C).inverseImage (Mod.forget (D := C) A) ∧
      fibrations (Mod C A) = (fibrations C).inverseImage (Mod.forget (D := C) A) :=
  ⟨tA.weak_eq, tA.fibrations_eq⟩

omit [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] in
/-- The returned full model uses exactly the original free-I generated left lifting class. -/
theorem sourceCofibrations_eq_freeI :
    let : ModelCategory (Mod C A) := tA.model
    cofibrations (Mod C A) = (HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.freeI (A := A) IA).rlp.llp := by
  let : ModelCategory (Mod C A) := tA.model
  let : Fact tA.generationCardinal.cardinal.IsRegular := tA.generationCardinal.regular
  let : OrderBot tA.generationCardinal.cardinal.ord.ToType := tA.generationCardinal.orderBot
  change cofibrations (Mod C A) = (IA.strictMap (Mod.free A)).rlp.llp
  rw [← tA.generation_I, tA.generation.I_rlp, trivialFibrations_llp]

/-- The original source rank, bottom and cell history earn flatness for each cofibrant left module. -/
theorem relativeFlat_of_originalTransfer
    (H : MorphismProperty C) [H.RespectsIso]
    (cl : HomotopicalAlgebra.ModuleTransfer.CellComparison.Closure.{u, v, wA, wA} (weakEquivalences C) H)
    (hFlat : HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.GeneratingCoefficientFlatness IA)
    (hTensor : ∀ (N : RightModuleFree.Carrier A) {K L : C} (i : K ⟶ L), IA i → H (N.X ◁ i))
    (M : Mod C A) :
    let : ModelCategory (Mod C A) := tA.model
    IsCofibrant M → HomotopicalAlgebra.ModuleTransfer.WeakScalar.RelativeFlat M := by
  let : ModelCategory (Mod C A) := tA.model
  let : Fact tA.generationCardinal.cardinal.IsRegular := tA.generationCardinal.regular
  let : OrderBot tA.generationCardinal.cardinal.ord.ToType := tA.generationCardinal.orderBot
  let : (HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.freeI (A := A) IA).IsCardinalForSmallObjectArgument
      tA.generationCardinal.cardinal := tA.generationCardinal.P_smallObject
  change IsCofibrant M → HomotopicalAlgebra.ModuleTransfer.WeakScalar.RelativeFlat M
  intro hM
  let : IsCofibrant M := hM
  intro N N' f hf
  exact HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.relativeFlat_of_original_freeICells IA
    tA.generationCardinal.cardinal
    (sourceCofibrations_eq_freeI tA) H cl hFlat hTensor M f hf

/-- The entire original module cell comparison applies to all cofibrant modules and arbitrary right endpoints. -/
theorem relativeFlat_all_originalCofibrant
    (H : MorphismProperty C) [H.RespectsIso]
    (cl : HomotopicalAlgebra.ModuleTransfer.CellComparison.Closure.{u, v, wA, wA} (weakEquivalences C) H)
    (hFlat : HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.GeneratingCoefficientFlatness IA)
    (hTensor : ∀ (N : RightModuleFree.Carrier A) {K L : C} (i : K ⟶ L), IA i → H (N.X ◁ i)) :
    let : ModelCategory (Mod C A) := tA.model
    ∀ M : Mod C A, IsCofibrant M → HomotopicalAlgebra.ModuleTransfer.WeakScalar.RelativeFlat M := by
  let : ModelCategory (Mod C A) := tA.model
  change ∀ M : Mod C A, IsCofibrant M → HomotopicalAlgebra.ModuleTransfer.WeakScalar.RelativeFlat M
  exact fun M hM => relativeFlat_of_originalTransfer tA H cl hFlat hTensor M hM

/-- The actual balanced scalar-unit map is weak from the earned original free-I producer. -/
theorem scalarUnit_weak_of_originalTransfers
    (H : MorphismProperty C) [H.RespectsIso]
    (cl : HomotopicalAlgebra.ModuleTransfer.CellComparison.Closure.{u, v, wA, wA} (weakEquivalences C) H)
    (hFlat : HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.GeneratingCoefficientFlatness IA)
    (hTensor : ∀ (N : RightModuleFree.Carrier A) {K L : C} (i : K ⟶ L), IA i → H (N.X ◁ i))
    (p : A ⟶ B) [IsMonHom p] (hp : weakEquivalences C p) (M : Mod C A) :
    let : ModelCategory (Mod C A) := tA.model
    IsCofibrant M → WeakEquivalence ((Mod.ExtensionOfScalars.adjunction p).unit.app M) := by
  let : ModelCategory (Mod C A) := tA.model
  change IsCofibrant M → WeakEquivalence ((Mod.ExtensionOfScalars.adjunction p).unit.app M)
  intro hM
  exact HomotopicalAlgebra.ModuleTransfer.WeakScalar.scalarUnit_weak tA.weak_eq p hp M
    (relativeFlat_of_originalTransfer tA H cl hFlat hTensor M hM)

/-- The actual balanced adjunction is a full Quillen equivalence in the original two created models. -/
theorem isQuillenEquivalence_of_originalTransfers
    (H : MorphismProperty C) [H.RespectsIso]
    (cl : HomotopicalAlgebra.ModuleTransfer.CellComparison.Closure.{u, v, wA, wA} (weakEquivalences C) H)
    (hFlat : HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.GeneratingCoefficientFlatness IA)
    (hTensor : ∀ (N : RightModuleFree.Carrier A) {K L : C} (i : K ⟶ L), IA i → H (N.X ◁ i))
    (p : A ⟶ B) [IsMonHom p] (hp : weakEquivalences C p) :
    let : ModelCategory (Mod C A) := tA.model
    let : ModelCategory (Mod C B) := tB.model
    (Mod.ExtensionOfScalars.adjunction p).IsQuillenEquivalence := by
  let : ModelCategory (Mod C A) := tA.model
  let : ModelCategory (Mod C B) := tB.model
  exact HomotopicalAlgebra.ModuleTransfer.WeakScalar.isQuillenEquivalenceOfRelativeFlatness
    tA.weak_eq tB.weak_eq tA.fibrations_eq tB.fibrations_eq p hp
    (relativeFlat_all_originalCofibrant tA H cl hFlat hTensor)

/-- The same source-rank Q and direct localized restriction form the actual derived equivalence. -/
def directDerivedEquivalence
    (H : MorphismProperty C) [H.RespectsIso]
    (cl : HomotopicalAlgebra.ModuleTransfer.CellComparison.Closure.{u, v, wA, wA} (weakEquivalences C) H)
    (hFlat : HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.GeneratingCoefficientFlatness IA)
    (hTensor : ∀ (N : RightModuleFree.Carrier A) {K L : C} (i : K ⟶ L), IA i → H (N.X ◁ i))
    (p : A ⟶ B) [IsMonHom p] (hp : weakEquivalences C p) :
    letI : ModelCategory (Mod C A) := tA.model
    letI : ModelCategory (Mod C B) := tB.model
    (weakEquivalences (Mod C A)).Localization ≌ (weakEquivalences (Mod C B)).Localization := by
  letI : ModelCategory (Mod C A) := tA.model
  letI : ModelCategory (Mod C B) := tB.model
  exact HomotopicalAlgebra.ModuleTransfer.WeakScalarDerived.directDerivedEquivalence
    tA.weak_eq tB.weak_eq tA.fibrations_eq tB.fibrations_eq p hp
    (relativeFlat_all_originalCofibrant tA H cl hFlat hTensor)
    (ModuleTransfer.ScalarChange.replacementsOfTransfer tA)

/-- Both independent original module ranks give the unchanged chosen-Q/chosen-R derived equivalence. -/
def replacementDerivedEquivalence
    (H : MorphismProperty C) [H.RespectsIso]
    (cl : HomotopicalAlgebra.ModuleTransfer.CellComparison.Closure.{u, v, wA, wA} (weakEquivalences C) H)
    (hFlat : HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.GeneratingCoefficientFlatness IA)
    (hTensor : ∀ (N : RightModuleFree.Carrier A) {K L : C} (i : K ⟶ L), IA i → H (N.X ◁ i))
    (p : A ⟶ B) [IsMonHom p] (hp : weakEquivalences C p) :
    letI : ModelCategory (Mod C A) := tA.model
    letI : ModelCategory (Mod C B) := tB.model
    (weakEquivalences (Mod C A)).Localization ≌ (weakEquivalences (Mod C B)).Localization := by
  letI : ModelCategory (Mod C A) := tA.model
  letI : ModelCategory (Mod C B) := tB.model
  exact HomotopicalAlgebra.ModuleTransfer.WeakScalarDerived.replacementDerivedEquivalence
    tA.weak_eq tB.weak_eq tA.fibrations_eq tB.fibrations_eq p hp
    (relativeFlat_all_originalCofibrant tA H cl hFlat hTensor)
    (ModuleTransfer.ScalarChange.replacementsOfTransfer tA)
    (ModuleTransfer.ScalarChange.replacementsOfTransfer tB)

end HomotopicalAlgebra.ModuleTransfer.WeakScalarOfTransfers
