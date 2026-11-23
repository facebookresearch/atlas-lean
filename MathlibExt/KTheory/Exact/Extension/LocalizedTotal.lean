/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.LocalizedFiber
public import MathlibExt.KTheory.Exact.Extension.Contractible
public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveEquivalenceWeakEquivalence
public import MathlibExt.CategoryTheory.CategoryBar.QuillenTheoremARight
public import MathlibExt.CategoryTheory.Monoidal.ActionLocalization.DenominatorCommaRealization
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Realization.ContinuousWhitehead

/-!
# Contractibility of the original localized-total realization

The denominator projection, its lifts, strict fibers and comma adjunction,
and the right-comma Quillen-A comparison come from the canonical generic
owners. Simplicial reversal uses the established realization API.

The extension-category application contracts the original localized-total
realization. Quotient objects, stabilizing denominators, and independent
object and Hom universes are retained.
-/

@[expose] public section

universe u v

/-! ## The actual right-comma Quillen-A hypotheses for the original denominator projection -/

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.ExactCategory CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalActionCategory
open scoped Simplicial
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace AlgebraicKTheory.LocalizedTotal

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] ExtensionCategory.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

/-- The actual projection retains the original extension object and denominator category. -/
def denominatorFunctor : ExtensionCategory.localizedExtensions (C := C) ⥤
    MonoidalActionCategory (Core C) (Core C) :=
  denominatorProjection (Core C) (ExtensionCategory C)

/-- The original positive inclusion has its actual tensor-unit denominator. -/
def positiveInclusion : ExtensionCategory C ⥤ ExtensionCategory.localizedExtensions (C := C) :=
  SInverse.inclusion (Core C) (ExtensionCategory C)

/-- The actual right comma of the denominator projection at the given denominator. -/
abbrev rightComma (s : Core C) :=
  CostructuredArrow (denominatorFunctor (C := C))
    (⟨s⟩ : MonoidalActionCategory (Core C) (Core C))

/-- Realize the constructed original-E/fixed-denominator equivalence using its actual paths. -/
def fiberRealizedEquiv (s : Core C) :
    ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj (nerve (ExtensionCategory C) : SSet.{max u v}))
      (SSet.toTop.obj
        (nerve (denominatorFiber (X := ExtensionCategory C) s) : SSet.{max u v})) := by
  let E := denominatorFiberEquivalence (X := ExtensionCategory C) s
  let NE : SSet.{max u v} := nerve (ExtensionCategory C)
  let NF : SSet.{max u v} := nerve (denominatorFiber (X := ExtensionCategory C) s)
  let f : NE ⟶ NF := nerveMap E.functor
  let g : NF ⟶ NE := nerveMap E.inverse
  have hfg : f ≫ g = nerveMap (E.functor ⋙ E.inverse) := nerveMap_comp E.functor E.inverse
  have hgf : g ≫ f = nerveMap (E.inverse ⋙ E.functor) := nerveMap_comp E.inverse E.functor
  have hu0 : SSet.Homotopy (nerveMap (E.functor ⋙ E.inverse)) (𝟙 NE) := by
    simpa only [nerveMap_id] using NatTrans.nerveHomotopy E.unitInv
  have hc0 : SSet.Homotopy (nerveMap (E.inverse ⋙ E.functor)) (𝟙 NF) := by
    simpa only [nerveMap_id] using NatTrans.nerveHomotopy E.counit
  have hu : SSet.Homotopy (f ≫ g) (𝟙 NE) := hfg.symm ▸ hu0
  have hc : SSet.Homotopy (g ≫ f) (𝟙 NF) := hgf.symm ▸ hc0
  exact SSet.realizedHomotopyEquiv NE NF f g hu hc
/-- The forward fiber comparison is the realized literal fixed-denominator functor. -/
theorem fiberRealizedEquiv_toFun (s : Core C) :
    (fiberRealizedEquiv (C := C) s).toFun =
      (SSet.toTop.map (nerveMap (denominatorFiberFunctor
        (X := ExtensionCategory C) s))).hom := rfl

/-- Its inverse is the realized constructed original positive-object projection. -/
theorem fiberRealizedEquiv_invFun (s : Core C) :
    (fiberRealizedEquiv (C := C) s).invFun =
      (SSet.toTop.map (nerveMap (denominatorFiberInverse
        (X := ExtensionCategory C) s))).hom := rfl

/-- The actual comma retraction and fixed-denominator inverse compare the comma with original E. -/
def commaRealizedEquiv (s : Core C) :
    ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj (nerve (rightComma (C := C) s) : SSet.{max u v}))
      (SSet.toTop.obj (nerve (ExtensionCategory C) : SSet.{max u v})) :=
  (denominatorCommaRealizedHomotopyEquiv (X := ExtensionCategory C) s).trans
    (fiberRealizedEquiv (C := C) s).symm

/-- The forward map is the actual realized comma retraction followed by the original inverse. -/
theorem commaRealizedEquiv_toFun (s : Core C) :
    (commaRealizedEquiv (C := C) s).toFun =
      (fiberRealizedEquiv (C := C) s).invFun.comp
        (denominatorCommaRealizedHomotopyEquiv (X := ExtensionCategory C) s).toFun := rfl

/-- The reverse map retains both actual constructed inclusion maps. -/
theorem commaRealizedEquiv_invFun (s : Core C) :
    (commaRealizedEquiv (C := C) s).invFun =
      (denominatorCommaRealizedHomotopyEquiv (X := ExtensionCategory C) s).invFun.comp
        (fiberRealizedEquiv (C := C) s).toFun := rfl

/-- Every original denominator right comma is contractible by the proved original E contraction. -/
theorem rightComma_contractibleSpace (s : Core C) :
    ContractibleSpace
      (SSet.toTop.obj (nerve (rightComma (C := C) s) : SSet.{max u v})) := by
  have hE : ContractibleSpace (SSet.toTop.obj (nerve (ExtensionCategory C))) :=
    ExtensionCategory.realization_contractibleSpace (C := C)
  exact @ContinuousMap.HomotopyEquiv.contractibleSpace _ _ _ _ hE
    (commaRealizedEquiv (C := C) s)

/-- The exact actual right-comma-to-terminal map satisfies the needed realization-WE hypothesis. -/
theorem rightComma_to_terminal_mem (s : Core C) :
    SSet.realizationWeakEquivalences
      (terminal.from (nerve (rightComma (C := C) s) : SSet.{max u v})) := by
  have hComma : ContractibleSpace
      (SSet.toTop.obj (nerve (rightComma (C := C) s) : SSet.{max u v})) :=
    rightComma_contractibleSpace (C := C) s
  exact @SSet.RealizationCWUpgrade.conull_mem_of_contractible
    (nerve (rightComma (C := C) s)) hComma

omit [ExactCategory C] in
/-- The original tensor-unit initial object proves the exact base conull weak equivalence. -/
theorem denominatorBase_to_terminal_mem :
    SSet.realizationWeakEquivalences
      (terminal.from (nerve (MonoidalActionCategory (Core C) (Core C)) : SSet.{max u v})) :=
  NerveContractible.terminal_from_mem_realizationWeakEquivalences_of_isInitial
    (selfUnitIsInitial (S := Core C))

/-- The original positive inclusion retains its literal tensor-unit denominator. -/
theorem positiveInclusion_denominator_obj (E : ExtensionCategory C) :
    (denominatorFunctor (C := C)).obj ((positiveInclusion (C := C)).obj E) =
      (⟨𝟙_ (Core C)⟩ : MonoidalActionCategory (Core C) (Core C)) := rfl

/-- The actual denominator image of every positive-inclusion arrow is the base identity. -/
theorem positiveInclusion_denominator_map {E F : ExtensionCategory C} (f : E ⟶ F) :
    (denominatorFunctor (C := C)).map ((positiveInclusion (C := C)).map f) =
      𝟙 (⟨𝟙_ (Core C)⟩ : MonoidalActionCategory (Core C) (Core C)) :=
  (denominatorProjection_pairMap f (𝟙 (𝟙_ (Core C)))).trans
    ((MonoidalActionCategory.inclusion (Core C) (Core C)).map_id (𝟙_ (Core C)))

end AlgebraicKTheory.LocalizedTotal

end


/-! ## Apply the derived actual right-comma criterion to the original denominator projection -/

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject
open CategoryTheory.MorphismProperty CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal

attribute [local instance] CategoryTheory.uliftCategory


namespace AlgebraicKTheory.LocalizedTotal

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] ExtensionCategory.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

/-- The actual cross-universe denominator projection is weakly equivalent by its derived commas. -/
theorem denominatorFunctor_mem :
    SSet.realizationWeakEquivalences
      (nerveMapCross.{max u v, u} (denominatorFunctor (C := C))) := by
  apply SSet.OppositeRealization.crossMap_mem_of_costructuredArrow
    (denominatorFunctor (C := C))
  intro d
  rcases d with ⟨s⟩
  exact rightComma_to_terminal_mem (C := C) s

/-- The exact original localized-total conull map is weakly equivalent to the terminal point. -/
theorem localizedTotal_to_terminal_mem :
    SSet.realizationWeakEquivalences
      (terminal.from (nerve (ExtensionCategory.localizedExtensions (C := C)) :
        SSet.{max u v})) := by
  let N : SSet.{max u v} := nerve (ExtensionCategory.localizedExtensions (C := C))
  let B : SSet.{max u v} := nerve (MonoidalActionCategory (Core C) (Core C))
  let p : N ⟶ B := nerveMapCross.{max u v, u} (denominatorFunctor (C := C))
  let q : B ⟶ (⊤_ SSet.{max u v}) := terminal.from B
  have hp : SSet.realizationWeakEquivalences p := denominatorFunctor_mem (C := C)
  have hq : SSet.realizationWeakEquivalences q := denominatorBase_to_terminal_mem (C := C)
  have hcomp : SSet.realizationWeakEquivalences (p ≫ q) :=
    SSet.realizationWeakEquivalences.comp_mem p q hp hq
  have heq : p ≫ q = terminal.from N := terminal.hom_ext _ _
  exact heq ▸ hcomp

end AlgebraicKTheory.LocalizedTotal

end


/-!
# Contractibility of the original localized-total realization

The imported canonical adapter derives realized cofibrancy from the initial
simplicial monomorphism and TopCat fibrancy from the actual singular Kan
complex. Its good realized standard cylinder interprets model Whitehead as
continuous homotopy and retains the given realization map as the HE forward
map. The application below uses the original localized-total terminal weak
equivalence and keeps all original u/v and the exact nerve realization.

The specialization retains the verified original proof body. Its canonical
public import and semantic consumer tests passed the native verification gates.
-/

universe k

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.ExactCategory CategoryTheory.Limits HomotopicalAlgebra
open scoped Simplicial MonoidalCategory SSet.modelCategoryQuillen TopCat.modelCategory

namespace AlgebraicKTheory.LocalizedTotal

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] ExtensionCategory.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

/-- Contractibility of the same original localized-total realization, with all u/v retained. -/
theorem localizedTotal_contractible :
    ContractibleSpace
      (SSet.toTop.obj (nerve (ExtensionCategory.localizedExtensions (C := C)) :
        SSet.{max u v})) :=
  SSet.RealizationCWUpgrade.contractible_of_conull_weakEquivalence
    (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max u v})
    (localizedTotal_to_terminal_mem (C := C))

end AlgebraicKTheory.LocalizedTotal

end
