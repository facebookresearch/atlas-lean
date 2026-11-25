/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.CellularSource
import all MathlibExt.AlgebraicTopology.ModelCategory.CellularSource
import Lean.Util.CollectAxioms
import Batteries.Tactic.Lint

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w u v

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

section OriginalPresentedComplex

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C}
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => P.homFamily) f)
  (t : CellularSubcomplex c)

example : t.hom ≫ t.inclusion = f := t.fac

example (a : t.complex.Cells) : (t.originalCell a).j = a.j := rfl

example (a : t.complex.Cells) : a.i = (t.originalCell a).i := t.originalCell_label a

example (a : t.complex.Cells) :
    a.ι ≫ t.inclusion =
      eqToHom (congrArg (fun p : P.toSet => p.1.right) (t.originalCell_label a)) ≫
        (t.originalCell a).ι := t.originalCell_inclusion a

example : Cardinal.mk t.complex.Cells ≤ Cardinal.mk c.Cells := t.cells_cardinal_le

example : (CellularSubcomplex.full c).complex = c := rfl

example : (CellularSubcomplex.full c).comparison = 𝟙 c.F := rfl

end OriginalPresentedComplex

section OriginalCellularity

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  {d : CofibrantGenerationData C κ} (h : CellularSource d)

example {A B : C} (f : A ⟶ B) (hf : cofibrations C f) : Mono f :=
  CellularSource.mono_of_cofibration h f hf

example {A B : C} (f : A ⟶ B) (hf : cofibrations C f) :
    IsLimit (Fork.ofι f (pushout.condition (f := f) (g := f))) :=
  CellularSource.originalPushoutEqualizer h f hf

example (i : d.I.toSet) : IsCellularCompact.{w} d.I i.1.left := h.I_domains_compact i

example (i : d.I.toSet) : IsCellularCompact.{w} d.I i.1.right := h.I_codomains_compact i

example (j : d.J.toSet) : IsUniformlySmallRelativeTo.{w} d.I j.1.left := h.J_domains_small j

end OriginalCellularity

#print axioms HomotopicalAlgebra.CellularSubcomplex.full
#print axioms HomotopicalAlgebra.CellularSubcomplex.fac
#print axioms HomotopicalAlgebra.CellularSubcomplex.originalCell
#print axioms HomotopicalAlgebra.CellularSubcomplex.originalCell_label
#print axioms HomotopicalAlgebra.CellularSubcomplex.originalCell_inclusion
#print axioms HomotopicalAlgebra.CellularSubcomplex.cellEmbedding
#print axioms HomotopicalAlgebra.CellularSubcomplex.cells_cardinal_le
#print axioms HomotopicalAlgebra.IsCellularCompactAt.mono
#print axioms HomotopicalAlgebra.IsCellularCompactAt.of_retract
#print axioms HomotopicalAlgebra.CellularSource.effectivePresentation
#print axioms HomotopicalAlgebra.CellularSource.mono_of_cofibration
#print axioms HomotopicalAlgebra.CellularSource.originalPushoutEqualizer

namespace CellularFamilyClients

open CategoryTheory Limits MorphismProperty Opposite
open HomotopicalAlgebra HomotopicalAlgebra.CellularSubcomplexExtension

section OriginalInclusion

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (h : CellularSource d)
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f)
  (t : CellularSubcomplex c)

example : cofibrations C t.inclusion := inclusionCofibration d c h t

example : Mono t.inclusion := inclusionMono d c h t

example : RegularMono t.inclusion := inclusionRegularMono d c h t

example :
    IsLimit (Fork.ofι t.inclusion (pushout.condition (f := t.inclusion) (g := t.inclusion))) :=
  inclusionPushoutEqualizer d c h t

example (j : O) (hj : ¬ IsMax j) : Mono (c.F.map (homOfLE (Order.le_succ j))) :=
  originalSuccessorMono d c h j hj

example (j : O) (hj : ¬ IsMax j) (a : (t.complex.attachCells j hj).ι) :
    boundary d t.complex j hj a ≫ t.comparison.app j =
      eqToHom (congrArg (fun p : d.I.toSet => p.1.left) (t.label_eq j hj a)) ≫
        boundary d c j hj (t.cellIndex j hj a) :=
  subcomplexBoundary d c h t j hj a

end OriginalInclusion

section OriginalCompatibleFamily

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (h : CellularSource d)
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f)
  {T : Type w} (t : T → CellularSubcomplex c) {E B : C}
  (α : ∀ i : T, (t i).endpoint ⟶ E) (q : E ⟶ B) (r : X ⟶ E) (β : Y ⟶ B)
  (hq : d.I.rlp q) (hrq : r ≫ q = f ≫ β)
  (hroot : ∀ i : T, (t i).hom ≫ α i = r)
  (hα : ∀ i : T, α i ≫ q = (t i).inclusion ≫ β)
  (hcells : FamilyCellCompatible d c t α)

example :
    ∃ ℓ : Y ⟶ E, f ≫ ℓ = r ∧ ℓ ≫ q = β ∧ ∀ i : T, (t i).inclusion ≫ ℓ = α i :=
  existsFamilyLift d c h t α q r β hq hrq hroot hα hcells

example : StageState d c t α q r β ⊥ := bottomState d c t α q r β hrq hroot

example (j : O) (hj : ¬ IsMax j) (s : StageState d c t α q r β j) :
    StageState d c t α q r β (Order.succ j) :=
  successorState d c h t α q r β hq hcells hα j hj s

example (j : O) (hj : ¬ IsMax j) (s : StageState d c t α q r β j) :
    (stageFunctor d c t α q r β).map (homOfLE (Order.le_succ j)).op
      (successorState d c h t α q r β hq hcells hα j hj s) = s :=
  successorState_restrict d c h t α q r β hq hcells hα j hj s

example : (stageFunctor d c t α q r β).sections :=
  (familyInductionData d c h t α q r β hq hcells hα).sectionsMk
    (bottomState d c t α q r β hrq hroot)

example (j : O) (hj : ¬ IsMax j) (s : StageState d c t α q r β j)
    (i : T) (a : ((t i).complex.attachCells j hj).ι) :
    eqToHom (congrArg (fun p : d.I.toSet => p.1.right) ((t i).label_eq j hj a)) ≫
      completionCellImage d c t α q r β hq j hj s ((t i).cellIndex j hj a) =
        ((t i).complex.attachCells j hj).cell a ≫ (t i).complex.incl.app (Order.succ j) ≫ α i :=
  completionCellImage_family d c t α q r β hq hcells j hj s i a

example (j : O) (hj : ¬ IsMax j) (k : (c.attachCells j hj).ι)
    (hk : Selected d c t j hj k) (i : T) (a : ((t i).complex.attachCells j hj).ι)
    (e : (t i).cellIndex j hj a = k) :
    eqToHom (congrArg (fun a => ((c.attachCells j hj).π a).1.right) e) ≫
      selectedCellImage d c t α j hj k hk = familyCellImage d c t α j hj i a :=
  selectedCellImage_eq d c t α hcells j hj k hk i a e

end OriginalCompatibleFamily

#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.boundary
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.boundary_cell
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.originalSuccessorCofibration
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.originalSuccessorMono
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.generatorTransport
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.subcomplexBoundary
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.familyCellImage
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.FamilyCellCompatible
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.Selected
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.selectedCellImage
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.selectedCellImage_eq
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.familyCellImage_boundary
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.familyCellImage_right
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.selectedCellImage_boundary
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.selectedCellImage_right
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.StageState
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.stageMap
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.stageFunctor
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.missingCellSquare
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.completionCellImage
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.completionCellImage_boundary
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.completionCellImage_right
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.completionCellImage_family
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.completionCofanMap
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.completionCofanMap_inj
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.successorLift
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.successorLift_stage
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.successorLift_cell
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.bottomState
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.successorState
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.successorState_restrict
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.ordinaryLimitFamily
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.limitState
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.limitState_restrict
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.familyInductionData
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.existsFamilyLift
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.inclusionCofibration
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.inclusionMono
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.inclusionRegularMono
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.inclusionPushoutEqualizer

end CellularFamilyClients

namespace CellularPrefixClients

open CategoryTheory Limits MorphismProperty Opposite
open HomotopicalAlgebra HomotopicalAlgebra.CellularSubcomplexExtension

section OriginalPrefix

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f) (j : O)

example : (prefixComplex d c j).F = (Set.initialSegIic j).monotone.functor ⋙ c.F :=
  prefixComplex_functor d c j

example : (prefixComplex d c j).isoBot = c.isoBot := prefixComplex_isoBot d c j

example (a : Set.Iic j) : (prefixComplex d c j).incl.app a = c.F.map (homOfLE a.2) :=
  prefixComplex_incl d c j a

example (a : Set.Iic j) (ha : ¬ IsMax a) :
    ((prefixComplex d c j).attachCells a ha).cofan₁ = (c.attachCells a.1 (prefixNotMax a ha)).cofan₁ :=
  prefixComplex_sourceCofan d c j a ha

example (a : Set.Iic j) (ha : ¬ IsMax a) :
    ((prefixComplex d c j).attachCells a ha).cofan₂ = (c.attachCells a.1 (prefixNotMax a ha)).cofan₂ :=
  prefixComplex_targetCofan d c j a ha

example (a : Set.Iic j) (ha : ¬ IsMax a) :
    ((prefixComplex d c j).attachCells a ha).m = (c.attachCells a.1 (prefixNotMax a ha)).m :=
  prefixComplex_attachingMap d c j a ha

example (a : Set.Iic j) (ha : ¬ IsMax a) (k : (c.attachCells a.1 (prefixNotMax a ha)).ι) :
    ((prefixComplex d c j).attachCells a ha).π k = (c.attachCells a.1 (prefixNotMax a ha)).π k :=
  prefixComplex_label d c j a ha k

example (a : Set.Iic j) (ha : ¬ IsMax a) (k : (c.attachCells a.1 (prefixNotMax a ha)).ι) :
    boundary d (prefixComplex d c j) a ha k = boundary d c a.1 (prefixNotMax a ha) k :=
  prefixComplex_boundary d c j a ha k

example (a : Set.Iic j) (ha : ¬ IsMax a) (k : (c.attachCells a.1 (prefixNotMax a ha)).ι) :
    ((prefixComplex d c j).attachCells a ha).cell k =
      (c.attachCells a.1 (prefixNotMax a ha)).cell k ≫ c.F.map (eqToHom (prefixSuccessorEq a ha).symm) :=
  prefixComplex_cell d c j a ha k

example (a : Set.Iic j) (ha : ¬ IsMax a) (k : (c.attachCells a.1 (prefixNotMax a ha)).ι) :
    (({ j := a, hj := ha, k := k } : (prefixComplex d c j).Cells)).ι =
      (c.attachCells a.1 (prefixNotMax a ha)).cell k ≫
        c.F.map (homOfLE (Order.succ_le_of_lt (prefixStage_lt_endpoint a ha))) :=
  prefixComplex_cell_inclusion d c j a ha k

variable (t : CellularSubcomplex c)

example : (prefixSubcomplex d c t j).endpoint = t.complex.F.obj j :=
  prefixSubcomplex_endpoint d c t j

example : (prefixSubcomplex d c t j).inclusion = t.comparison.app j :=
  prefixSubcomplex_inclusion d c t j

example (a : Set.Iic j) (ha : ¬ IsMax a) :
    (prefixSubcomplex d c t j).cellIndex a ha = t.cellIndex a.1 (prefixNotMax a ha) :=
  prefixSubcomplex_cellIndex d c t j a ha

example : (prefixSubcomplex d c t j).complex = prefixComplex d t.complex j := rfl

example : (prefixSubcomplex d c t j).comparison =
    Functor.whiskerLeft (Set.initialSegIic j).monotone.functor t.comparison := rfl

example : (prefixSubcomplex d c t j).hom =
    t.complex.isoBot.inv ≫ t.complex.F.map (homOfLE (bot_le : (⊥ : O) ≤ j)) := rfl

example :
    (t.complex.isoBot.inv ≫ t.complex.F.map (homOfLE (bot_le : (⊥ : O) ≤ j))) ≫
        t.comparison.app j = c.isoBot.inv ≫ c.F.map (homOfLE (bot_le : (⊥ : O) ≤ j)) :=
  (prefixSubcomplex d c t j).fac

variable (h : CellularSource d)

example : cofibrations C (t.comparison.app j) := by
  simpa only [prefixSubcomplex_endpoint, prefixSubcomplex_inclusion] using
    inclusionCofibration d (prefixComplex d c j) h (prefixSubcomplex d c t j)

example : Mono (t.comparison.app j) := by
  simpa only [prefixSubcomplex_endpoint, prefixSubcomplex_inclusion] using
    inclusionMono d (prefixComplex d c j) h (prefixSubcomplex d c t j)

example : RegularMono (t.comparison.app j) := by
  simpa only [prefixSubcomplex_endpoint, prefixSubcomplex_inclusion] using
    inclusionRegularMono d (prefixComplex d c j) h (prefixSubcomplex d c t j)

end OriginalPrefix

section FamilyAtActualOriginalStage

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (h : CellularSource d)
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f)
  (j : O) {T : Type w} (t : T → CellularSubcomplex c) {E B : C}
  (α : ∀ i : T, (t i).complex.F.obj j ⟶ E) (q : E ⟶ B) (r : X ⟶ E) (β : c.F.obj j ⟶ B)
  (hq : d.I.rlp q)
  (hrq : r ≫ q = (c.isoBot.inv ≫ c.F.map (homOfLE (bot_le : (⊥ : O) ≤ j))) ≫ β)
  (hroot : ∀ i : T, (prefixSubcomplex d c (t i) j).hom ≫ α i = r)
  (hα : ∀ i : T, α i ≫ q = (t i).comparison.app j ≫ β)
  (hcells : FamilyCellCompatible d (prefixComplex d c j)
    (fun i : T => prefixSubcomplex d c (t i) j) α)

example :
    ∃ ℓ : c.F.obj j ⟶ E,
      (c.isoBot.inv ≫ c.F.map (homOfLE (bot_le : (⊥ : O) ≤ j))) ≫ ℓ = r ∧
        ℓ ≫ q = β ∧ ∀ i : T, (t i).comparison.app j ≫ ℓ = α i :=
  existsFamilyLift d (prefixComplex d c j) h (fun i => prefixSubcomplex d c (t i) j)
    α q r β hq hrq hroot hα hcells

end FamilyAtActualOriginalStage

#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.prefixNotMax
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.prefixStage_lt_endpoint
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.prefixSuccessorEq
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.prefixShape
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.prefixStepIso
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.prefixComplex
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.prefixComplex_functor
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.prefixComplex_isoBot
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.prefixComplex_incl
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.prefixComplex_sourceCofan
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.prefixComplex_targetCofan
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.prefixComplex_label
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.prefixComplex_attachingMap
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.prefixComplex_boundary
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.prefixComplex_cell
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.prefixComplex_cell_inclusion
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.prefixSubcomplex
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.prefixSubcomplex_endpoint
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.prefixSubcomplex_inclusion
#print axioms HomotopicalAlgebra.CellularSubcomplexExtension.prefixSubcomplex_cellIndex

end CellularPrefixClients

namespace CellularContainmentClients

open CategoryTheory Limits MorphismProperty Opposite
open HomotopicalAlgebra HomotopicalAlgebra.CellularSubcomplexContainment

section OriginalSupport

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f)
  (t u : CellularSubcomplex c) (H : SupportLE d c t u)

example : Set.range t.originalCell ⊆ Set.range u.originalCell := H

example : SupportLE d c t t := supportRefl d c t

example (v : CellularSubcomplex c) (K : SupportLE d c u v) : SupportLE d c t v :=
  supportTrans d c t u v H K

example (a : t.complex.Cells) : u.originalCell (supportCell d c t u H a) = t.originalCell a :=
  supportCell_original d c t u H a

example (a : t.complex.Cells) : (supportCell d c t u H a).j = a.j :=
  supportCell_stage d c t u H a

example : t.complex.Cells ↪ u.complex.Cells := supportCellEmbedding d c t u H

example (j : O) (hj : ¬ IsMax j) (k : (t.complex.attachCells j hj).ι) :
    u.cellIndex j hj (stageCell d c t u H j hj k) = t.cellIndex j hj k :=
  stageCell_original d c t u H j hj k

example (j : O) (hj : ¬ IsMax j) (k : (t.complex.attachCells j hj).ι) :
    (t.complex.attachCells j hj).π k = (u.complex.attachCells j hj).π (stageCell d c t u H j hj k) :=
  stageCell_label d c t u H j hj k

variable (h : CellularSource d)

example : t.hom ≫ containmentMap d c t u h H = u.hom := containmentMap_root d c t u h H

example : containmentMap d c t u h H ≫ u.inclusion = t.inclusion := containmentMap_ambient d c t u h H

example (a : t.complex.Cells) (b : u.complex.Cells) (hab : u.originalCell b = t.originalCell a) :
    a.ι ≫ containmentMap d c t u h H = cellMapInto d c t u a b hab :=
  containmentMap_cell d c t u h H a b hab

example (m : t.endpoint ⟶ u.endpoint) (hm : m ≫ u.inclusion = t.inclusion) :
    m = containmentMap d c t u h H := containmentMap_unique d c t u h H m hm

example : CellularSubcomplex u.complex := asSubcomplex d c t u h H

example : (asSubcomplex d c t u h H).complex = t.complex := asSubcomplex_complex d c t u h H

example : (asSubcomplex d c t u h H).inclusion = containmentMap d c t u h H :=
  asSubcomplex_inclusion d c t u h H

example : (asSubcomplex d c t u h H).comparison = comparison d c t u h H :=
  asSubcomplex_comparison d c t u h H

example : cofibrations C (containmentMap d c t u h H) := containmentMap_cofibration d c t u h H

example : Mono (containmentMap d c t u h H) := containmentMap_mono d c t u h H

example : RegularMono (containmentMap d c t u h H) := containmentMapRegularMono d c t u h H

example (j : O) : stageMap d c t u h H j ≫ u.comparison.app j = t.comparison.app j :=
  stageMap_ambient d c t u h H j

example (j : O) :
    (t.complex.isoBot.inv ≫ t.complex.F.map (homOfLE (bot_le : (⊥ : O) ≤ j))) ≫
        stageMap d c t u h H j =
      u.complex.isoBot.inv ≫ u.complex.F.map (homOfLE (bot_le : (⊥ : O) ≤ j)) :=
  stageMap_root d c t u h H j

example (j : O) (hj : ¬ IsMax j) (k : (t.complex.attachCells j hj).ι) :
    (t.complex.attachCells j hj).cell k ≫ stageMap d c t u h H (Order.succ j) =
      eqToHom (congrArg (fun p : d.I.toSet => p.1.right) (stageCell_label d c t u H j hj k)) ≫
        (u.complex.attachCells j hj).cell (stageCell d c t u H j hj k) :=
  stageMap_cell d c t u h H j hj k

example (j : O) (m : t.complex.F.obj j ⟶ u.complex.F.obj j)
    (hm : m ≫ u.comparison.app j = t.comparison.app j) : m = stageMap d c t u h H j :=
  stageMap_unique d c t u h H j m hm

example (j : O) : cofibrations C (stageMap d c t u h H j) := stageMap_cofibration d c t u h H j

example (j : O) : RegularMono (stageMap d c t u h H j) := stageMapRegularMono d c t u h H j

example : comparison d c t u h H ≫ u.comparison = t.comparison := comparison_ambient d c t u h H

example (j : O) : t.complex.incl.app j ≫ containmentMap d c t u h H =
    (comparison d c t u h H).app j ≫ u.complex.incl.app j := comparison_endpoint d c t u h H j

example (a : t.complex.F ⟶ u.complex.F) (ha : a ≫ u.comparison = t.comparison) :
    a = comparison d c t u h H := comparison_unique d c t u h H a ha

example : containmentMap d c t t h (supportRefl d c t) = 𝟙 t.endpoint :=
  containmentMap_refl d c t h (supportRefl d c t)

example (v : CellularSubcomplex c) (K : SupportLE d c u v) :
    containmentMap d c t u h H ≫ containmentMap d c u v h K =
      containmentMap d c t v h (supportTrans d c t u v H K) :=
  containmentMap_comp d c t u h v H K

example (v : CellularSubcomplex c) (K : SupportLE d c u v) (j : O) :
    stageMap d c t u h H j ≫ stageMap d c u v h K j =
      stageMap d c t v h (supportTrans d c t u v H K) j := stageMap_comp d c t u h v H K j

example (v : CellularSubcomplex c) (K : SupportLE d c u v) :
    comparison d c t u h H ≫ comparison d c u v h K =
      comparison d c t v h (supportTrans d c t u v H K) := comparison_comp d c t u h v H K

end OriginalSupport

section EqualOriginalSupports

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f)
  (t u : CellularSubcomplex c) (h : CellularSource d)
  (e : Set.range t.originalCell = Set.range u.originalCell)

example : t.endpoint ≅ u.endpoint := endpointIso d c t u h e

example (j : O) : t.complex.F.obj j ≅ u.complex.F.obj j := stageIso d c t u h e j

example : t.complex.F ≅ u.complex.F := comparisonIso d c t u h e

example : t.hom ≫ (endpointIso d c t u h e).hom = u.hom := endpointIso_root d c t u h e

example : (endpointIso d c t u h e).hom ≫ u.inclusion = t.inclusion := endpointIso_ambient d c t u h e

example (a : t.complex.Cells) (b : u.complex.Cells) (hab : u.originalCell b = t.originalCell a) :
    a.ι ≫ (endpointIso d c t u h e).hom = cellMapInto d c t u a b hab := endpointIso_cell d c t u h e a b hab

example (j : O) : (stageIso d c t u h e j).hom ≫ u.comparison.app j = t.comparison.app j :=
  stageIso_ambient d c t u h e j

example (j : O) : t.complex.incl.app j ≫ (endpointIso d c t u h e).hom =
    (stageIso d c t u h e j).hom ≫ u.complex.incl.app j := isomorphism_endpoint d c t u h e j

example : (comparisonIso d c t u h e).hom ≫ u.comparison = t.comparison := comparisonIso_ambient d c t u h e

end EqualOriginalSupports

#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.SupportLE
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.supportRefl
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.supportTrans
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.originalCell_injective
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.supportCell
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.supportCell_original
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.supportCell_stage
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.supportCellEmbedding
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.cellLabelEq
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.ambientCell_transport
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.cellMapInto
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.cellMapInto_ambient
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.occurrenceEmbedding
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.existsStageCell
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.stageCell
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.stageCell_original
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.stageCellEmbedding
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.stageCell_label
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.prefixSupportLE
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.ambientStageCell_transport
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.stageCellMap_ambient
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.existsContainmentMap
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.containmentMap
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.containmentMap_ambient
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.containmentMap_root
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.containmentMap_unique
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.containmentMap_cell
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.stageComparisonMono
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.stageMap
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.stageMap_ambient
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.stageMap_unique
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.stageMap_cell
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.stageMap_naturality
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.comparison
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.comparison_ambient
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.comparison_endpoint
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.comparison_bot
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.comparison_unique
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.asSubcomplex
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.asSubcomplex_complex
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.asSubcomplex_inclusion
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.asSubcomplex_comparison
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.containmentMap_cofibration
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.containmentMap_mono
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.containmentMapRegularMono
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.stageMap_cofibration
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.stageMap_mono
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.stageMapRegularMono
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.stageMap_root
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.containmentMap_refl
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.containmentMap_comp
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.stageMap_refl
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.stageMap_comp
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.comparison_refl
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.comparison_comp
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.endpointIso
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.stageIso
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.comparisonIso
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.endpointIso_root
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.endpointIso_ambient
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.stageIso_ambient
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.comparisonIso_ambient
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.isomorphism_endpoint
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.endpointIso_cell
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.stageIso_root
#print axioms HomotopicalAlgebra.CellularSubcomplexContainment.stageIso_cell

end CellularContainmentClients

namespace CellularPushoutClients

open CategoryTheory Limits MorphismProperty Opposite
open HomotopicalAlgebra HomotopicalAlgebra.CellularCofibrationPushout

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {A B L P : C} (f : A ⟶ B) (g : A ⟶ L) (i : B ⟶ P) (j : L ⟶ P)
  (sq : IsPushout f g i j)
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (h : CellularSource d)
  (hf : cofibrations C f) (hg : cofibrations C g)

example : pushout.inl f f ≫ duplicateMap f g i j sq = i ≫ pushout.inl j j :=
  duplicateMap_left f g i j sq

example : pushout.inr f f ≫ duplicateMap f g i j sq = i ≫ pushout.inr j j :=
  duplicateMap_right f g i j sq

example : duplicateSourceRoot f ≫ duplicateMap f g i j sq = g ≫ duplicateTargetRoot j :=
  duplicateMap_root f g i j sq

example : IsPushout (duplicateSourceRoot f) g (duplicateMap f g i j sq) (duplicateTargetRoot j) :=
  duplicateIsPushout f g i j sq

example : cofibrations C (duplicateMap f g i j sq) := duplicateMap_cofibration f g i j sq hg

example : Mono (duplicateMap f g i j sq) := duplicateMap_mono f g i j sq d h hg

example : IsPullback f g i j := isPullback f g i j sq d h hf hg

example {Z : C} (a : Z ⟶ B) (b : Z ⟶ L) (hab : a ≫ i = b ≫ j) :
    ∃ m : Z ⟶ A, m ≫ f = a ∧ m ≫ g = b :=
  (isPullback f g i j sq d h hf hg).exists_lift a b hab

example {Z : C} (a b : Z ⟶ A) (hf' : a ≫ f = b ≫ f) (hg' : a ≫ g = b ≫ g) : a = b :=
  (isPullback f g i j sq d h hf hg).hom_ext hf' hg'

#print axioms HomotopicalAlgebra.CellularCofibrationPushout.duplicateSourceRoot
#print axioms HomotopicalAlgebra.CellularCofibrationPushout.duplicateTargetRoot
#print axioms HomotopicalAlgebra.CellularCofibrationPushout.duplicateMap
#print axioms HomotopicalAlgebra.CellularCofibrationPushout.duplicateMap_left
#print axioms HomotopicalAlgebra.CellularCofibrationPushout.duplicateMap_right
#print axioms HomotopicalAlgebra.CellularCofibrationPushout.duplicateMap_root
#print axioms HomotopicalAlgebra.CellularCofibrationPushout.duplicateIsPushout
#print axioms HomotopicalAlgebra.CellularCofibrationPushout.duplicateMap_cofibration
#print axioms HomotopicalAlgebra.CellularCofibrationPushout.duplicateMap_mono
#print axioms HomotopicalAlgebra.CellularCofibrationPushout.isPullback

end CellularPushoutClients

namespace CellularAttachmentClients

open CategoryTheory Limits MorphismProperty Opposite
open HomotopicalAlgebra HomotopicalAlgebra.CellularAttachmentComparison

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (h : CellularSource d)
  {S T X Y : C} (δ : S ⟶ T) (f : S ⟶ X) (g : T ⟶ Y) (u : X ⟶ Y)
  (a : AttachCells.{w} d.I.homFamily f) (b : AttachCells.{w} d.I.homFamily g)
  (cellIndex : a.ι ↪ b.ι)
  (labelEq : ∀ k : a.ι, a.π k = b.π (cellIndex k))
  (rootEq : f ≫ u = δ ≫ g)
  (cellEq : ∀ k : a.ι, a.cell k ≫ u =
    eqToHom (congrArg (fun p : d.I.toSet => p.1.right) (labelEq k)) ≫ b.cell (cellIndex k))
  (hδ : cofibrations C δ)

example : cofibrations C f := attachmentCofibration d a

example : cofibrations C g := attachmentCofibration d b

example (k : a.ι) : boundary d a k ≫ f = d.I.homFamily (a.π k) ≫ a.cell k :=
  boundary_cell d a k

example (k : a.ι) : boundary d a k ≫ δ =
    eqToHom (congrArg (fun p : d.I.toSet => p.1.left) (labelEq k)) ≫ boundary d b (cellIndex k) :=
  selectedBoundary d h δ f g u a b cellIndex labelEq rootEq cellEq k

example : cofibrations C u := comparisonCofibration d h δ f g u a b cellIndex labelEq rootEq cellEq hδ

example : Mono u := comparisonMono d h δ f g u a b cellIndex labelEq rootEq cellEq hδ

example : RegularMono u := comparisonRegularMono d h δ f g u a b cellIndex labelEq rootEq cellEq hδ

example {E B : C} (p : E ⟶ B) (hp : d.I.rlp p) : HasLiftingProperty u p :=
  comparisonHasLiftingProperty d h δ f g u a b cellIndex labelEq rootEq cellEq hδ p hp

example {E B : C} (p : E ⟶ B) (hp : d.I.rlp p) (α : X ⟶ E) (β : Y ⟶ B)
    (sq : CommSq α u p β) : ∃ ℓ : Y ⟶ E, u ≫ ℓ = α ∧ ℓ ≫ p = β := by
  let _ : HasLiftingProperty u p :=
    comparisonHasLiftingProperty d h δ f g u a b cellIndex labelEq rootEq cellEq hδ p hp
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

example {E B : C} (p : E ⟶ B) (hp : d.I.rlp p) (α : X ⟶ E) (β : Y ⟶ B)
    (sq : CommSq α u p β) (m : T ⟶ E) (hm : δ ≫ m = f ≫ α) (hmp : m ≫ p = g ≫ β) (i : b.ι) :
    ∃ n : (b.π i).1.right ⟶ E,
      d.I.homFamily (b.π i) ≫ n = boundary d b i ≫ m ∧ n ≫ p = b.cell i ≫ β ∧
        ∀ (k : a.ι) (e : cellIndex k = i),
          eqToHom (congrArg (fun x : d.I.toSet => x.1.right)
            ((labelEq k).trans (congrArg b.π e))) ≫ n = a.cell k ≫ α :=
  cellLiftExists d h δ f g u a b cellIndex labelEq rootEq cellEq p hp α β sq m hm hmp i

#print axioms HomotopicalAlgebra.CellularAttachmentComparison.boundary
#print axioms HomotopicalAlgebra.CellularAttachmentComparison.boundary_cell
#print axioms HomotopicalAlgebra.CellularAttachmentComparison.attachmentCofibration
#print axioms HomotopicalAlgebra.CellularAttachmentComparison.selectedBoundary
#print axioms HomotopicalAlgebra.CellularAttachmentComparison.cellLiftExists
#print axioms HomotopicalAlgebra.CellularAttachmentComparison.comparisonHasLiftingProperty
#print axioms HomotopicalAlgebra.CellularAttachmentComparison.comparisonCofibration
#print axioms HomotopicalAlgebra.CellularAttachmentComparison.comparisonMono
#print axioms HomotopicalAlgebra.CellularAttachmentComparison.comparisonRegularMono

end CellularAttachmentClients

namespace CellularUnionClients

open HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  {d : CofibrantGenerationData C κ} (h : CellularSource d)
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f)
  {I : Type w} (t : I → CellularSubcomplex c)

example : CellularSubcomplex c := CellularSubcomplex.union h t

example : (CellularSubcomplex.union h t).support = ⋃ i : I, (t i).support :=
  CellularSubcomplex.union_support h t

example : Cardinal.mk (CellularSubcomplex.union h t).complex.Cells ≤
    Cardinal.sum (fun i : I => Cardinal.mk (t i).complex.Cells) :=
  CellularSubcomplex.union_cells_cardinal_le h t

example (i : I) : (t i).hom ≫ CellularSubcomplex.unionInclusion h t i =
    (CellularSubcomplex.union h t).hom := CellularSubcomplex.unionInclusion_root h t i

example (i : I) : CellularSubcomplex.unionInclusion h t i ≫
    (CellularSubcomplex.union h t).inclusion = (t i).inclusion :=
  CellularSubcomplex.unionInclusion_ambient h t i

example (i : I) : cofibrations C (CellularSubcomplex.unionInclusion h t i) :=
  CellularSubcomplex.unionInclusion_cofibration h t i

example [Inhabited I] :
    Cardinal.mk (t default).support = Cardinal.mk (t default).complex.Cells :=
  (t default).support_cardinal

end CellularUnionClients

#print axioms HomotopicalAlgebra.RelativeCellComplex.exists_lift_through_mono
#print axioms HomotopicalAlgebra.CellularSubcomplex.support
#print axioms HomotopicalAlgebra.CellularSubcomplex.support_cardinal
#print axioms HomotopicalAlgebra.RelativeCellComplex.rootAtStage
#print axioms HomotopicalAlgebra.RelativeCellComplex.rootAtStage_map
#print axioms HomotopicalAlgebra.RelativeCellComplex.rootAtStage_incl
#print axioms HomotopicalAlgebra.RelativeCellComplex.Cells.toStage
#print axioms HomotopicalAlgebra.RelativeCellComplex.Cells.toStage_map
#print axioms HomotopicalAlgebra.RelativeCellComplex.Cells.toStage_incl
#print axioms HomotopicalAlgebra.CellularSubcomplex.originalCellTarget
#print axioms HomotopicalAlgebra.CellularSubcomplex.originalCellTarget_inclusion
#print axioms HomotopicalAlgebra.CellularSubcomplex.originalCellAtStage
#print axioms HomotopicalAlgebra.CellularSubcomplex.originalCellAtStage_map
#print axioms HomotopicalAlgebra.CellularSubcomplex.originalCellAtStage_incl
#print axioms HomotopicalAlgebra.CellularSubcomplex.originalCellAtStage_comparison
#print axioms HomotopicalAlgebra.CellularUnion.index
#print axioms HomotopicalAlgebra.CellularUnion.obj
#print axioms HomotopicalAlgebra.CellularUnion.root
#print axioms HomotopicalAlgebra.CellularUnion.inclusion
#print axioms HomotopicalAlgebra.CellularUnion.comparison
#print axioms HomotopicalAlgebra.CellularUnion.map
#print axioms HomotopicalAlgebra.CellularUnion.F
#print axioms HomotopicalAlgebra.CellularUnion.endpointCocone
#print axioms HomotopicalAlgebra.CellularUnion.endpointIsColimit
#print axioms HomotopicalAlgebra.CellularUnion.endpointComparisonCofibration
#print axioms HomotopicalAlgebra.CellularUnion.stageComparisonCofibration
#print axioms HomotopicalAlgebra.CellularUnion.wellOrderContinuous
#print axioms HomotopicalAlgebra.CellularUnion.sourceCell
#print axioms HomotopicalAlgebra.CellularUnion.targetCell
#print axioms HomotopicalAlgebra.CellularUnion.cell_square
#print axioms HomotopicalAlgebra.CellularUnion.stepDesc
#print axioms HomotopicalAlgebra.CellularUnion.attachingIsPushout
#print axioms HomotopicalAlgebra.CellularUnion.attachCells
#print axioms HomotopicalAlgebra.CellularUnion.botIso
#print axioms HomotopicalAlgebra.CellularUnion.complex
#print axioms HomotopicalAlgebra.CellularUnion.unionSubcomplex
#print axioms HomotopicalAlgebra.CellularUnion.pieceSubcomplex
#print axioms HomotopicalAlgebra.CellularUnion.union_support
#print axioms HomotopicalAlgebra.CellularUnion.union_cells_cardinal_le
#print axioms HomotopicalAlgebra.CellularSubcomplex.union
#print axioms HomotopicalAlgebra.CellularSubcomplex.unionInclusion
#print axioms HomotopicalAlgebra.CellularSubcomplex.unionInclusion_root
#print axioms HomotopicalAlgebra.CellularSubcomplex.unionInclusion_ambient
#print axioms HomotopicalAlgebra.CellularSubcomplex.union_support
#print axioms HomotopicalAlgebra.CellularSubcomplex.union_cells_cardinal_le
#print axioms HomotopicalAlgebra.CellularSubcomplex.unionInclusion_cofibration


namespace CellularEffectiveOnlyPromotedClients

open CategoryTheory Limits MorphismProperty Opposite
open HomotopicalAlgebra

namespace EffectiveFamilyClients

open CategoryTheory Limits MorphismProperty Opposite
open HomotopicalAlgebra HomotopicalAlgebra.EffectiveCellularSubcomplexExtension

section OriginalInclusion

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (h : EffectiveCofibrations C)
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f)
  (t : CellularSubcomplex c)

example : cofibrations C t.inclusion := inclusionCofibration d c h t

example : Mono t.inclusion := inclusionMono d c h t

example : RegularMono t.inclusion := inclusionRegularMono d c h t

example :
    IsLimit (Fork.ofι t.inclusion (pushout.condition (f := t.inclusion) (g := t.inclusion))) :=
  inclusionPushoutEqualizer d c h t

example (j : O) (hj : ¬ IsMax j) : Mono (c.F.map (homOfLE (Order.le_succ j))) :=
  originalSuccessorMono d c h j hj

example (j : O) (hj : ¬ IsMax j) (a : (t.complex.attachCells j hj).ι) :
    boundary d t.complex j hj a ≫ t.comparison.app j =
      eqToHom (congrArg (fun p : d.I.toSet => p.1.left) (t.label_eq j hj a)) ≫
        boundary d c j hj (t.cellIndex j hj a) :=
  subcomplexBoundary d c h t j hj a

end OriginalInclusion

section OriginalCompatibleFamily

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (h : EffectiveCofibrations C)
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f)
  {T : Type w} (t : T → CellularSubcomplex c) {E B : C}
  (α : ∀ i : T, (t i).endpoint ⟶ E) (q : E ⟶ B) (r : X ⟶ E) (β : Y ⟶ B)
  (hq : d.I.rlp q) (hrq : r ≫ q = f ≫ β)
  (hroot : ∀ i : T, (t i).hom ≫ α i = r)
  (hα : ∀ i : T, α i ≫ q = (t i).inclusion ≫ β)
  (hcells : FamilyCellCompatible d c t α)

example :
    ∃ ℓ : Y ⟶ E, f ≫ ℓ = r ∧ ℓ ≫ q = β ∧ ∀ i : T, (t i).inclusion ≫ ℓ = α i :=
  existsFamilyLift d c h t α q r β hq hrq hroot hα hcells

example : StageState d c t α q r β ⊥ := bottomState d c t α q r β hrq hroot

example (j : O) (hj : ¬ IsMax j) (s : StageState d c t α q r β j) :
    StageState d c t α q r β (Order.succ j) :=
  successorState d c h t α q r β hq hcells hα j hj s

example (j : O) (hj : ¬ IsMax j) (s : StageState d c t α q r β j) :
    (stageFunctor d c t α q r β).map (homOfLE (Order.le_succ j)).op
      (successorState d c h t α q r β hq hcells hα j hj s) = s :=
  successorState_restrict d c h t α q r β hq hcells hα j hj s

example : (stageFunctor d c t α q r β).sections :=
  (familyInductionData d c h t α q r β hq hcells hα).sectionsMk
    (bottomState d c t α q r β hrq hroot)

example (j : O) (hj : ¬ IsMax j) (s : StageState d c t α q r β j)
    (i : T) (a : ((t i).complex.attachCells j hj).ι) :
    eqToHom (congrArg (fun p : d.I.toSet => p.1.right) ((t i).label_eq j hj a)) ≫
      completionCellImage d c t α q r β hq j hj s ((t i).cellIndex j hj a) =
        ((t i).complex.attachCells j hj).cell a ≫ (t i).complex.incl.app (Order.succ j) ≫ α i :=
  completionCellImage_family d c t α q r β hq hcells j hj s i a

example (j : O) (hj : ¬ IsMax j) (k : (c.attachCells j hj).ι)
    (hk : Selected d c t j hj k) (i : T) (a : ((t i).complex.attachCells j hj).ι)
    (e : (t i).cellIndex j hj a = k) :
    eqToHom (congrArg (fun a => ((c.attachCells j hj).π a).1.right) e) ≫
      selectedCellImage d c t α j hj k hk = familyCellImage d c t α j hj i a :=
  selectedCellImage_eq d c t α hcells j hj k hk i a e

end OriginalCompatibleFamily

#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.boundary
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.boundary_cell
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.originalSuccessorCofibration
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.originalSuccessorMono
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.generatorTransport
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.subcomplexBoundary
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.familyCellImage
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.FamilyCellCompatible
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.Selected
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.selectedCellImage
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.selectedCellImage_eq
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.familyCellImage_boundary
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.familyCellImage_right
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.selectedCellImage_boundary
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.selectedCellImage_right
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.StageState
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.stageMap
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.stageFunctor
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.missingCellSquare
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.completionCellImage
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.completionCellImage_boundary
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.completionCellImage_right
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.completionCellImage_family
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.completionCofanMap
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.completionCofanMap_inj
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.successorLift
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.successorLift_stage
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.successorLift_cell
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.bottomState
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.successorState
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.successorState_restrict
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.ordinaryLimitFamily
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.limitState
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.limitState_restrict
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.familyInductionData
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.existsFamilyLift
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.inclusionCofibration
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.inclusionMono
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.inclusionRegularMono
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.inclusionPushoutEqualizer

end EffectiveFamilyClients

namespace EffectivePrefixClients

open CategoryTheory Limits MorphismProperty Opposite
open HomotopicalAlgebra HomotopicalAlgebra.EffectiveCellularSubcomplexExtension

section OriginalPrefix

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f) (j : O)

example : (prefixComplex d c j).F = (Set.initialSegIic j).monotone.functor ⋙ c.F :=
  prefixComplex_functor d c j

example : (prefixComplex d c j).isoBot = c.isoBot := prefixComplex_isoBot d c j

example (a : Set.Iic j) : (prefixComplex d c j).incl.app a = c.F.map (homOfLE a.2) :=
  prefixComplex_incl d c j a

example (a : Set.Iic j) (ha : ¬ IsMax a) :
    ((prefixComplex d c j).attachCells a ha).cofan₁ = (c.attachCells a.1 (prefixNotMax a ha)).cofan₁ :=
  prefixComplex_sourceCofan d c j a ha

example (a : Set.Iic j) (ha : ¬ IsMax a) :
    ((prefixComplex d c j).attachCells a ha).cofan₂ = (c.attachCells a.1 (prefixNotMax a ha)).cofan₂ :=
  prefixComplex_targetCofan d c j a ha

example (a : Set.Iic j) (ha : ¬ IsMax a) :
    ((prefixComplex d c j).attachCells a ha).m = (c.attachCells a.1 (prefixNotMax a ha)).m :=
  prefixComplex_attachingMap d c j a ha

example (a : Set.Iic j) (ha : ¬ IsMax a) (k : (c.attachCells a.1 (prefixNotMax a ha)).ι) :
    ((prefixComplex d c j).attachCells a ha).π k = (c.attachCells a.1 (prefixNotMax a ha)).π k :=
  prefixComplex_label d c j a ha k

example (a : Set.Iic j) (ha : ¬ IsMax a) (k : (c.attachCells a.1 (prefixNotMax a ha)).ι) :
    boundary d (prefixComplex d c j) a ha k = boundary d c a.1 (prefixNotMax a ha) k :=
  prefixComplex_boundary d c j a ha k

example (a : Set.Iic j) (ha : ¬ IsMax a) (k : (c.attachCells a.1 (prefixNotMax a ha)).ι) :
    ((prefixComplex d c j).attachCells a ha).cell k =
      (c.attachCells a.1 (prefixNotMax a ha)).cell k ≫ c.F.map (eqToHom (prefixSuccessorEq a ha).symm) :=
  prefixComplex_cell d c j a ha k

example (a : Set.Iic j) (ha : ¬ IsMax a) (k : (c.attachCells a.1 (prefixNotMax a ha)).ι) :
    (({ j := a, hj := ha, k := k } : (prefixComplex d c j).Cells)).ι =
      (c.attachCells a.1 (prefixNotMax a ha)).cell k ≫
        c.F.map (homOfLE (Order.succ_le_of_lt (prefixStage_lt_endpoint a ha))) :=
  prefixComplex_cell_inclusion d c j a ha k

variable (t : CellularSubcomplex c)

example : (prefixSubcomplex d c t j).endpoint = t.complex.F.obj j :=
  prefixSubcomplex_endpoint d c t j

example : (prefixSubcomplex d c t j).inclusion = t.comparison.app j :=
  prefixSubcomplex_inclusion d c t j

example (a : Set.Iic j) (ha : ¬ IsMax a) :
    (prefixSubcomplex d c t j).cellIndex a ha = t.cellIndex a.1 (prefixNotMax a ha) :=
  prefixSubcomplex_cellIndex d c t j a ha

example : (prefixSubcomplex d c t j).complex = prefixComplex d t.complex j := rfl

example : (prefixSubcomplex d c t j).comparison =
    Functor.whiskerLeft (Set.initialSegIic j).monotone.functor t.comparison := rfl

example : (prefixSubcomplex d c t j).hom =
    t.complex.isoBot.inv ≫ t.complex.F.map (homOfLE (bot_le : (⊥ : O) ≤ j)) := rfl

example :
    (t.complex.isoBot.inv ≫ t.complex.F.map (homOfLE (bot_le : (⊥ : O) ≤ j))) ≫
        t.comparison.app j = c.isoBot.inv ≫ c.F.map (homOfLE (bot_le : (⊥ : O) ≤ j)) :=
  (prefixSubcomplex d c t j).fac

variable (h : EffectiveCofibrations C)

example : cofibrations C (t.comparison.app j) := by
  simpa only [prefixSubcomplex_endpoint, prefixSubcomplex_inclusion] using
    inclusionCofibration d (prefixComplex d c j) h (prefixSubcomplex d c t j)

example : Mono (t.comparison.app j) := by
  simpa only [prefixSubcomplex_endpoint, prefixSubcomplex_inclusion] using
    inclusionMono d (prefixComplex d c j) h (prefixSubcomplex d c t j)

example : RegularMono (t.comparison.app j) := by
  simpa only [prefixSubcomplex_endpoint, prefixSubcomplex_inclusion] using
    inclusionRegularMono d (prefixComplex d c j) h (prefixSubcomplex d c t j)

end OriginalPrefix

section FamilyAtActualOriginalStage

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (h : EffectiveCofibrations C)
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f)
  (j : O) {T : Type w} (t : T → CellularSubcomplex c) {E B : C}
  (α : ∀ i : T, (t i).complex.F.obj j ⟶ E) (q : E ⟶ B) (r : X ⟶ E) (β : c.F.obj j ⟶ B)
  (hq : d.I.rlp q)
  (hrq : r ≫ q = (c.isoBot.inv ≫ c.F.map (homOfLE (bot_le : (⊥ : O) ≤ j))) ≫ β)
  (hroot : ∀ i : T, (prefixSubcomplex d c (t i) j).hom ≫ α i = r)
  (hα : ∀ i : T, α i ≫ q = (t i).comparison.app j ≫ β)
  (hcells : FamilyCellCompatible d (prefixComplex d c j)
    (fun i : T => prefixSubcomplex d c (t i) j) α)

example :
    ∃ ℓ : c.F.obj j ⟶ E,
      (c.isoBot.inv ≫ c.F.map (homOfLE (bot_le : (⊥ : O) ≤ j))) ≫ ℓ = r ∧
        ℓ ≫ q = β ∧ ∀ i : T, (t i).comparison.app j ≫ ℓ = α i :=
  existsFamilyLift d (prefixComplex d c j) h (fun i => prefixSubcomplex d c (t i) j)
    α q r β hq hrq hroot hα hcells

end FamilyAtActualOriginalStage

#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixNotMax
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixStage_lt_endpoint
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixSuccessorEq
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixShape
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixStepIso
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex_functor
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex_isoBot
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex_incl
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex_sourceCofan
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex_targetCofan
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex_label
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex_attachingMap
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex_boundary
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex_cell
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex_cell_inclusion
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixSubcomplex
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixSubcomplex_endpoint
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixSubcomplex_inclusion
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixSubcomplex_cellIndex

end EffectivePrefixClients

namespace EffectiveContainmentClients

open CategoryTheory Limits MorphismProperty Opposite
open HomotopicalAlgebra HomotopicalAlgebra.EffectiveCellularSubcomplexContainment

section OriginalSupport

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f)
  (t u : CellularSubcomplex c) (H : SupportLE d c t u)

example : Set.range t.originalCell ⊆ Set.range u.originalCell := H

example : SupportLE d c t t := supportRefl d c t

example (v : CellularSubcomplex c) (K : SupportLE d c u v) : SupportLE d c t v :=
  supportTrans d c t u v H K

example (a : t.complex.Cells) : u.originalCell (supportCell d c t u H a) = t.originalCell a :=
  supportCell_original d c t u H a

example (a : t.complex.Cells) : (supportCell d c t u H a).j = a.j :=
  supportCell_stage d c t u H a

example : t.complex.Cells ↪ u.complex.Cells := supportCellEmbedding d c t u H

example (j : O) (hj : ¬ IsMax j) (k : (t.complex.attachCells j hj).ι) :
    u.cellIndex j hj (stageCell d c t u H j hj k) = t.cellIndex j hj k :=
  stageCell_original d c t u H j hj k

example (j : O) (hj : ¬ IsMax j) (k : (t.complex.attachCells j hj).ι) :
    (t.complex.attachCells j hj).π k = (u.complex.attachCells j hj).π (stageCell d c t u H j hj k) :=
  stageCell_label d c t u H j hj k

variable (h : EffectiveCofibrations C)

example : t.hom ≫ containmentMap d c t u h H = u.hom := containmentMap_root d c t u h H

example : containmentMap d c t u h H ≫ u.inclusion = t.inclusion := containmentMap_ambient d c t u h H

example (a : t.complex.Cells) (b : u.complex.Cells) (hab : u.originalCell b = t.originalCell a) :
    a.ι ≫ containmentMap d c t u h H = cellMapInto d c t u a b hab :=
  containmentMap_cell d c t u h H a b hab

example (m : t.endpoint ⟶ u.endpoint) (hm : m ≫ u.inclusion = t.inclusion) :
    m = containmentMap d c t u h H := containmentMap_unique d c t u h H m hm

example : CellularSubcomplex u.complex := asSubcomplex d c t u h H

example : (asSubcomplex d c t u h H).complex = t.complex := asSubcomplex_complex d c t u h H

example : (asSubcomplex d c t u h H).inclusion = containmentMap d c t u h H :=
  asSubcomplex_inclusion d c t u h H

example : (asSubcomplex d c t u h H).comparison = comparison d c t u h H :=
  asSubcomplex_comparison d c t u h H

example : cofibrations C (containmentMap d c t u h H) := containmentMap_cofibration d c t u h H

example : Mono (containmentMap d c t u h H) := containmentMap_mono d c t u h H

example : RegularMono (containmentMap d c t u h H) := containmentMapRegularMono d c t u h H

example (j : O) : stageMap d c t u h H j ≫ u.comparison.app j = t.comparison.app j :=
  stageMap_ambient d c t u h H j

example (j : O) :
    (t.complex.isoBot.inv ≫ t.complex.F.map (homOfLE (bot_le : (⊥ : O) ≤ j))) ≫
        stageMap d c t u h H j =
      u.complex.isoBot.inv ≫ u.complex.F.map (homOfLE (bot_le : (⊥ : O) ≤ j)) :=
  stageMap_root d c t u h H j

example (j : O) (hj : ¬ IsMax j) (k : (t.complex.attachCells j hj).ι) :
    (t.complex.attachCells j hj).cell k ≫ stageMap d c t u h H (Order.succ j) =
      eqToHom (congrArg (fun p : d.I.toSet => p.1.right) (stageCell_label d c t u H j hj k)) ≫
        (u.complex.attachCells j hj).cell (stageCell d c t u H j hj k) :=
  stageMap_cell d c t u h H j hj k

example (j : O) (m : t.complex.F.obj j ⟶ u.complex.F.obj j)
    (hm : m ≫ u.comparison.app j = t.comparison.app j) : m = stageMap d c t u h H j :=
  stageMap_unique d c t u h H j m hm

example (j : O) : cofibrations C (stageMap d c t u h H j) := stageMap_cofibration d c t u h H j

example (j : O) : RegularMono (stageMap d c t u h H j) := stageMapRegularMono d c t u h H j

example : comparison d c t u h H ≫ u.comparison = t.comparison := comparison_ambient d c t u h H

example (j : O) : t.complex.incl.app j ≫ containmentMap d c t u h H =
    (comparison d c t u h H).app j ≫ u.complex.incl.app j := comparison_endpoint d c t u h H j

example (a : t.complex.F ⟶ u.complex.F) (ha : a ≫ u.comparison = t.comparison) :
    a = comparison d c t u h H := comparison_unique d c t u h H a ha

example : containmentMap d c t t h (supportRefl d c t) = 𝟙 t.endpoint :=
  containmentMap_refl d c t h (supportRefl d c t)

example (v : CellularSubcomplex c) (K : SupportLE d c u v) :
    containmentMap d c t u h H ≫ containmentMap d c u v h K =
      containmentMap d c t v h (supportTrans d c t u v H K) :=
  containmentMap_comp d c t u h v H K

example (v : CellularSubcomplex c) (K : SupportLE d c u v) (j : O) :
    stageMap d c t u h H j ≫ stageMap d c u v h K j =
      stageMap d c t v h (supportTrans d c t u v H K) j := stageMap_comp d c t u h v H K j

example (v : CellularSubcomplex c) (K : SupportLE d c u v) :
    comparison d c t u h H ≫ comparison d c u v h K =
      comparison d c t v h (supportTrans d c t u v H K) := comparison_comp d c t u h v H K

end OriginalSupport

section EqualOriginalSupports

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f)
  (t u : CellularSubcomplex c) (h : EffectiveCofibrations C)
  (e : Set.range t.originalCell = Set.range u.originalCell)

example : t.endpoint ≅ u.endpoint := endpointIso d c t u h e

example (j : O) : t.complex.F.obj j ≅ u.complex.F.obj j := stageIso d c t u h e j

example : t.complex.F ≅ u.complex.F := comparisonIso d c t u h e

example : t.hom ≫ (endpointIso d c t u h e).hom = u.hom := endpointIso_root d c t u h e

example : (endpointIso d c t u h e).hom ≫ u.inclusion = t.inclusion := endpointIso_ambient d c t u h e

example (a : t.complex.Cells) (b : u.complex.Cells) (hab : u.originalCell b = t.originalCell a) :
    a.ι ≫ (endpointIso d c t u h e).hom = cellMapInto d c t u a b hab := endpointIso_cell d c t u h e a b hab

example (j : O) : (stageIso d c t u h e j).hom ≫ u.comparison.app j = t.comparison.app j :=
  stageIso_ambient d c t u h e j

example (j : O) : t.complex.incl.app j ≫ (endpointIso d c t u h e).hom =
    (stageIso d c t u h e j).hom ≫ u.complex.incl.app j := isomorphism_endpoint d c t u h e j

example : (comparisonIso d c t u h e).hom ≫ u.comparison = t.comparison := comparisonIso_ambient d c t u h e

end EqualOriginalSupports

#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.SupportLE
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.supportRefl
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.supportTrans
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.originalCell_injective
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.supportCell
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.supportCell_original
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.supportCell_stage
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.supportCellEmbedding
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.cellLabelEq
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.ambientCell_transport
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.cellMapInto
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.cellMapInto_ambient
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.occurrenceEmbedding
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.existsStageCell
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageCell
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageCell_original
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageCellEmbedding
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageCell_label
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.prefixSupportLE
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.ambientStageCell_transport
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageCellMap_ambient
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.existsContainmentMap
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.containmentMap
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.containmentMap_ambient
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.containmentMap_root
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.containmentMap_unique
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.containmentMap_cell
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageComparisonMono
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMap
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMap_ambient
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMap_unique
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMap_cell
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMap_naturality
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.comparison
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.comparison_ambient
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.comparison_endpoint
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.comparison_bot
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.comparison_unique
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.asSubcomplex
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.asSubcomplex_complex
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.asSubcomplex_inclusion
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.asSubcomplex_comparison
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.containmentMap_cofibration
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.containmentMap_mono
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.containmentMapRegularMono
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMap_cofibration
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMap_mono
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMapRegularMono
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMap_root
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.containmentMap_refl
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.containmentMap_comp
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMap_refl
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMap_comp
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.comparison_refl
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.comparison_comp
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.endpointIso
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageIso
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.comparisonIso
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.endpointIso_root
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.endpointIso_ambient
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageIso_ambient
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.comparisonIso_ambient
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.isomorphism_endpoint
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.endpointIso_cell
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageIso_root
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageIso_cell

end EffectiveContainmentClients

namespace EffectiveUnionClients

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  (eff : cofibrations C ≤ MorphismProperty.regularMono C)
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f)
  {I : Type w} (t : I → CellularSubcomplex c)

example : CellularSubcomplex c := EffectiveCellularSubcomplex.union d eff t

example : (EffectiveCellularSubcomplex.union d eff t).support = ⋃ i : I, (t i).support :=
  EffectiveCellularSubcomplex.union_support d eff t

example : Cardinal.mk (EffectiveCellularSubcomplex.union d eff t).complex.Cells ≤
    Cardinal.sum (fun i : I => Cardinal.mk (t i).complex.Cells) :=
  EffectiveCellularSubcomplex.union_cells_cardinal_le d eff t

example : Cardinal.mk (EffectiveCellularSubcomplex.union d eff t).support ≤
    Cardinal.sum (fun i : I => Cardinal.mk (t i).support) :=
  EffectiveCellularSubcomplex.union_support_cardinal_le d eff t

example (i : I) : (t i).hom ≫ EffectiveCellularSubcomplex.unionInclusion d eff t i =
    (EffectiveCellularSubcomplex.union d eff t).hom :=
  EffectiveCellularSubcomplex.unionInclusion_root d eff t i

example (i : I) : EffectiveCellularSubcomplex.unionInclusion d eff t i ≫
    (EffectiveCellularSubcomplex.union d eff t).inclusion = (t i).inclusion :=
  EffectiveCellularSubcomplex.unionInclusion_ambient d eff t i

example (i : I) : cofibrations C (EffectiveCellularSubcomplex.unionInclusion d eff t i) :=
  EffectiveCellularSubcomplex.unionInclusion_cofibration d eff t i

example (i : I) : Mono (EffectiveCellularSubcomplex.unionInclusion d eff t i) :=
  EffectiveCellularSubcomplex.unionInclusion_mono d eff t i

example (i : I) : RegularMono (EffectiveCellularSubcomplex.unionInclusion d eff t i) :=
  EffectiveCellularSubcomplex.unionInclusionRegularMono d eff t i

example : cofibrations C (EffectiveCellularSubcomplex.union d eff t).inclusion :=
  EffectiveCellularSubcomplex.union_cofibration d eff t

example : Mono (EffectiveCellularSubcomplex.union d eff t).inclusion :=
  EffectiveCellularSubcomplex.union_mono d eff t

example : RegularMono (EffectiveCellularSubcomplex.union d eff t).inclusion :=
  EffectiveCellularSubcomplex.unionRegularMono d eff t

example (j : O) : (EffectiveCellularSubcomplexExtension.prefixComplex d c j).isoBot = c.isoBot :=
  EffectiveCellularSubcomplexExtension.prefixComplex_isoBot d c j

end EffectiveUnionClients

#print axioms HomotopicalAlgebra.EffectiveCofibrations
#print axioms HomotopicalAlgebra.EffectiveCofibrations.effectivePresentation
#print axioms HomotopicalAlgebra.EffectiveCofibrations.mono_of_cofibration
#print axioms HomotopicalAlgebra.EffectiveCofibrations.originalPushoutEqualizer
#print axioms HomotopicalAlgebra.EffectiveCellularUnion.index
#print axioms HomotopicalAlgebra.EffectiveCellularUnion.F
#print axioms HomotopicalAlgebra.EffectiveCellularUnion.endpointCocone
#print axioms HomotopicalAlgebra.EffectiveCellularUnion.endpointIsColimit
#print axioms HomotopicalAlgebra.EffectiveCellularUnion.endpointComparisonCofibration
#print axioms HomotopicalAlgebra.EffectiveCellularUnion.stageComparisonCofibration
#print axioms HomotopicalAlgebra.EffectiveCellularUnion.wellOrderContinuous
#print axioms HomotopicalAlgebra.EffectiveCellularUnion.cell_square
#print axioms HomotopicalAlgebra.EffectiveCellularUnion.attachingIsPushout
#print axioms HomotopicalAlgebra.EffectiveCellularUnion.attachCells
#print axioms HomotopicalAlgebra.EffectiveCellularUnion.botIso
#print axioms HomotopicalAlgebra.EffectiveCellularUnion.complex
#print axioms HomotopicalAlgebra.EffectiveCellularUnion.unionSubcomplex
#print axioms HomotopicalAlgebra.EffectiveCellularUnion.pieceSubcomplex
#print axioms HomotopicalAlgebra.EffectiveCellularUnion.union_support
#print axioms HomotopicalAlgebra.EffectiveCellularUnion.union_cells_cardinal_le
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplex.union
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplex.unionInclusion
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplex.unionInclusion_root
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplex.unionInclusion_ambient
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplex.union_support
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplex.union_cells_cardinal_le
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplex.unionInclusion_cofibration
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplex.unionInclusion_mono
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplex.unionInclusionRegularMono
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplex.union_cofibration
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplex.union_mono
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplex.unionRegularMono
#print axioms HomotopicalAlgebra.EffectiveCellularSubcomplex.union_support_cardinal_le


end CellularEffectiveOnlyPromotedClients


namespace GenericPrefixCanonicalClients

open CategoryTheory Limits MorphismProperty Opposite
open HomotopicalAlgebra
open HomotopicalAlgebra.RelativeCellComplex.GenericPrefix
open HomotopicalAlgebra.CellularSubcomplexExtension (prefixNotMax prefixSuccessorEq prefixStage_lt_endpoint)

namespace GenericRelativeCellPrefixClients

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C}
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => P.homFamily) f) (j : O)

example : RelativeCellComplex.{w} (fun _ : Set.Iic j => P.homFamily)
    (c.isoBot.inv ≫ c.F.map (homOfLE (bot_le : (⊥ : O) ≤ j))) := prefixComplex c j

example : (prefixComplex c j).F = (Set.initialSegIic j).monotone.functor ⋙ c.F :=
  prefixComplex_functor c j

example : (prefixComplex c j).isoBot = c.isoBot := prefixComplex_isoBot c j

example (a : Set.Iic j) : (prefixComplex c j).incl.app a = c.F.map (homOfLE a.2) :=
  prefixComplex_incl c j a

example : IsColimit (Cocone.mk (c.F.obj j) (prefixComplex c j).incl) := (prefixComplex c j).isColimit

example : (prefixComplex c j).isoBot.inv ≫ (prefixComplex c j).incl.app ⊥ = root c j :=
  (prefixComplex c j).fac

example (a : Set.Iic j) (ha : ¬ IsMax a) :
    ((prefixComplex c j).attachCells a ha).ι = (c.attachCells a.1 (prefixNotMax a ha)).ι :=
  prefixComplex_occurrences c j a ha

example (a : Set.Iic j) (ha : ¬ IsMax a) :
    ((prefixComplex c j).attachCells a ha).cofan₁ = (c.attachCells a.1 (prefixNotMax a ha)).cofan₁ :=
  prefixComplex_sourceCofan c j a ha

example (a : Set.Iic j) (ha : ¬ IsMax a) :
    ((prefixComplex c j).attachCells a ha).cofan₂ = (c.attachCells a.1 (prefixNotMax a ha)).cofan₂ :=
  prefixComplex_targetCofan c j a ha

example (a : Set.Iic j) (ha : ¬ IsMax a) (k : (c.attachCells a.1 (prefixNotMax a ha)).ι) :
    ((prefixComplex c j).attachCells a ha).π k = (c.attachCells a.1 (prefixNotMax a ha)).π k :=
  prefixComplex_label c j a ha k

example (a : Set.Iic j) (ha : ¬ IsMax a) :
    ((prefixComplex c j).attachCells a ha).m = (c.attachCells a.1 (prefixNotMax a ha)).m :=
  prefixComplex_attachingMap c j a ha

example (a : Set.Iic j) (ha : ¬ IsMax a) :
    ((prefixComplex c j).attachCells a ha).g₁ = (c.attachCells a.1 (prefixNotMax a ha)).g₁ :=
  prefixComplex_sourceMap c j a ha

example (a : Set.Iic j) (ha : ¬ IsMax a) :
    ((prefixComplex c j).attachCells a ha).g₂ = (c.attachCells a.1 (prefixNotMax a ha)).g₂ ≫
      c.F.map (eqToHom (prefixSuccessorEq a ha).symm) := prefixComplex_targetMap c j a ha

example (a : Set.Iic j) (ha : ¬ IsMax a) (k : (c.attachCells a.1 (prefixNotMax a ha)).ι) :
    ((prefixComplex c j).attachCells a ha).cofan₁.inj k ≫ ((prefixComplex c j).attachCells a ha).g₁ =
      (c.attachCells a.1 (prefixNotMax a ha)).cofan₁.inj k ≫ (c.attachCells a.1 (prefixNotMax a ha)).g₁ :=
  prefixComplex_boundary c j a ha k

example (a : Set.Iic j) (ha : ¬ IsMax a) (k : (c.attachCells a.1 (prefixNotMax a ha)).ι) :
    ((prefixComplex c j).attachCells a ha).cell k = (c.attachCells a.1 (prefixNotMax a ha)).cell k ≫
      c.F.map (eqToHom (prefixSuccessorEq a ha).symm) := prefixComplex_cell c j a ha k

example : (prefixComplex c j).Cells ≃ {a : c.Cells // a.j < j} := cellsEquiv c j

example (a : (prefixComplex c j).Cells) : (originalCell c j a).j = a.j.1 := rfl

example (a : (prefixComplex c j).Cells) : a.i = (originalCell c j a).i := originalCell_label c j a

example (a : (prefixComplex c j).Cells) :
    a.ι = (originalCell c j a).toStage j (originalCell_stage_lt c j a) := originalCell_toStage c j a

example (a : (prefixComplex c j).Cells) : a.ι ≫ c.incl.app j = (originalCell c j a).ι :=
  originalCell_inclusion c j a

example : Cardinal.mk (prefixComplex c j).Cells = Cardinal.mk {a : c.Cells // a.j < j} := cells_cardinal c j

example : Cardinal.mk (prefixComplex c j).Cells ≤ Cardinal.mk c.Cells := cells_cardinal_le c j

example : root c j ≫ c.incl.app j = f := root_endpoint c j

end GenericRelativeCellPrefixClients


#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericPrefix.root
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericPrefix.prefixShape
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericPrefix.prefixStepIso
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericPrefix.prefixComplex
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericPrefix.prefixComplex_functor
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericPrefix.prefixComplex_isoBot
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericPrefix.prefixComplex_incl
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericPrefix.prefixComplex_sourceCofan
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericPrefix.prefixComplex_targetCofan
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericPrefix.prefixComplex_occurrences
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericPrefix.prefixComplex_label
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericPrefix.prefixComplex_attachingMap
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericPrefix.prefixComplex_sourceMap
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericPrefix.prefixComplex_targetMap
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericPrefix.prefixComplex_boundary
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericPrefix.prefixComplex_cell
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericPrefix.prefixComplex_cell_inclusion
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericPrefix.originalCell
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericPrefix.originalCell_stage_lt
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericPrefix.cellsEquiv
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericPrefix.cellEmbedding
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericPrefix.cellEmbedding_original
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericPrefix.originalCell_label
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericPrefix.originalCell_toStage
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericPrefix.originalCell_inclusion
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericPrefix.cells_cardinal
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericPrefix.cells_cardinal_le
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericPrefix.root_endpoint

end GenericPrefixCanonicalClients

namespace GenericCompletionCanonicalClients

open CategoryTheory Limits MorphismProperty Opposite
open HomotopicalAlgebra
open HomotopicalAlgebra.RelativeCellComplex.GenericCompletion

namespace GenericRelativeCellCompletionClients

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C}
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => P.homFamily) f)
  {D₁ D₂ : PEmpty.{w + 1} → C} (e₁ : Cofan D₁) (e₂ : Cofan D₂)
  (he₁ : IsColimit e₁) (he₂ : IsColimit e₂)

example : RelativeCellComplex.{w} (fun _ : WithTop O => P.homFamily) f := complex c e₁ e₂ he₁ he₂

example (a : O) : (complex c e₁ e₂ he₁ he₂).F.obj (a : WithTop O) = c.F.obj a :=
  complex_obj_coe c e₁ e₂ he₁ he₂ a

example : (complex c e₁ e₂ he₁ he₂).F.obj ⊤ = Y := complex_obj_top c e₁ e₂ he₁ he₂

example : (complex c e₁ e₂ he₁ he₂).isoBot = c.isoBot := complex_isoBot c e₁ e₂ he₁ he₂

example (a : O) : (complex c e₁ e₂ he₁ he₂).incl.app (a : WithTop O) = c.incl.app a :=
  complex_incl_coe c e₁ e₂ he₁ he₂ a

example : (complex c e₁ e₂ he₁ he₂).incl.app ⊤ = 𝟙 Y := complex_incl_top c e₁ e₂ he₁ he₂

example : (complex c e₁ e₂ he₁ he₂).isoBot.inv ≫ (complex c e₁ e₂ he₁ he₂).incl.app ⊥ = f :=
  (complex c e₁ e₂ he₁ he₂).fac

example : IsColimit (Cocone.mk Y (complex c e₁ e₂ he₁ he₂).incl) := (complex c e₁ e₂ he₁ he₂).isColimit

example (a : O) (ha : ¬ IsMax a) (hnew : ¬ IsMax (a : WithTop O)) :
    (complex c e₁ e₂ he₁ he₂).attachCells (a : WithTop O) hnew =
      (c.attachCells a ha).ofArrowIso (stepIso c a ha) := attach_nonmax c e₁ e₂ he₁ he₂ a ha hnew

example (a : O) (ha : IsMax a) (hnew : ¬ IsMax (a : WithTop O)) :
    ((complex c e₁ e₂ he₁ he₂).attachCells (a : WithTop O) hnew).ι = PEmpty.{w + 1} :=
  cells_max c e₁ e₂ he₁ he₂ a ha hnew

example : (complex c e₁ e₂ he₁ he₂).Cells ≃ c.Cells := cellsEquiv c e₁ e₂ he₁ he₂

example : Cardinal.mk (complex c e₁ e₂ he₁ he₂).Cells = Cardinal.mk c.Cells :=
  cells_cardinal c e₁ e₂ he₁ he₂

example (a : c.Cells) : (completedCell c e₁ e₂ he₁ he₂ a).i = a.i := completedCell_label c e₁ e₂ he₁ he₂ a

example (a : c.Cells) : (completedCell c e₁ e₂ he₁ he₂ a).ι =
    eqToHom (congrArg (fun p : P.toSet => p.1.right) (completedCell_label c e₁ e₂ he₁ he₂ a)) ≫ a.ι :=
  completedCell_inclusion c e₁ e₂ he₁ he₂ a

example (a : (complex c e₁ e₂ he₁ he₂).Cells) : ((cellsEquiv c e₁ e₂ he₁ he₂ a).j : WithTop O) = a.j :=
  originalCell_stage c e₁ e₂ he₁ he₂ a

example (a : (complex c e₁ e₂ he₁ he₂).Cells) : a.i = (cellsEquiv c e₁ e₂ he₁ he₂ a).i :=
  originalCell_label c e₁ e₂ he₁ he₂ a

example (a : O) (ha : ¬ IsMax a) (hnew : ¬ IsMax (a : WithTop O)) :
    ((complex c e₁ e₂ he₁ he₂).attachCells (a : WithTop O) hnew).cofan₁ ≍ (c.attachCells a ha).cofan₁ :=
  sourceCofan_nonmax_heq c e₁ e₂ he₁ he₂ a ha hnew

example (a : O) (ha : ¬ IsMax a) (hnew : ¬ IsMax (a : WithTop O)) :
    ((complex c e₁ e₂ he₁ he₂).attachCells (a : WithTop O) hnew).cofan₂ ≍ (c.attachCells a ha).cofan₂ :=
  targetCofan_nonmax_heq c e₁ e₂ he₁ he₂ a ha hnew

example (a : O) (ha : ¬ IsMax a) (hnew : ¬ IsMax (a : WithTop O)) :
    ((complex c e₁ e₂ he₁ he₂).attachCells (a : WithTop O) hnew).m ≍ (c.attachCells a ha).m :=
  attachingMap_nonmax_heq c e₁ e₂ he₁ he₂ a ha hnew

example : IsColimit ((Set.principalSegIio (⊤ : WithTop O)).cocone (completedShape c).F) :=
  CategoryTheory.TransfiniteCompositionOfShape.GenericCompletion.topPrefixIsColimit c.toTransfiniteCompositionOfShape

example (a : O) (ha : IsMax a) : IsIso (c.incl.app a) :=
  CategoryTheory.TransfiniteCompositionOfShape.GenericCompletion.originalMaxEndpoint_isIso
    c.toTransfiniteCompositionOfShape a ha

section NoMaximum

variable [NoMaxOrder O]

example : RelativeCellComplex.{w} (fun _ : WithTop O => P.homFamily) f := noMaxComplex c

example : (noMaxComplex c).F.obj ⊤ = Y := noMaxComplex_obj_top c

example : (noMaxComplex c).isoBot = c.isoBot := noMaxComplex_isoBot c

example (a : O) : (noMaxComplex c).incl.app (a : WithTop O) = c.incl.app a := noMaxComplex_incl_coe c a

example : (noMaxComplex c).incl.app ⊤ = 𝟙 Y := noMaxComplex_incl_top c

example : (noMaxComplex c).Cells ≃ c.Cells := noMaxCellsEquiv c

example : Cardinal.mk (noMaxComplex c).Cells = Cardinal.mk c.Cells := noMaxCells_cardinal c

example (a : O) (hnew : ¬ IsMax (a : WithTop O)) :
    ((noMaxComplex c).attachCells (a : WithTop O) hnew).cofan₁ = (c.attachCells a (not_isMax a)).cofan₁ :=
  noMaxComplex_sourceCofan c a hnew

example (a : O) (hnew : ¬ IsMax (a : WithTop O)) :
    ((noMaxComplex c).attachCells (a : WithTop O) hnew).cofan₂ = (c.attachCells a (not_isMax a)).cofan₂ :=
  noMaxComplex_targetCofan c a hnew

example (a : O) (hnew : ¬ IsMax (a : WithTop O)) :
    ((noMaxComplex c).attachCells (a : WithTop O) hnew).m = (c.attachCells a (not_isMax a)).m :=
  noMaxComplex_attachingMap c a hnew

example (a : c.Cells) : (completedNoMaxCell c a).i = a.i := completedNoMaxCell_label c a

example (a : c.Cells) : (completedNoMaxCell c a).ι = a.ι := completedNoMaxCell_inclusion c a

example (a : (noMaxComplex c).Cells) : ((noMaxCellsEquiv c a).j : WithTop O) = a.j := originalNoMaxCell_stage c a

example (a : (noMaxComplex c).Cells) : a.i = (noMaxCellsEquiv c a).i := originalNoMaxCell_label c a

end NoMaximum

end GenericRelativeCellCompletionClients



#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.attachmentLabel_of_eq
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.attachmentCell_of_eq
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.completedShape
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.stepIso
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.maxStepIso
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.complex
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.complex_obj_coe
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.complex_obj_top
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.complex_isoBot
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.complex_incl_coe
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.complex_incl_top
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.attach_nonmax
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.cells_nonmax
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.cells_max
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.originalCell
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.originalCell_coe
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.completedCell
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.cellsEquiv
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.cells_cardinal
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.completedCell_label
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.completedCell_inclusion
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.originalCell_stage
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.originalCell_label
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.sourceCofan_nonmax_heq
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.targetCofan_nonmax_heq
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.attachingMap_nonmax_heq
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.noMaxComplex
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.noMaxComplex_obj_coe
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.noMaxComplex_obj_top
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.noMaxComplex_isoBot
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.noMaxComplex_incl_coe
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.noMaxComplex_incl_top
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.originalNoMaxCell
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.completedNoMaxCell
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.noMaxCellsEquiv
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.noMaxCells_cardinal
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.noMaxComplex_sourceCofan
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.noMaxComplex_targetCofan
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.noMaxComplex_attachingMap
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.noMaxComplex_label
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.completedNoMaxCell_label
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.completedNoMaxCell_inclusion
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.originalNoMaxCell_stage
#print axioms HomotopicalAlgebra.RelativeCellComplex.GenericCompletion.originalNoMaxCell_label

end GenericCompletionCanonicalClients

namespace OriginalPlateauCanonicalClients

open CategoryTheory Limits MorphismProperty Opposite
open HomotopicalAlgebra HomotopicalAlgebra.CellularSubcomplexExtension

namespace OriginalPlateauClients

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f)
  (cap : O) (s : CellularSubcomplex (prefixComplex d c cap))

example : CellularSubcomplex c := CellularPlateau.subcomplex d c cap s

example : (CellularPlateau.subcomplex d c cap s).endpoint = s.endpoint :=
  CellularPlateau.endpoint d c cap s

example : (CellularPlateau.subcomplex d c cap s).hom = s.hom :=
  CellularPlateau.hom d c cap s

example : (CellularPlateau.subcomplex d c cap s).inclusion = s.inclusion ≫ c.incl.app cap :=
  CellularPlateau.inclusion d c cap s

example : IsColimit (CellularPlateau.endpointCocone d c cap s) :=
  CellularPlateau.endpointIsColimit d c cap s

example : (CellularPlateau.F cap s.complex.F).IsWellOrderContinuous :=
  CellularPlateau.wellOrderContinuous cap s.complex.F

example : (CellularPlateau.subcomplex d c cap s).support =
    CellularPlateau.ambientOccurrenceEmbedding d c cap '' s.support :=
  CellularPlateau.support d c cap s

example : Cardinal.mk (CellularPlateau.subcomplex d c cap s).complex.Cells =
    Cardinal.mk s.complex.Cells := CellularPlateau.cells_cardinal d c cap s

example (γ : Cardinal.{w}) (hs : Cardinal.mk s.complex.Cells ≤ γ) :
    Cardinal.mk (CellularPlateau.subcomplex d c cap s).complex.Cells ≤ γ := by
  rw [CellularPlateau.cells_cardinal]
  exact hs

example (a : s.complex.Cells) :
    (CellularPlateau.subcomplex d c cap s).originalCell
      (CellularPlateau.originalCell d c cap s a) =
        CellularPlateau.ambientOccurrence d c cap (s.originalCell a) :=
  CellularPlateau.originalCell_ambient d c cap s a

example (a : (CellularPlateau.complex d c cap s).Cells) :
    ∃ b : s.complex.Cells,
      (CellularPlateau.subcomplex d c cap s).originalCell a =
        CellularPlateau.ambientOccurrence d c cap (s.originalCell b) :=
  CellularPlateau.exists_originalCell d c cap s a

example (i : O) (hi : ¬ IsMax i) (hicap : cap ≤ i) :
    ((CellularPlateau.complex d c cap s).attachCells i hi).ι = PEmpty :=
  CellularPlateau.attach_after_empty d c cap s i hi hicap

end OriginalPlateauClients

#print axioms HomotopicalAlgebra.CellularPlateau.capIndex
#print axioms HomotopicalAlgebra.CellularPlateau.capFunctor
#print axioms HomotopicalAlgebra.CellularPlateau.capFunctor_final
#print axioms HomotopicalAlgebra.CellularPlateau.beforeCapIndex_final
#print axioms HomotopicalAlgebra.CellularPlateau.afterCapIndex_final
#print axioms HomotopicalAlgebra.CellularPlateau.wellOrderContinuous
#print axioms HomotopicalAlgebra.CellularPlateau.extendToSuccContinuous
#print axioms HomotopicalAlgebra.CellularPlateau.emptyCofan
#print axioms HomotopicalAlgebra.CellularPlateau.emptyCofanIsColimit
#print axioms HomotopicalAlgebra.CellularPlateau.emptyAttach
#print axioms HomotopicalAlgebra.CellularPlateau.botIso
#print axioms HomotopicalAlgebra.CellularPlateau.endpointCocone
#print axioms HomotopicalAlgebra.CellularPlateau.endpointIsColimit
#print axioms HomotopicalAlgebra.CellularPlateau.beforeStepIso
#print axioms HomotopicalAlgebra.CellularPlateau.afterStep_isIso
#print axioms HomotopicalAlgebra.CellularPlateau.complex
#print axioms HomotopicalAlgebra.CellularPlateau.attach_before
#print axioms HomotopicalAlgebra.CellularPlateau.attach_after_empty
#print axioms HomotopicalAlgebra.CellularPlateau.comparison
#print axioms HomotopicalAlgebra.CellularPlateau.comparison_app
#print axioms HomotopicalAlgebra.CellularPlateau.comparison_endpoint
#print axioms HomotopicalAlgebra.CellularPlateau.comparison_bot
#print axioms HomotopicalAlgebra.CellularPlateau.beforeIndexEquiv
#print axioms HomotopicalAlgebra.CellularPlateau.beforeIndex_label
#print axioms HomotopicalAlgebra.CellularPlateau.cell_before
#print axioms HomotopicalAlgebra.CellularPlateau.cells_before
#print axioms HomotopicalAlgebra.CellularPlateau.cellEmbedding
#print axioms HomotopicalAlgebra.CellularPlateau.cellEmbedding_label
#print axioms HomotopicalAlgebra.CellularPlateau.subcomplex
#print axioms HomotopicalAlgebra.CellularPlateau.ambientOccurrence
#print axioms HomotopicalAlgebra.CellularPlateau.ambientOccurrenceEmbedding
#print axioms HomotopicalAlgebra.CellularPlateau.originalCell
#print axioms HomotopicalAlgebra.CellularPlateau.originalCell_ambient
#print axioms HomotopicalAlgebra.CellularPlateau.exists_originalCell
#print axioms HomotopicalAlgebra.CellularPlateau.support
#print axioms HomotopicalAlgebra.CellularPlateau.endpoint
#print axioms HomotopicalAlgebra.CellularPlateau.hom
#print axioms HomotopicalAlgebra.CellularPlateau.inclusion
#print axioms HomotopicalAlgebra.CellularPlateau.cells_cardinal


end OriginalPlateauCanonicalClients

#lint only unusedArguments in MathlibExt.AlgebraicTopology.ModelCategory.CellularSource


namespace SingleEffectiveCoreCompatibilityClients

open HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f)
  (h : CellularSource d) (t u : CellularSubcomplex c)

example (j : O) (hj : ¬ IsMax j) (k : (c.attachCells j hj).ι) :
    CellularSubcomplexExtension.boundary d c j hj k =
      EffectiveCellularSubcomplexExtension.boundary d c j hj k := rfl

example (j : O) : CellularSubcomplexExtension.prefixComplex d c j =
    EffectiveCellularSubcomplexExtension.prefixComplex d c j := rfl

example (j : O) : CellularSubcomplexExtension.prefixSubcomplex d c t j =
    EffectiveCellularSubcomplexExtension.prefixSubcomplex d c t j := rfl

example (j : O) : (CellularSubcomplexExtension.prefixSubcomplex d c t j).endpoint =
    t.complex.F.obj j := CellularSubcomplexExtension.prefixSubcomplex_endpoint d c t j

example (j : O) : (CellularSubcomplexExtension.prefixSubcomplex d c t j).inclusion =
    t.comparison.app j := CellularSubcomplexExtension.prefixSubcomplex_inclusion d c t j

example : cofibrations C t.inclusion :=
  EffectiveCellularSubcomplexExtension.inclusionCofibration d c h.effectiveCofibrations t

variable (H : CellularSubcomplexContainment.SupportLE d c t u)

example : CellularSubcomplexContainment.containmentMap d c t u h H =
    EffectiveCellularSubcomplexContainment.containmentMap d c t u h.effectiveCofibrations H := rfl

example : CellularSubcomplexContainment.containmentMap d c t u h H ≫ u.inclusion =
    t.inclusion := CellularSubcomplexContainment.containmentMap_ambient d c t u h H

example : t.hom ≫ CellularSubcomplexContainment.containmentMap d c t u h H =
    u.hom := CellularSubcomplexContainment.containmentMap_root d c t u h H

example (j : O) : CellularSubcomplexContainment.stageMap d c t u h H j =
    EffectiveCellularSubcomplexContainment.stageMap d c t u h.effectiveCofibrations H j := rfl

example : CellularSubcomplexContainment.comparison d c t u h H =
    EffectiveCellularSubcomplexContainment.comparison d c t u h.effectiveCofibrations H := rfl

example : CellularSubcomplexContainment.asSubcomplex d c t u h H =
    EffectiveCellularSubcomplexContainment.asSubcomplex d c t u h.effectiveCofibrations H := rfl

example : cofibrations C (CellularSubcomplexContainment.containmentMap d c t u h H) :=
  CellularSubcomplexContainment.containmentMap_cofibration d c t u h H

variable {I : Type w} (pieces : I → CellularSubcomplex c)

example : CellularSubcomplex.union h pieces =
    EffectiveCellularSubcomplex.union d h.effectiveCofibrations pieces := rfl

example (i : I) : CellularSubcomplex.unionInclusion h pieces i =
    EffectiveCellularSubcomplex.unionInclusion d h.effectiveCofibrations pieces i := rfl

example (i : I) : (pieces i).hom ≫ CellularSubcomplex.unionInclusion h pieces i =
    (CellularSubcomplex.union h pieces).hom := CellularSubcomplex.unionInclusion_root h pieces i

example (i : I) : CellularSubcomplex.unionInclusion h pieces i ≫
    (CellularSubcomplex.union h pieces).inclusion = (pieces i).inclusion :=
  CellularSubcomplex.unionInclusion_ambient h pieces i

example : (CellularSubcomplex.union h pieces).support = ⋃ i : I, (pieces i).support :=
  CellularSubcomplex.union_support h pieces

example : Cardinal.mk (CellularSubcomplex.union h pieces).complex.Cells ≤
    Cardinal.sum (fun i : I => Cardinal.mk (pieces i).complex.Cells) :=
  CellularSubcomplex.union_cells_cardinal_le h pieces

example (i : I) : cofibrations C (CellularSubcomplex.unionInclusion h pieces i) :=
  CellularSubcomplex.unionInclusion_cofibration h pieces i

end SingleEffectiveCoreCompatibilityClients

set_option pp.universes true in
#check @HomotopicalAlgebra.CellularSubcomplexExtension.existsFamilyLift
set_option pp.universes true in
#check @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.existsFamilyLift
set_option pp.universes true in
#check @HomotopicalAlgebra.CellularSubcomplexContainment.asSubcomplex
set_option pp.universes true in
#check @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.asSubcomplex
set_option pp.universes true in
#check @HomotopicalAlgebra.CellularUnion.unionSubcomplex
set_option pp.universes true in
#check @HomotopicalAlgebra.EffectiveCellularUnion.unionSubcomplex
set_option pp.universes true in
#check @HomotopicalAlgebra.CellularSubcomplex.union
set_option pp.universes true in
#check @HomotopicalAlgebra.EffectiveCellularSubcomplex.union


open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let source := `MathlibExt.AlgebraicTopology.ModelCategory.CellularSource
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      if env.header.moduleNames[index]! == source then
        let axioms ← collectAxioms name
        unless axioms.all (allowed.contains ·) do
          throwError "Unexpected axioms for {name}: {axioms}"
        count := count + 1
  logInfo m!"NATIVE_STD3_ALL_CELLULAR_SOURCE_CONSTANTS={count}"
