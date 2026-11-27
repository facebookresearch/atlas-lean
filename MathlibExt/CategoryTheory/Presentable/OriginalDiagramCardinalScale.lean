/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.Functor.OriginalArrowBounds
public import MathlibExt.CategoryTheory.Presentable.HomPowerAccessibility
public import MathlibExt.CategoryTheory.Presentable.FunctorPresentability
public import MathlibExt.CategoryTheory.Presentable.UnderFunctorPresentability
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.DiagramActionConstraintBounds
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CompactRootBaseChange
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.CategoryTheory.SmallObject.Basic
public import Mathlib.SetTheory.Cardinal.HasCardinalLT

/-!
# Original diagram and tree bounds at an internally selected regular cardinal

The original base local-presentability witness and the actual small I/J label
families supply endpoint ranks. The actual original index supplies its own
object and arrow bound. Native cofree/power choices remain at the original
base witness throughout cardinal enlargement. The total original cell carrier
is bounded at the same selected cardinal. Arbitrary original roots remain.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w uD vD uC vC uI uJ uP

namespace CategoryTheory.Presentable.OriginalDiagramCardinalScale

open Limits Opposite SmallObject

variable {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D]
  {iota : Type uI} {jota : Type uJ}

/-- The actual two original generator families retain every original label. -/
def combinedFamily (I : iota → Arrow C) (J : jota → Arrow C) : iota ⊕ jota → Arrow C :=
  Sum.elim I J

/-- Every original I label retains its entire Arrow value. -/
theorem combinedFamily_inl (I : iota → Arrow C) (J : jota → Arrow C) (i : iota) :
    combinedFamily I J (.inl i) = I i := rfl

/-- Every original J label retains its entire Arrow value. -/
theorem combinedFamily_inr (I : iota → Arrow C) (J : jota → Arrow C) (j : jota) :
    combinedFamily I J (.inr j) = J j := rfl

/-- The endpoint family contains both actual endpoints of every original I/J arrow. -/
def generatorEndpoint (I : iota → Arrow C) (J : jota → Arrow C)
    (k : (iota ⊕ jota) × Bool) : C :=
  match k.2 with
  | false => (combinedFamily I J k.1).left
  | true => (combinedFamily I J k.1).right

/-- The entire source function is the original source function, without label reindexing. -/
theorem generatorEndpoint_source_function (I : iota → Arrow C) (J : jota → Arrow C) :
    (fun k : iota ⊕ jota => generatorEndpoint I J (k, false)) =
      (fun k : iota ⊕ jota => (combinedFamily I J k).left) := rfl

/-- The entire target function is the original target function, without label reindexing. -/
theorem generatorEndpoint_target_function (I : iota → Arrow C) (J : jota → Arrow C) :
    (fun k : iota ⊕ jota => generatorEndpoint I J (k, true)) =
      (fun k : iota ⊕ jota => (combinedFamily I J k).right) := rfl

section OriginalScale

variable (baseRank : Cardinal.{w}) [Fact baseRank.IsRegular]
  [IsCardinalLocallyPresentable C baseRank]
  [Small.{w} D] [LocallySmall.{w} D]
  (I : iota → Arrow C) (J : jota → Arrow C)
  (P : Type uP) (lowerRank : Cardinal.{w})

/-- Complete produced cardinal data on the actual original categories and generator labels. -/
structure Profile where
  /-- The internally selected enlarged cardinal. -/
  chi : Cardinal.{w}
  /-- Its actual native regularity dictionary. -/
  [regular : Fact chi.IsRegular]
  /-- The selected cardinal is genuinely uncountable. -/
  uncountable : Cardinal.aleph0 < chi
  /-- The original requested lower rank is retained as a proved lower bound. -/
  lower_le : lowerRank ≤ chi
  /-- The actual original base local-presentability rank is a proved lower bound. -/
  base_le : baseRank ≤ chi
  /-- Local presentability is derived on the original coefficient carrier. -/
  base_locallyPresentable : IsCardinalLocallyPresentable C chi
  /-- Local presentability is derived on the whole original functor category. -/
  diagram_locallyPresentable : IsCardinalLocallyPresentable (D ⥤ C) chi
  /-- Every original index object lies in the same bounded carrier. -/
  object_bound : HasCardinalLT D chi
  /-- The actual entire original Arrow carrier is bounded. -/
  arrow_bound : HasCardinalLT (Arrow D) chi
  /-- The actual internally chosen small-model Arrow carrier is also bounded. -/
  representative_arrow_bound : HasCardinalLT (Arrow (SmallModel.{w} D)) chi
  /-- Every original generator label, including unused original labels, remains bounded. -/
  generator_label_bound : HasCardinalLT (iota ⊕ jota) chi
  /-- The actual total original cell carrier is bounded. -/
  cell_bound : HasCardinalLT P chi
  /-- Every original generator source is presentable at the selected cardinal. -/
  source_presentable (k : iota ⊕ jota) : IsCardinalPresentable (combinedFamily I J k).left chi
  /-- Every original generator target is presentable at the selected cardinal. -/
  target_presentable (k : iota ⊕ jota) : IsCardinalPresentable (combinedFamily I J k).right chi
  /-- Every original Hom carrier retains its actual size bound. -/
  hom_bound (d e : D) : HasCardinalLT (d ⟶ e) chi
  /-- The actual cofree functors are returned on all original labels. -/
  cofree : D → C ⥤ D ⥤ C
  /-- The entire cofree function equals the original native function at baseRank. -/
  cofree_original : cofree = Completeness.cofree C baseRank (equivSmallModel.{w} D)
  /-- The actual Hom-power functors are returned on all pairs of original labels. -/
  power : D → D → C ⥤ C
  /-- The entire power function equals the original native function at baseRank. -/
  power_original : power = Completeness.homPower C baseRank (equivSmallModel.{w} D)
  /-- Every same original cofree value preserves the required filtered colimits. -/
  cofree_accessible (d : D) : (cofree d).IsCardinalAccessible chi
  /-- Every same original Hom-power value preserves the required filtered colimits. -/
  power_accessible (d e : D) : (power d e).IsCardinalAccessible chi

/-- Select every original diagram, endpoint and total-cell bound at one regular cardinal. -/
theorem exists_profile [Small.{w} iota] [Small.{w} jota] [Small.{w} P] :
    Nonempty (Profile baseRank (D := D) I J P lowerRank) := by
  let : IsAccessibleCategory.{w} C := ⟨baseRank, inferInstance, inferInstance⟩
  let Q : ObjectProperty C := ObjectProperty.ofObj (generatorEndpoint I J)
  let : ObjectProperty.Small.{w} Q := inferInstance
  let : ObjectProperty.EssentiallySmall.{w} Q := inferInstance
  obtain ⟨endpointRank, hEndpointRegular, hEndpoints⟩ :=
    ObjectProperty.le_isCardinalPresentable Q
  let : Fact endpointRank.IsRegular := hEndpointRegular
  obtain ⟨powerRank, hPowerRegular, hBase, hRepresentative, hCoefficient, hDiagram,
      _, hCofree, hPower⟩ :=
    HomPowerAccessibility.bounded_common_rank C baseRank (equivSmallModel.{w} D)
  let : Fact powerRank.IsRegular := hPowerRegular
  obtain ⟨carrierRank, _, hCarrier⟩ :=
    HasCardinalLT.exists_regular_cardinal.{w} ((iota ⊕ jota) ⊕ P)
  obtain ⟨chi, hRegular, hUncountable, hRanks, hArrow, hObjects, hHoms⟩ :=
    Functor.OriginalArrowBounds.existsRegularBoundAbove (D := D)
      (max powerRank (max endpointRank (max carrierRank lowerRank)))
  let : Fact chi.IsRegular := ⟨hRegular⟩
  have hPowerLe : powerRank ≤ chi :=
    (le_max_left powerRank _).trans hRanks
  have hEndpointLe : endpointRank ≤ chi :=
    ((le_max_left endpointRank _).trans (le_max_right powerRank _)).trans hRanks
  have hCarrierLe : carrierRank ≤ chi :=
    (((le_max_left carrierRank lowerRank).trans (le_max_right endpointRank _)).trans
      (le_max_right powerRank _)).trans hRanks
  have hLowerLe : lowerRank ≤ chi :=
    (((le_max_right carrierRank lowerRank).trans (le_max_right endpointRank _)).trans
      (le_max_right powerRank _)).trans hRanks
  have hLabels : HasCardinalLT (iota ⊕ jota) chi :=
    (hCarrier.of_injective Sum.inl Sum.inl_injective).of_le hCarrierLe
  have hCells : HasCardinalLT P chi :=
    (hCarrier.of_injective Sum.inr Sum.inr_injective).of_le hCarrierLe
  let : IsCardinalLocallyPresentable C powerRank := hCoefficient
  let : IsCardinalLocallyPresentable (D ⥤ C) powerRank := hDiagram
  have hSource (k : iota ⊕ jota) :
      IsCardinalPresentable (combinedFamily I J k).left chi := by
    let : IsCardinalPresentable (generatorEndpoint I J (k, false)) endpointRank :=
      hEndpoints _ (ObjectProperty.ofObj_apply (generatorEndpoint I J) (k, false))
    exact isCardinalPresentable_of_le (generatorEndpoint I J (k, false)) hEndpointLe
  have hTarget (k : iota ⊕ jota) :
      IsCardinalPresentable (combinedFamily I J k).right chi := by
    let : IsCardinalPresentable (generatorEndpoint I J (k, true)) endpointRank :=
      hEndpoints _ (ObjectProperty.ofObj_apply (generatorEndpoint I J) (k, true))
    exact isCardinalPresentable_of_le (generatorEndpoint I J (k, true)) hEndpointLe
  have hCofreeChi (d : D) :
      (Completeness.cofree C baseRank (equivSmallModel.{w} D) d).IsCardinalAccessible chi := by
    let : (Completeness.cofree C baseRank (equivSmallModel.{w} D) d).IsCardinalAccessible
        powerRank := hCofree d
    exact Functor.isCardinalAccessible_of_le _ hPowerLe
  have hPowerChi (d e : D) :
      (Completeness.homPower C baseRank (equivSmallModel.{w} D) d e).IsCardinalAccessible chi := by
    let : (Completeness.homPower C baseRank (equivSmallModel.{w} D) d e).IsCardinalAccessible
        powerRank := hPower d e
    exact Functor.isCardinalAccessible_of_le _ hPowerLe
  exact ⟨{
    chi := chi
    regular := inferInstance
    uncountable := hUncountable
    lower_le := hLowerLe
    base_le := hBase.trans hPowerLe
    base_locallyPresentable := IsCardinalLocallyPresentable.of_le C hPowerLe
    diagram_locallyPresentable := IsCardinalLocallyPresentable.of_le (D ⥤ C) hPowerLe
    object_bound := hObjects
    arrow_bound := hArrow
    representative_arrow_bound := hRepresentative.of_le hPowerLe
    generator_label_bound := hLabels
    cell_bound := hCells
    source_presentable := hSource
    target_presentable := hTarget
    hom_bound := hHoms
    cofree := Completeness.cofree C baseRank (equivSmallModel.{w} D)
    cofree_original := rfl
    power := Completeness.homPower C baseRank (equivSmallModel.{w} D)
    power_original := rfl
    cofree_accessible := hCofreeChi
    power_accessible := hPowerChi }⟩

/-- The entire original scale is chosen from the proved existence theorem internally. -/
def chosenProfile [Small.{w} iota] [Small.{w} jota] [Small.{w} P] :
    Profile baseRank (D := D) I J P lowerRank :=
  Classical.choice (exists_profile baseRank (D := D) I J P lowerRank)

namespace Profile

variable {baseRank I J P lowerRank} (p : Profile baseRank (D := D) I J P lowerRank)

/-- The selected rank really gives accessibility of the original coefficient category. -/
theorem base_accessible : letI := p.regular; IsCardinalAccessibleCategory C p.chi := by
  let : Fact p.chi.IsRegular := p.regular
  let : IsCardinalLocallyPresentable C p.chi := p.base_locallyPresentable
  infer_instance

/-- The selected rank really gives accessibility of the whole original diagram category. -/
theorem diagram_accessible : letI := p.regular; IsCardinalAccessibleCategory (D ⥤ C) p.chi := by
  let : Fact p.chi.IsRegular := p.regular
  let : IsCardinalLocallyPresentable (D ⥤ C) p.chi := p.diagram_locallyPresentable
  infer_instance

/-- The whole original component criterion is derived at this same selected rank. -/
theorem presentable_iff_components (F : D ⥤ C) :
    letI := p.regular
    IsCardinalPresentable F p.chi ↔ ∀ d : D, IsCardinalPresentable (F.obj d) p.chi := by
  let : Fact p.chi.IsRegular := p.regular
  exact FunctorPresentability.presentable_iff_components C baseRank (equivSmallModel.{w} D) p.chi
    p.base_le p.representative_arrow_bound F

/-- Every actual incoming object, incoming pair and native two-arrow carrier is bounded. -/
theorem original_constraint_bounds :
    HasCardinalLT (ComposableArrows D 2) p.chi ∧
      ∀ e : D, HasCardinalLT (Over e) p.chi ∧
        HasCardinalLT (DiagramActionConstraintBounds.IncomingPair e) p.chi ∧
        HasCardinalLT (DiagramActionConstraintBounds.Constraint e) p.chi := by
  let : Fact p.chi.IsRegular := p.regular
  have h := DiagramActionConstraintBounds.allBounds p.chi p.arrow_bound
  exact ⟨h.2.1, h.2.2⟩

/-- Relative compactness retains the arbitrary original root functor and all its actions. -/
theorem relative_diagram_presentable (F : D ⥤ C) (U : Under F)
    (hU : letI := p.regular
      ∀ d : D, IsCardinalPresentable (Under.mk (U.hom.app d)) p.chi) :
    letI := p.regular; IsCardinalPresentable U p.chi := by
  let : Fact p.chi.IsRegular := p.regular
  exact UnderFunctorPresentability.relative_diagram_presentable F p.chi p.arrow_bound U hU

/-- The actual full power comparison comes from equality of the entire original functors. -/
def powerComparison (d e : D) :
    p.power d e ≅ Completeness.homPower C baseRank (equivSmallModel.{w} D) d e :=
  eqToIso (congrFun (congrFun p.power_original d) e)

/-- The actual full cofree comparison comes from equality of the entire original functors. -/
def cofreeComparison (d : D) :
    p.cofree d ≅ Completeness.cofree C baseRank (equivSmallModel.{w} D) d :=
  eqToIso (congrFun p.cofree_original d)

/-- Every native whole power map retains its original typed coefficient-map equation. -/
theorem power_map (d e : D) {X Y : C} (f : X ⟶ Y) :
    (p.power d e).map f ≫ (p.powerComparison d e).hom.app Y =
      (p.powerComparison d e).hom.app X ≫
        (Completeness.homPower C baseRank (equivSmallModel.{w} D) d e).map f :=
  (p.powerComparison d e).hom.naturality f

/-- The inverse whole power comparison retains the same original coefficient-map function. -/
theorem power_map_inv (d e : D) {X Y : C} (f : X ⟶ Y) :
    (Completeness.homPower C baseRank (equivSmallModel.{w} D) d e).map f ≫
        (p.powerComparison d e).inv.app Y =
      (p.powerComparison d e).inv.app X ≫ (p.power d e).map f :=
  (p.powerComparison d e).inv.naturality f

/-- Transport of the whole coefficient map equals the same native original map. -/
theorem power_map_transport (d e : D) {X Y : C} (f : X ⟶ Y) :
    (p.powerComparison d e).inv.app X ≫ (p.power d e).map f ≫
        (p.powerComparison d e).hom.app Y =
      (Completeness.homPower C baseRank (equivSmallModel.{w} D) d e).map f := by
  rw [p.power_map, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

/-- Every original cofree action keeps the whole original typed index-action map. -/
theorem cofree_action (d : D) {e e' : D} (a : e ⟶ e') (X : C) :
    ((p.cofree d).obj X).map a ≫ ((p.cofreeComparison d).hom.app X).app e' =
      ((p.cofreeComparison d).hom.app X).app e ≫
        ((Completeness.cofree C baseRank (equivSmallModel.{w} D) d).obj X).map a :=
  ((p.cofreeComparison d).hom.app X).naturality a

/-- The inverse cofree comparison retains every whole original index-action map. -/
theorem cofree_action_inv (d : D) {e e' : D} (a : e ⟶ e') (X : C) :
    ((Completeness.cofree C baseRank (equivSmallModel.{w} D) d).obj X).map a ≫
        ((p.cofreeComparison d).inv.app X).app e' =
      ((p.cofreeComparison d).inv.app X).app e ≫ ((p.cofree d).obj X).map a :=
  ((p.cofreeComparison d).inv.app X).naturality a

/-- Every cofree coefficient map retains its complete original component function. -/
theorem cofree_coefficient (d e : D) {X Y : C} (f : X ⟶ Y) :
    ((p.cofree d).map f).app e ≫ ((p.cofreeComparison d).hom.app Y).app e =
      ((p.cofreeComparison d).hom.app X).app e ≫
        ((Completeness.cofree C baseRank (equivSmallModel.{w} D) d).map f).app e :=
  NatTrans.congr_app ((p.cofreeComparison d).hom.naturality f) e

/-- The inverse cofree comparison retains the complete original coefficient-map function. -/
theorem cofree_coefficient_inv (d e : D) {X Y : C} (f : X ⟶ Y) :
    ((Completeness.cofree C baseRank (equivSmallModel.{w} D) d).map f).app e ≫
        ((p.cofreeComparison d).inv.app Y).app e =
      ((p.cofreeComparison d).inv.app X).app e ≫ ((p.cofree d).map f).app e :=
  NatTrans.congr_app ((p.cofreeComparison d).inv.naturality f) e

section LowerCarriers

variable [PartialOrder P]

/-- Every literal original lower carrier is bounded by the actual total original carrier. -/
theorem lower_object_bound (B : LowerSet P) : HasCardinalLT B p.chi :=
  p.cell_bound.of_injective Subtype.val Subtype.val_injective

/-- Every actual Arrow of every original lower carrier is bounded, without mono assumptions. -/
theorem lower_arrow_bound (B : LowerSet P) : HasCardinalLT (Arrow B) p.chi := by
  let : Fact p.chi.IsRegular := p.regular
  exact (hasCardinalLT_arrow_iff_of_isThin B p.chi (Fact.out : p.chi.IsRegular).aleph0_le).2
    (p.lower_object_bound B)

/-- Every original strict predecessor carrier is bounded at this same selected rank. -/
theorem predecessor_bound (a : P) : HasCardinalLT (LowerSet.Iio a) p.chi :=
  p.lower_object_bound (LowerSet.Iio a)

/-- Every original increment retains its actual carrier bound. -/
theorem increment_bound (B E : LowerSet P) : HasCardinalLT (CellTree.Increment B E) p.chi :=
  p.cell_bound.of_injective (fun a => a.1) Subtype.val_injective

end LowerCarriers

end Profile

end OriginalScale

section SelectedOriginalCompactRoot

variable (baseRank : Cardinal.{w}) [Fact baseRank.IsRegular]
  [IsCardinalLocallyPresentable C baseRank]
  [Small.{w} D] [LocallySmall.{w} D]
  (I : iota → Arrow C) (J : jota → Arrow C)
  [Small.{w} iota] [Small.{w} jota]
  {P : Type w} [PartialOrder P] {X : C}
  [HasPushouts C] (T : CellTree (combinedFamily I J) X (P := P))
  (lowerRank : Cardinal.{w})

/-- The actual entire compact-root result, with its internally selected original scale. -/
structure SelectedCompactRoot where
  /-- The complete scale is an output, with no incoming desired-cardinal premise. -/
  profile : Profile baseRank (D := D) I J P lowerRank
  /-- Every whole original tree, lower UP and function is returned by the genuine supplier. -/
  presentation : letI := profile.regular
    CompactRootBaseChange.CompactRootPresentation profile.chi T

/-- Select the regular cardinal and construct the whole original compact-root tree internally. -/
def selectedCompactRoot : SelectedCompactRoot baseRank (D := D) I J T lowerRank := by
  let p := chosenProfile baseRank (D := D) I J P lowerRank
  let : Fact p.chi.IsRegular := p.regular
  let : IsCardinalLocallyPresentable C p.chi := p.base_locallyPresentable
  exact {
    profile := p
    presentation := CompactRootBaseChange.compactRootPresentation p.chi T p.cell_bound
      (fun a => p.source_presentable (T.label a))
      (fun a => p.target_presentable (T.label a)) }

end SelectedOriginalCompactRoot

section WholeOriginalValues

variable {baseRank : Cardinal.{w}} [Fact baseRank.IsRegular]
  [IsCardinalLocallyPresentable C baseRank]
  [Small.{w} D] [LocallySmall.{w} D]
  {I : iota → Arrow C} {J : jota → Arrow C}
  {P : Type w} [PartialOrder P] {X : C} [HasPushouts C]
  {T : CellTree (combinedFamily I J) X (P := P)} {lowerRank : Cardinal.{w}}
  (R : SelectedCompactRoot baseRank (D := D) I J T lowerRank)

namespace SelectedCompactRoot

/-- Every original vertex retains the whole forward original-root map function. -/
theorem vertex_root_function : letI := R.profile.regular
    (fun a : P => pushout.inr (R.presentation.tree.vertex a).hom R.presentation.rootMap ≫
      (R.presentation.comparison.hom.app a).right) = (fun a : P => (T.vertex a).hom) := by
  let : Fact R.profile.chi.IsRegular := R.profile.regular
  funext a
  exact Under.w (R.presentation.comparison.hom.app a)

/-- Every original vertex retains the whole inverse original-root map function. -/
theorem vertex_root_inv_function : letI := R.profile.regular
    (fun a : P => (T.vertex a).hom ≫ (R.presentation.comparison.inv.app a).right) =
      (fun a : P => pushout.inr (R.presentation.tree.vertex a).hom R.presentation.rootMap) := by
  let : Fact R.profile.chi.IsRegular := R.profile.regular
  funext a
  exact Under.w (R.presentation.comparison.inv.app a)

/-- Every original predecessor retains the whole forward original-root map function. -/
theorem predecessor_root_function : letI := R.profile.regular
    (fun a : P => pushout.inr (R.presentation.tree.predecessorObj a).hom R.presentation.rootMap ≫
      (R.presentation.predecessorComparison a).hom.right) =
      (fun a : P => (T.predecessorObj a).hom) := by
  let : Fact R.profile.chi.IsRegular := R.profile.regular
  funext a
  exact Under.w (R.presentation.predecessorComparison a).hom

/-- Every original predecessor retains the whole inverse original-root map function. -/
theorem predecessor_root_inv_function : letI := R.profile.regular
    (fun a : P => (T.predecessorObj a).hom ≫
      (R.presentation.predecessorComparison a).inv.right) =
      (fun a : P => pushout.inr (R.presentation.tree.predecessorObj a).hom
        R.presentation.rootMap) := by
  let : Fact R.profile.chi.IsRegular := R.profile.regular
  funext a
  exact Under.w (R.presentation.predecessorComparison a).inv

/-- Every pair of literal original lower sets keeps its entire forward structural map. -/
theorem lower_map (L : LowerSetColimitData T.diagram) (B E : LowerSet P) (h : B ≤ E) :
    letI := R.profile.regular
    (Under.pushout R.presentation.rootMap).map
        (R.presentation.lower.functor.map (homOfLE h)) ≫
      (R.presentation.lowerComparison L).hom.app E =
      (R.presentation.lowerComparison L).hom.app B ≫ L.functor.map (homOfLE h) := by
  let : Fact R.profile.chi.IsRegular := R.profile.regular
  exact (R.presentation.lowerComparison L).hom.naturality (homOfLE h)

/-- Every pair of literal original lower sets keeps its entire inverse structural map. -/
theorem lower_map_inv (L : LowerSetColimitData T.diagram) (B E : LowerSet P) (h : B ≤ E) :
    letI := R.profile.regular
    L.functor.map (homOfLE h) ≫ (R.presentation.lowerComparison L).inv.app E =
      (R.presentation.lowerComparison L).inv.app B ≫
        (Under.pushout R.presentation.rootMap).map
          (R.presentation.lower.functor.map (homOfLE h)) := by
  let : Fact R.profile.chi.IsRegular := R.profile.regular
  exact (R.presentation.lowerComparison L).inv.naturality (homOfLE h)

/-- The entire forward function of all original lower root maps retains its values. -/
theorem lower_root_function (L : LowerSetColimitData T.diagram) : letI := R.profile.regular
    (fun B : LowerSet P =>
      pushout.inr (R.presentation.lower.obj B).hom R.presentation.rootMap ≫
        ((R.presentation.lowerComparison L).hom.app B).right) =
      (fun B : LowerSet P => (L.obj B).hom) := by
  let : Fact R.profile.chi.IsRegular := R.profile.regular
  funext B
  exact Under.w ((R.presentation.lowerComparison L).hom.app B)

/-- The entire inverse function of all original lower root maps retains its values. -/
theorem lower_root_inv_function (L : LowerSetColimitData T.diagram) : letI := R.profile.regular
    (fun B : LowerSet P => (L.obj B).hom ≫
      ((R.presentation.lowerComparison L).inv.app B).right) =
      (fun B : LowerSet P => pushout.inr (R.presentation.lower.obj B).hom
        R.presentation.rootMap) := by
  let : Fact R.profile.chi.IsRegular := R.profile.regular
  funext B
  exact Under.w ((R.presentation.lowerComparison L).inv.app B)

/-- Every actual new lower carrier has the root-adjoined object bound at the selected rank. -/
theorem lower_root_adjoined_object_bound (B : LowerSet P) :
    HasCardinalLT (WithInitial B) R.profile.chi := by
  let : Fact R.profile.chi.IsRegular := R.profile.regular
  exact CompactRootBaseChange.rootAdjoinedObject_bound R.profile.chi B
    (R.profile.lower_object_bound B)

/-- Every actual new root-adjoined lower diagram has its complete native Arrow bound. -/
theorem lower_root_adjoined_arrow_bound (B : LowerSet P) :
    HasCardinalLT (Arrow (WithInitial B)) R.profile.chi := by
  let : Fact R.profile.chi.IsRegular := R.profile.regular
  exact CompactRootBaseChange.rootAdjoinedArrow_bound R.profile.chi B
    (R.profile.lower_object_bound B)

/-- The whole original attaching function is retained, with actual dependent label transport. -/
theorem attaching_function : letI := R.profile.regular
    (fun a : P => R.presentation.tree.attaching a ≫
      pushout.inl (R.presentation.tree.predecessorObj a).hom R.presentation.rootMap ≫
      (R.presentation.predecessorComparison a).hom.right) =
    (fun a : P => eqToHom (congrArg (fun l : iota ⊕ jota => (combinedFamily I J l).left)
      (congrFun R.presentation.label_eq a)) ≫ T.attaching a) := by
  let : Fact R.profile.chi.IsRegular := R.profile.regular
  exact R.presentation.attaching_function

/-- The whole original generator-target function is retained with its actual label transport. -/
theorem cell_function : letI := R.profile.regular
    (fun a : P => R.presentation.tree.cell a ≫
      pushout.inl (R.presentation.tree.vertex a).hom R.presentation.rootMap ≫
      (R.presentation.comparison.hom.app a).right) =
    (fun a : P => eqToHom (congrArg (fun l : iota ⊕ jota => (combinedFamily I J l).right)
      (congrFun R.presentation.label_eq a)) ≫ T.cell a) := by
  let : Fact R.profile.chi.IsRegular := R.profile.regular
  exact R.presentation.cell_function

/-- The entire lower-to-endpoint Iso equals the same selected original endpoint Iso. -/
theorem lower_endpoint_iso (L : LowerSetColimitData T.diagram) : letI := R.profile.regular
    (Under.pushout R.presentation.rootMap).mapIso
      (R.presentation.tree.endpointIso R.presentation.lower) ≪≫ R.presentation.endpointComparison =
      (R.presentation.lowerComparison L).app ⊤ ≪≫ T.endpointIso L := by
  let : Fact R.profile.chi.IsRegular := R.profile.regular
  exact R.presentation.lower_endpoint_iso L

/-- The entire lower-to-predecessor Iso equals the same selected native predecessor Iso. -/
theorem lower_predecessor_iso (L : LowerSetColimitData T.diagram) (a : P) :
    letI := R.profile.regular
    (Under.pushout R.presentation.rootMap).mapIso
      (R.presentation.tree.predecessorIso R.presentation.lower a) ≪≫
        R.presentation.predecessorComparison a =
      (R.presentation.lowerComparison L).app (LowerSet.Iio a) ≪≫ T.predecessorIso L a := by
  let : Fact R.profile.chi.IsRegular := R.profile.regular
  exact R.presentation.lower_predecessor_iso L a

end SelectedCompactRoot

end WholeOriginalValues

section ExistentialOriginalBase

variable [IsLocallyPresentable.{w} C]

/-- Select the actual original coefficient LP rank from its legitimate existential witness. -/
def originalBaseRank : Cardinal.{w} :=
  Classical.choose (IsLocallyPresentable.exists_cardinal.{w} C)

/-- The actual regularity dictionary belongs to that same original LP witness. -/
theorem originalBaseRank_regular : Fact (originalBaseRank (C := C)).IsRegular :=
  Classical.choose (Classical.choose_spec (IsLocallyPresentable.exists_cardinal.{w} C))

/-- The original category has local presentability at that same internally selected rank. -/
theorem originalBaseRank_locallyPresentable : letI := originalBaseRank_regular (C := C)
    IsCardinalLocallyPresentable C (originalBaseRank (C := C)) :=
  Classical.choose_spec (Classical.choose_spec (IsLocallyPresentable.exists_cardinal.{w} C))

/-- Actual coefficient LP supplies genuine pushouts for the original compact-root construction. -/
theorem original_hasPushouts : HasPushouts C := by
  let : Fact (originalBaseRank (C := C)).IsRegular := originalBaseRank_regular (C := C)
  let : IsCardinalLocallyPresentable C (originalBaseRank (C := C)) :=
    originalBaseRank_locallyPresentable (C := C)
  infer_instance

/-- Choose the entire original bounded profile without a supplied cardinal or accessibility rank. -/
def scaleFromLocallyPresentable [Small.{w} D] [LocallySmall.{w} D]
    (I : iota → Arrow C) (J : jota → Arrow C)
    [Small.{w} iota] [Small.{w} jota] (P : Type uP) [Small.{w} P]
    (lowerRank : Cardinal.{w}) :
    letI := originalBaseRank_regular (C := C)
    letI := originalBaseRank_locallyPresentable (C := C)
    Profile (originalBaseRank (C := C)) (D := D) I J P lowerRank := by
  let : Fact (originalBaseRank (C := C)).IsRegular := originalBaseRank_regular (C := C)
  let : IsCardinalLocallyPresentable C (originalBaseRank (C := C)) :=
    originalBaseRank_locallyPresentable (C := C)
  exact chosenProfile (originalBaseRank (C := C)) (D := D) I J P lowerRank

/-- Actual LP, original small labels and the original tree produce its whole compact-root result. -/
def compactRootFromLocallyPresentable [Small.{w} D] [LocallySmall.{w} D]
    (I : iota → Arrow C) (J : jota → Arrow C)
    [Small.{w} iota] [Small.{w} jota] {P : Type w} [PartialOrder P] {X : C}
    (T : CellTree (combinedFamily I J) X (P := P)) (lowerRank : Cardinal.{w}) :
    letI := original_hasPushouts (C := C)
    letI := originalBaseRank_regular (C := C)
    letI := originalBaseRank_locallyPresentable (C := C)
    SelectedCompactRoot (originalBaseRank (C := C)) (D := D) I J T lowerRank := by
  let : HasPushouts C := original_hasPushouts (C := C)
  let : Fact (originalBaseRank (C := C)).IsRegular := originalBaseRank_regular (C := C)
  let : IsCardinalLocallyPresentable C (originalBaseRank (C := C)) :=
    originalBaseRank_locallyPresentable (C := C)
  exact selectedCompactRoot (originalBaseRank (C := C)) (D := D) I J T lowerRank

end ExistentialOriginalBase

section OriginalMorphismFamilies

open MorphismProperty

variable [IsLocallyPresentable.{w} C]
  [Small.{w} D] [LocallySmall.{w} D] (I J : MorphismProperty C)
  [I.IsSmall.{w}] [J.IsSmall.{w}]
  (P : Type uP) [Small.{w} P] (lowerRank : Cardinal.{w})

/-- The property entry keeps every original I and J Arrow as its actual original label. -/
def scaleForMorphismProperties :
    letI := originalBaseRank_regular (C := C)
    letI := originalBaseRank_locallyPresentable (C := C)
    Profile (originalBaseRank (C := C)) (D := D)
      (fun i : I.toSet => i.1) (fun j : J.toSet => j.1) P lowerRank :=
  scaleFromLocallyPresentable (D := D) (fun i : I.toSet => i.1) (fun j : J.toSet => j.1) P lowerRank

/-- The same produced cardinal has an actual native ordinal bottom. -/
@[instance_reducible]
def regularOrdinalBottom (chi : Cardinal.{w}) [Fact chi.IsRegular] :
    OrderBot chi.ord.ToType := by
  have h : Nonempty chi.ord.ToType := by
    simpa using Cardinal.IsRegular.ne_zero (Fact.out : chi.IsRegular)
  let : Nonempty chi.ord.ToType := h
  exact WellFoundedLT.toOrderBot chi.ord.ToType

/-- Genuine source presentability constructs all six original small-object fields internally. -/
theorem smallObjectFromSources (K : MorphismProperty C) [K.IsSmall.{w}]
    (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
    [OrderBot chi.ord.ToType]
    (hSource : ∀ f : K.toSet, IsCardinalPresentable f.1.left chi) :
    K.IsCardinalForSmallObjectArgument chi where
  isSmall := inferInstance
  locallySmall := inferInstance
  hasPushouts := inferInstance
  hasCoproducts := inferInstance
  hasIterationOfShape := inferInstance
  preservesColimit := by
    intro A B X Y i hi f hf
    let : IsCardinalPresentable A chi := hSource ⟨Arrow.mk i, hi⟩
    let : PreservesColimitsOfShape chi.ord.ToType (coyoneda.obj (op A)) :=
      preservesColimitsOfShape_of_isCardinalPresentable A chi chi.ord.ToType
    infer_instance

/-- The same whole original property profile returns both six-field eligibility dictionaries. -/
structure OriginalSmallObjectScale where
  /-- The actual internally selected original base rank retains its regularity dictionary. -/
  [baseRegular : Fact (originalBaseRank (C := C)).IsRegular]
  /-- Its actual original local-presentability dictionary belongs to the same witness. -/
  [baseLocallyPresentable : IsCardinalLocallyPresentable C (originalBaseRank (C := C))]
  /-- The profile is produced internally from actual base/index/generator data. -/
  profile : Profile (originalBaseRank (C := C)) (D := D)
      (fun i : I.toSet => i.1) (fun j : J.toSet => j.1) P lowerRank
  /-- The actual ordinal bottom belongs to the selected cardinal. -/
  bottom : OrderBot profile.chi.ord.ToType
  /-- Every original I eligibility field uses the same chosen cardinal and bottom. -/
  I_smallObject : letI := profile.regular
    letI := bottom
    I.IsCardinalForSmallObjectArgument profile.chi
  /-- Every original J eligibility field uses the same chosen cardinal and bottom. -/
  J_smallObject : letI := profile.regular
    letI := bottom
    J.IsCardinalForSmallObjectArgument profile.chi

/-- Choose both endpoint families and construct the whole original common SOA profile. -/
def originalSmallObjectScale : OriginalSmallObjectScale (D := D) I J P lowerRank := by
  let : Fact (originalBaseRank (C := C)).IsRegular := originalBaseRank_regular (C := C)
  let : IsCardinalLocallyPresentable C (originalBaseRank (C := C)) :=
    originalBaseRank_locallyPresentable (C := C)
  let p := scaleForMorphismProperties (D := D) I J P lowerRank
  let : Fact p.chi.IsRegular := p.regular
  let : IsCardinalLocallyPresentable C p.chi := p.base_locallyPresentable
  let b := regularOrdinalBottom p.chi
  let : OrderBot p.chi.ord.ToType := b
  exact {
    baseRegular := inferInstance
    baseLocallyPresentable := inferInstance
    profile := p
    bottom := b
    I_smallObject := smallObjectFromSources I p.chi
      (fun i => p.source_presentable (.inl i))
    J_smallObject := smallObjectFromSources J p.chi
      (fun j => p.source_presentable (.inr j)) }

end OriginalMorphismFamilies

section OriginalPropertyCompactRoot

variable [IsLocallyPresentable.{w} C]
  [Small.{w} D] [LocallySmall.{w} D] (I J : MorphismProperty C)
  [I.IsSmall.{w}] [J.IsSmall.{w}]
  {P : Type w} [PartialOrder P] {X : C}
  (T : CellTree (combinedFamily (fun i : I.toSet => i.1) (fun j : J.toSet => j.1)) X (P := P))
  (lowerRank : Cardinal.{w})

/-- The original-property tree retains every original label and all compact-root data. -/
def compactRootForMorphismProperties :
    letI := original_hasPushouts (C := C)
    letI := originalBaseRank_regular (C := C)
    letI := originalBaseRank_locallyPresentable (C := C)
    SelectedCompactRoot (originalBaseRank (C := C)) (D := D)
      (fun i : I.toSet => i.1) (fun j : J.toSet => j.1) T lowerRank :=
  compactRootFromLocallyPresentable (D := D)
    (fun i : I.toSet => i.1) (fun j : J.toSet => j.1) T lowerRank

end OriginalPropertyCompactRoot

end CategoryTheory.Presentable.OriginalDiagramCardinalScale
