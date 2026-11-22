/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativeConstruction
public import MathlibExt.CategoryTheory.Enriched.LeftKanExtension
public import MathlibExt.CategoryTheory.Enriched.RightKanExtension
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Native projective Kan adjunctions

The models are the actual fixed native constructions on small genuine enriched
indices. Restriction preserves the original pointwise right classes, so the
coend left Kan adjunction is Quillen. The free comparison retains its complete
unit and counit. Right Kan is Quillen exactly under the displayed original free
boundary/horn image conditions. The particular PointedCGWH limit and colimit
instances are used directly.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective
open scoped CGWH.limits CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.Kan

variable {A B : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  [EnrichedCategory PointedCGWH.{u, v} B]

/-- Actual native pointwise fibrations restrict along every full enriched index map. -/
theorem restriction_preservesFibrations (j : EnrichedFunctor PointedCGWH.{u, v} A B) :
    let : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
      Native.Construction.modelCategory
    let : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} B) :=
      Native.Construction.modelCategory
    PreservesFibrations (EnrichedFunctorCat.restriction j) := by
  let : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
    Native.Construction.modelCategory
  let : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} B) :=
    Native.Construction.modelCategory
  change PreservesFibrations (EnrichedFunctorCat.restriction j)
  intro X Y q hq
  rw [Native.Construction.fibrations_eq (A := B)] at hq
  change fibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)
    ((EnrichedFunctorCat.restriction j).map q)
  rw [Native.Construction.fibrations_eq (A := A)]
  rw [EvaluationTransfer.evaluationProperty_iff] at hq ⊢
  intro a
  change fibrations PointedCGWH.{u, v}
    (EnrichedFunctorCat.component (EnrichedFunctorCat.restrictionMap j q) a)
  rw [EnrichedFunctorCat.restrictionMap_component]
  exact hq (j.obj a)

/-- Actual native pointwise trivial fibrations retain every original component. -/
theorem restriction_preservesTrivialFibrations (j : EnrichedFunctor PointedCGWH.{u, v} A B) :
    let : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
      Native.Construction.modelCategory
    let : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} B) :=
      Native.Construction.modelCategory
    PreservesTrivialFibrations (EnrichedFunctorCat.restriction j) := by
  let : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
    Native.Construction.modelCategory
  let : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} B) :=
    Native.Construction.modelCategory
  change PreservesTrivialFibrations (EnrichedFunctorCat.restriction j)
  intro X Y q hq
  rw [Native.Construction.trivialFibrations_eq (A := B)] at hq
  change trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)
    ((EnrichedFunctorCat.restriction j).map q)
  rw [Native.Construction.trivialFibrations_eq (A := A)]
  rw [EvaluationTransfer.evaluationProperty_iff] at hq ⊢
  intro a
  change trivialFibrations PointedCGWH.{u, v}
    (EnrichedFunctorCat.component (EnrichedFunctorCat.restrictionMap j q) a)
  rw [EnrichedFunctorCat.restrictionMap_component]
  exact hq (j.obj a)

/-- The genuine coend Lan is left Quillen to actual restriction for fixed native models. -/
theorem leftKanRestriction_isQuillen (j : EnrichedFunctor PointedCGWH.{u, v} A B) :
    let : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
      Native.Construction.modelCategory
    let : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} B) :=
      Native.Construction.modelCategory
    (EnrichedFunctorCat.leftKanRestrictionAdjunction j).IsQuillenAdjunction := by
  let : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
    Native.Construction.modelCategory
  let : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} B) :=
    Native.Construction.modelCategory
  exact Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
    (restriction_preservesFibrations j) (restriction_preservesTrivialFibrations j)


/-- Literal identity components compare the actual selected evaluation after restriction. -/
def restrictionEvaluationIso (j : EnrichedFunctor PointedCGWH.{u, v} A B) (a : A) :
    EnrichedFunctorCat.restriction j ⋙ EnrichedFunctorCat.evaluation a ≅
      EnrichedFunctorCat.evaluation (j.obj a) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y q
    change EnrichedFunctorCat.component (EnrichedFunctorCat.restrictionMap j q) a ≫ 𝟙 _ =
      𝟙 _ ≫ EnrichedFunctorCat.component q (j.obj a)
    let P := X.toEnrichedFunctor.obj (j.obj a)
    let Q := Y.toEnrichedFunctor.obj (j.obj a)
    let c : P ⟶ Q := EnrichedFunctorCat.component (EnrichedFunctorCat.restrictionMap j q) a
    let d : P ⟶ Q := EnrichedFunctorCat.component q (j.obj a)
    have hc : c = d := EnrichedFunctorCat.restrictionMap_component j q a
    change c ≫ 𝟙 Q = 𝟙 P ≫ d
    exact (Category.comp_id c).trans (hc.trans (Category.id_comp d).symm))

/-- Actual prolongation sends the whole original free functor to the original target free. -/
def leftKanFreeIso (j : EnrichedFunctor PointedCGWH.{u, v} A B) (a : A) :
    EnrichedFunctorCat.Free.functor a ⋙ EnrichedFunctorCat.leftKan j ≅
      EnrichedFunctorCat.Free.functor (j.obj a) :=
  Adjunction.leftAdjointUniq
    (((EnrichedFunctorCat.Free.adjunction a).comp
      (EnrichedFunctorCat.leftKanRestrictionAdjunction j)).ofNatIsoRight
        (restrictionEvaluationIso j a))
    (EnrichedFunctorCat.Free.adjunction (j.obj a))

/-- The complete original free/Lan unit identifies the comparison on its source identity. -/
theorem leftKanFreeIso_unit (j : EnrichedFunctor PointedCGWH.{u, v} A B) (a : A)
    (M : PointedCGWH.{u, v}) :
    (EnrichedFunctorCat.Free.adjunction a).unit.app M ≫
      EnrichedFunctorCat.component
        ((EnrichedFunctorCat.leftKanRestrictionAdjunction j).unit.app
          ((EnrichedFunctorCat.Free.functor a).obj M)) a ≫
      EnrichedFunctorCat.component ((leftKanFreeIso j a).hom.app M) (j.obj a) =
    (EnrichedFunctorCat.Free.adjunction (j.obj a)).unit.app M := by
  let adj := ((EnrichedFunctorCat.Free.adjunction a).comp
    (EnrichedFunctorCat.leftKanRestrictionAdjunction j)).ofNatIsoRight
      (restrictionEvaluationIso j a)
  have h := Adjunction.unit_leftAdjointUniq_hom_app adj
    (EnrichedFunctorCat.Free.adjunction (j.obj a)) M
  change adj.unit.app M ≫
    EnrichedFunctorCat.component ((leftKanFreeIso j a).hom.app M) (j.obj a) = _ at h
  have hu : adj.unit.app M =
      (EnrichedFunctorCat.Free.adjunction a).unit.app M ≫
        EnrichedFunctorCat.component
          ((EnrichedFunctorCat.leftKanRestrictionAdjunction j).unit.app
            ((EnrichedFunctorCat.Free.functor a).obj M)) a := by
    change ((EnrichedFunctorCat.Free.adjunction a).comp
        (EnrichedFunctorCat.leftKanRestrictionAdjunction j)).unit.app M ≫
      𝟙 _ = _
    rw [Adjunction.comp_unit_app]
    simp only [Category.comp_id]
    rfl
  rw [hu] at h
  exact h


/-- The whole original free counit agrees with the coend counit under prolongation. -/
theorem leftKanFreeIso_counit (j : EnrichedFunctor PointedCGWH.{u, v} A B) (a : A)
    (Y : EnrichedFunctorCat PointedCGWH.{u, v} B) :
    (leftKanFreeIso j a).hom.app (Y.toEnrichedFunctor.obj (j.obj a)) ≫
      (EnrichedFunctorCat.Free.adjunction (j.obj a)).counit.app Y =
    (EnrichedFunctorCat.leftKan j).map
        ((EnrichedFunctorCat.Free.adjunction a).counit.app
          ((EnrichedFunctorCat.restriction j).obj Y)) ≫
      (EnrichedFunctorCat.leftKanRestrictionAdjunction j).counit.app Y := by
  let adj := ((EnrichedFunctorCat.Free.adjunction a).comp
    (EnrichedFunctorCat.leftKanRestrictionAdjunction j)).ofNatIsoRight
      (restrictionEvaluationIso j a)
  have h := Adjunction.leftAdjointUniq_hom_app_counit adj
    (EnrichedFunctorCat.Free.adjunction (j.obj a)) Y
  change (leftKanFreeIso j a).hom.app (Y.toEnrichedFunctor.obj (j.obj a)) ≫
    (EnrichedFunctorCat.Free.adjunction (j.obj a)).counit.app Y = adj.counit.app Y at h
  have hc : adj.counit.app Y =
      (EnrichedFunctorCat.leftKan j).map
          ((EnrichedFunctorCat.Free.adjunction a).counit.app
            ((EnrichedFunctorCat.restriction j).obj Y)) ≫
        (EnrichedFunctorCat.leftKanRestrictionAdjunction j).counit.app Y := by
    change (EnrichedFunctorCat.Free.functor a ⋙ EnrichedFunctorCat.leftKan j).map (𝟙 _) ≫
      ((EnrichedFunctorCat.Free.adjunction a).comp
        (EnrichedFunctorCat.leftKanRestrictionAdjunction j)).counit.app Y = _
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Adjunction.comp_counit_app]
  exact h.trans hc


/-- The actual full horn family generates the fixed native fibration class. -/
private theorem nativeJ_rlp :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} B) :=
      Native.Construction.modelCategory
    (generators (A := B) PointedCGWH.realizedHornInclusions.{u, v}).rlp =
      fibrations (EnrichedFunctorCat PointedCGWH.{u, v} B) := by
  let : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} B) :=
    Native.Construction.modelCategory
  have h := MorphismProperty.rlp_eq_of_wfs
    (trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} B))
    (fibrations (EnrichedFunctorCat PointedCGWH.{u, v} B))
  rw [Native.Construction.trivialCofibrations_eq (A := B),
    MorphismProperty.rlp_llp_rlp] at h
  exact h

/-- The actual full boundary family generates the fixed native trivial fibrations. -/
private theorem nativeI_rlp :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} B) :=
      Native.Construction.modelCategory
    (generators (A := B) PointedCGWH.realizedBoundaryInclusions.{u, v}).rlp =
      trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} B) := by
  let : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} B) :=
    Native.Construction.modelCategory
  have h := MorphismProperty.rlp_eq_of_wfs
    (cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} B))
    (trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} B))
  rw [Native.Construction.cofibrations_eq (A := B), MorphismProperty.rlp_llp_rlp] at h
  exact h

/-- Right Kan is Quillen exactly when actual restriction sends the original free
boundary and horn arrows into the fixed native left classes. -/
theorem rightKan_isQuillen_iff_generators (j : EnrichedFunctor PointedCGWH.{u, v} A B) :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
      Native.Construction.modelCategory
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} B) :=
      Native.Construction.modelCategory
    (EnrichedFunctorCat.rightKanAdjunction j).IsQuillenAdjunction ↔
      generators (A := B) PointedCGWH.realizedBoundaryInclusions.{u, v} ≤
        (cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)).inverseImage
          (EnrichedFunctorCat.restriction j) ∧
      generators (A := B) PointedCGWH.realizedHornInclusions.{u, v} ≤
        (trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)).inverseImage
          (EnrichedFunctorCat.restriction j) := by
  let : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
    Native.Construction.modelCategory
  let : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} B) :=
    Native.Construction.modelCategory
  change (EnrichedFunctorCat.rightKanAdjunction j).IsQuillenAdjunction ↔ _
  constructor
  · intro h
    constructor
    · intro X Y i hi
      have hco : cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} B) i := by
        rw [Native.Construction.cofibrations_eq (A := B)]
        exact (generators (A := B) PointedCGWH.realizedBoundaryInclusions.{u, v}).le_llp_rlp i hi
      exact h.preservesCofibrations i hco
    · intro X Y i hi
      have hco : trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} B) i := by
        rw [Native.Construction.trivialCofibrations_eq (A := B)]
        exact (generators (A := B) PointedCGWH.realizedHornInclusions.{u, v}).le_llp_rlp i hi
      exact h.preservesTrivialCofibrations i hco
  · intro h
    apply Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
    · intro X Y p hp
      change fibrations (EnrichedFunctorCat PointedCGWH.{u, v} B)
        ((EnrichedFunctorCat.rightKan j).map p)
      rw [← nativeJ_rlp (B := B)]
      intro U V i hi
      have hi' : trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)
          ((EnrichedFunctorCat.restriction j).map i) := h.2 i hi
      have hl := MorphismProperty.hasLiftingProperty_of_wfs
        ((EnrichedFunctorCat.restriction j).map i) p hi' hp
      exact ((EnrichedFunctorCat.rightKanAdjunction j).hasLiftingProperty_iff i p).mp hl
    · intro X Y p hp
      change trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} B)
        ((EnrichedFunctorCat.rightKan j).map p)
      rw [← nativeI_rlp (B := B)]
      intro U V i hi
      have hi' : cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)
          ((EnrichedFunctorCat.restriction j).map i) := h.1 i hi
      have hl := MorphismProperty.hasLiftingProperty_of_wfs
        ((EnrichedFunctorCat.restriction j).map i) p hi' hp
      exact ((EnrichedFunctorCat.rightKanAdjunction j).hasLiftingProperty_iff i p).mp hl


private theorem freeUnit_original (a : A) (M : PointedCGWH.{u, v}) :
    (EnrichedFunctorCat.Free.adjunction a).unit.app M =
      (ρ_ M).inv ≫ (M ◁ eId PointedCGWH.{u, v} a) := by
  have h := (EnrichedFunctorCat.Free.adjunction a).homEquiv_id M
  rw [EnrichedFunctorCat.Free.adjunction_homEquiv] at h
  change (ρ_ M).inv ≫ (M ◁ eId PointedCGWH.{u, v} a) ≫
    EnrichedFunctorCat.component (𝟙 (EnrichedFunctorCat.Free.object a M)) a = _ at h
  rw [EnrichedFunctorCat.component_id, Category.comp_id] at h
  exact h.symm

/-- The original free identity and full coend identity insertion give the literal unit map. -/
theorem leftKanFreeIso_unit_original
    (j : EnrichedFunctor PointedCGWH.{u, v} A B) (a : A) (M : PointedCGWH.{u, v}) :
    (ρ_ M).inv ≫ (M ◁ eId PointedCGWH.{u, v} a) ≫
      ((λ_ (M ⊗ (a ⟶[PointedCGWH.{u, v}] a))).inv ≫
        (eId PointedCGWH.{u, v} (j.obj a) ▷ (M ⊗ (a ⟶[PointedCGWH.{u, v}] a))) ≫
        Enriched.weightedCoend.ι
          (EnrichedFunctorCat.leftKanWeight j (j.obj a))
          (EnrichedFunctorCat.Free.object a M).toEnrichedFunctor a) ≫
      EnrichedFunctorCat.component ((leftKanFreeIso j a).hom.app M) (j.obj a) =
    (ρ_ M).inv ≫ (M ◁ eId PointedCGWH.{u, v} (j.obj a)) := by
  have h := leftKanFreeIso_unit j a M
  rw [freeUnit_original, freeUnit_original] at h
  rw [EnrichedFunctorCat.leftKanRestrictionAdjunction_unit_component] at h
  exact h


private theorem freeCounit_component_original (b c : B)
    (Y : EnrichedFunctorCat PointedCGWH.{u, v} B) :
    EnrichedFunctorCat.component
        ((EnrichedFunctorCat.Free.adjunction b).counit.app Y) c =
      MonoidalClosed.uncurry (Y.toEnrichedFunctor.map b c) := by
  have h := (EnrichedFunctorCat.Free.adjunction b).homEquiv_symm_id Y
  rw [EnrichedFunctorCat.Free.adjunction_homEquiv] at h
  change EnrichedFunctorCat.Free.extend b (Y.toEnrichedFunctor.obj b) Y (𝟙 _) = _ at h
  have hc := congrArg (fun q => EnrichedFunctorCat.component q c) h
  rw [EnrichedFunctorCat.Free.extend_component] at hc
  change (𝟙 _ ⊗ₘ 𝟙 _) ≫ MonoidalClosed.uncurry (Y.toEnrichedFunctor.map b c) = _ at hc
  let K := Y.toEnrichedFunctor.obj b
  let H := b ⟶[PointedCGWH.{u, v}] c
  let L := Y.toEnrichedFunctor.obj c
  let action : K ⊗ H ⟶ L := MonoidalClosed.uncurry (Y.toEnrichedFunctor.map b c)
  let epsilon : EnrichedFunctorCat.Free.object b K ⟶ Y :=
    (EnrichedFunctorCat.Free.adjunction b).counit.app Y
  change (𝟙 K ⊗ₘ 𝟙 H) ≫ action = EnrichedFunctorCat.component epsilon c at hc
  have hid : (𝟙 K ⊗ₘ 𝟙 H) = 𝟙 (K ⊗ H) := MonoidalCategory.id_tensorHom_id K H
  have hact : (𝟙 K ⊗ₘ 𝟙 H) ≫ action = action :=
    (congrArg (fun f : K ⊗ H ⟶ K ⊗ H => f ≫ action) hid).trans (Category.id_comp action)
  exact hc.symm.trans hact

/-- At every target index the original free counit is the entire target Hom action. -/
theorem leftKanFreeIso_counit_component_original
    (j : EnrichedFunctor PointedCGWH.{u, v} A B) (a : A)
    (Y : EnrichedFunctorCat PointedCGWH.{u, v} B) (b : B) :
    EnrichedFunctorCat.component
        ((leftKanFreeIso j a).hom.app (Y.toEnrichedFunctor.obj (j.obj a))) b ≫
      MonoidalClosed.uncurry (Y.toEnrichedFunctor.map (j.obj a) b) =
    EnrichedFunctorCat.component
        ((EnrichedFunctorCat.leftKan j).map
          ((EnrichedFunctorCat.Free.adjunction a).counit.app
            ((EnrichedFunctorCat.restriction j).obj Y))) b ≫
      EnrichedFunctorCat.component
        ((EnrichedFunctorCat.leftKanRestrictionAdjunction j).counit.app Y) b := by
  let M := Y.toEnrichedFunctor.obj (j.obj a)
  let Q : EnrichedFunctorCat PointedCGWH.{u, v} B :=
    (EnrichedFunctorCat.leftKan j).obj (EnrichedFunctorCat.Free.object a M)
  let R : EnrichedFunctorCat PointedCGWH.{u, v} B := EnrichedFunctorCat.Free.object (j.obj a) M
  let T : EnrichedFunctorCat PointedCGWH.{u, v} B :=
    (EnrichedFunctorCat.leftKan j).obj ((EnrichedFunctorCat.restriction j).obj Y)
  let f : Q ⟶ R := (leftKanFreeIso j a).hom.app M
  let g : R ⟶ Y := (EnrichedFunctorCat.Free.adjunction (j.obj a)).counit.app Y
  let p : Q ⟶ T := (EnrichedFunctorCat.leftKan j).map
    ((EnrichedFunctorCat.Free.adjunction a).counit.app ((EnrichedFunctorCat.restriction j).obj Y))
  let q : T ⟶ Y := (EnrichedFunctorCat.leftKanRestrictionAdjunction j).counit.app Y
  have h : f ≫ g = p ≫ q := leftKanFreeIso_counit j a Y
  have hc := congrArg (fun r : Q ⟶ Y => EnrichedFunctorCat.component r b) h
  have hleft := EnrichedFunctorCat.component_comp f g b
  have hright := EnrichedFunctorCat.component_comp p q b
  have hg : EnrichedFunctorCat.component g b =
      MonoidalClosed.uncurry (Y.toEnrichedFunctor.map (j.obj a) b) :=
    freeCounit_component_original (j.obj a) b Y
  change EnrichedFunctorCat.component f b ≫ MonoidalClosed.uncurry
    (Y.toEnrichedFunctor.map (j.obj a) b) =
    EnrichedFunctorCat.component p b ≫ EnrichedFunctorCat.component q b
  exact (congrArg (fun r => EnrichedFunctorCat.component f b ≫ r) hg).symm.trans
    (hleft.symm.trans (hc.trans hright))

end HomotopicalAlgebra.EnrichedProjective.Native.Kan
