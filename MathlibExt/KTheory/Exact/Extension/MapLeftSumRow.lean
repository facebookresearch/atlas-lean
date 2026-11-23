/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.FunctorMapData
public import MathlibExt.KTheory.Exact.Extension.LocalizedFiber
public import MathlibExt.KTheory.Exact.Extension.RowIsoDiagram
public import MathlibExt.CategoryTheory.Preadditive.MapBiprodNaturality
public import MathlibExt.Algebra.Homology.ShortComplex.HEqTransport

/-!
# The original left-sum row comparison for an exact functor

Canonical mapBiprod components compare the mapped left-sum row with the
left sum of the original mapped row. Complete row-object equations retain
all dependent endpoint presentations. The given quotient is unchanged,
and the actual ordinary row Iso supplies its original quotient diagram.
No action comparison or source square is an input.
-/

noncomputable section

open CategoryTheory CategoryTheory.ExactCategory CategoryTheory.Limits

attribute [local instance]
  CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBiproducts

universe uC vC uD vD

namespace AlgebraicKTheory

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]

variable (F : C ⥤ D) [F.Additive] [F.IsExact]

private def mapLeftSumTemplateRowIso (T : Core C) (E : ExtensionCategory C) :
    (ExtensionCategory.leftSumObj T E).row.map F ≅
      (ExtensionCategory.leftSumObj (⟨F.obj T.of⟩ : Core D)
        (⟨E.row.map F, F.map_admissibleExact E.row E.admissible⟩ : ExtensionCategory D)).row := by
  dsimp only [ExtensionCategory.leftSumObj, ShortComplex.map]
  refine ShortComplex.isoMk (F.mapBiprod T.of E.row.X₁)
    (F.mapBiprod T.of E.row.X₂) (Iso.refl (F.obj E.row.X₃)) ?_ ?_
  · simpa only [F.map_id] using
      (Functor.mapBiprod_additive_naturality F (𝟙 T.of) E.row.f)
  · have hProjection : (F.mapBiprod T.of E.row.X₂).hom ≫ biprod.snd =
        F.map (biprod.snd : T.of ⊞ E.row.X₂ ⟶ E.row.X₂) :=
      (congrArg (fun k : F.obj (T.of ⊞ E.row.X₂) ⟶ F.obj T.of ⊞ F.obj E.row.X₂ =>
        k ≫ (biprod.snd : F.obj T.of ⊞ F.obj E.row.X₂ ⟶ F.obj E.row.X₂))
          (Functor.mapBiprod_hom F T.of E.row.X₂)).trans
            (biprod.lift_snd _ _)
    have hSquare : (F.mapBiprod T.of E.row.X₂).hom ≫
        (biprod.snd ≫ F.map E.row.g) = F.map (biprod.snd ≫ E.row.g) :=
      (Category.assoc (F.mapBiprod T.of E.row.X₂).hom biprod.snd (F.map E.row.g)).symm.trans
        ((congrArg (fun k : F.obj (T.of ⊞ E.row.X₂) ⟶ F.obj E.row.X₂ =>
          k ≫ F.map E.row.g) hProjection).trans
            (F.map_comp (biprod.snd : T.of ⊞ E.row.X₂ ⟶ E.row.X₂) E.row.g).symm)
    exact hSquare.trans (Category.comp_id (F.map (biprod.snd ≫ E.row.g))).symm

private def mapLeftSumRowIsoComputed (T : Core C) (E : ExtensionCategory C) :
    (ExtensionCategory.mapObject F (ExtensionCategory.leftSumObj T E)).row ≅
      (ExtensionCategory.leftSumObj (F.core.obj T) (ExtensionCategory.mapObject F E)).row := by
  have hSource := ExtensionCategory.mapObject_row F (ExtensionCategory.leftSumObj T E)
  have hCore : F.core.obj T = (⟨F.obj T.of⟩ : Core D) := rfl
  have hTarget :
      (ExtensionCategory.leftSumObj (F.core.obj T) (ExtensionCategory.mapObject F E)).row =
        (ExtensionCategory.leftSumObj (⟨F.obj T.of⟩ : Core D)
          (⟨E.row.map F, F.map_admissibleExact E.row E.admissible⟩ : ExtensionCategory D)).row :=
    congrArg₂ (fun (A : Core D) (M : ExtensionCategory D) =>
      (ExtensionCategory.leftSumObj A M).row) hCore (ExtensionCategory.mapObject_eq_mk F E)
  exact eqToIso hSource ≪≫ mapLeftSumTemplateRowIso F T E ≪≫ (eqToIso hTarget).symm

/-- The actual mapped left-sum row has its canonical original biproduct comparison. -/
public def ExtensionCategory.mapLeftSumRowIso (T : Core C) (E : ExtensionCategory C) :
    (ExtensionCategory.mapObject F (ExtensionCategory.leftSumObj T E)).row ≅
      (ExtensionCategory.leftSumObj (F.core.obj T) (ExtensionCategory.mapObject F E)).row :=
  mapLeftSumRowIsoComputed F T E

/-- The canonical row comparison yields an actual original Weibel quotient diagram. -/
public def ExtensionCategory.mapLeftSumDiagram (T : Core C) (E : ExtensionCategory C) :
    ExtensionDiagram (ExtensionCategory.mapObject F (ExtensionCategory.leftSumObj T E))
      (ExtensionCategory.leftSumObj (F.core.obj T) (ExtensionCategory.mapObject F E)) :=
  ExtensionDiagram.ofRowIso (ExtensionCategory.mapLeftSumRowIso F T E)


/-- The canonical mapped left-sum row comparison is an actual extension-category Iso. -/
public def ExtensionCategory.mapLeftSumIso (T : Core C) (E : ExtensionCategory C) :
    ExtensionCategory.mapObject F (ExtensionCategory.leftSumObj T E) ≅
      ExtensionCategory.leftSumObj (F.core.obj T) (ExtensionCategory.mapObject F E) :=
  ExtensionCategory.isoOfRowIso (ExtensionCategory.mapLeftSumRowIso F T E)

private theorem leftSumIsoHomComputed (T : Core C) (E : ExtensionCategory C) :
    (ExtensionCategory.mapLeftSumIso F T E).hom =
      ExtensionCategory.mkHom (ExtensionCategory.mapLeftSumDiagram F T E) :=
  ExtensionCategory.isoOfRowIso_hom (ExtensionCategory.mapLeftSumRowIso F T E)

/-- Its forward map retains the actual original source-quotient comparison diagram. -/
public theorem ExtensionCategory.mapLeftSumIso_hom (T : Core C) (E : ExtensionCategory C) :
    (ExtensionCategory.mapLeftSumIso F T E).hom =
      ExtensionCategory.mkHom (ExtensionCategory.mapLeftSumDiagram F T E) :=
  leftSumIsoHomComputed F T E

private theorem leftSumIsoTargetComputed (T : Core C) (E : ExtensionCategory C) :
    (ExtensionCategory.target (C := D)).mapIso (ExtensionCategory.mapLeftSumIso F T E) =
      QuillenQ.underlyingIso ((ShortComplex.π₃ (C := D)).mapIso
        (ExtensionCategory.mapLeftSumRowIso F T E)) :=
  ExtensionCategory.isoOfRowIso_target (ExtensionCategory.mapLeftSumRowIso F T E)

/-- The complete action-comparison Iso has its original canonical third-component Q image. -/
public theorem ExtensionCategory.mapLeftSumIso_target
    (T : Core C) (E : ExtensionCategory C) :
    (ExtensionCategory.target (C := D)).mapIso (ExtensionCategory.mapLeftSumIso F T E) =
      QuillenQ.underlyingIso ((ShortComplex.π₃ (C := D)).mapIso
        (ExtensionCategory.mapLeftSumRowIso F T E)) :=
  leftSumIsoTargetComputed F T E


private theorem leftSumRowIsoComponentsComputed (T : Core C) (E : ExtensionCategory C) :
    HEq (ExtensionCategory.mapLeftSumRowIso F T E).hom.τ₁ (F.mapBiprod T.of E.row.X₁).hom ∧
      HEq (ExtensionCategory.mapLeftSumRowIso F T E).inv.τ₁ (F.mapBiprod T.of E.row.X₁).inv ∧
      HEq (ExtensionCategory.mapLeftSumRowIso F T E).hom.τ₂ (F.mapBiprod T.of E.row.X₂).hom ∧
      HEq (ExtensionCategory.mapLeftSumRowIso F T E).inv.τ₂ (F.mapBiprod T.of E.row.X₂).inv ∧
      HEq (ExtensionCategory.mapLeftSumRowIso F T E).hom.τ₃ (𝟙 (F.obj E.row.X₃)) ∧
      HEq (ExtensionCategory.mapLeftSumRowIso F T E).inv.τ₃ (𝟙 (F.obj E.row.X₃)) := by
  let a := ExtensionCategory.mapLeftSumRowIso F T E
  let b := mapLeftSumTemplateRowIso F T E
  have hs := ExtensionCategory.mapObject_row F (ExtensionCategory.leftSumObj T E)
  have hCore : F.core.obj T = (⟨F.obj T.of⟩ : Core D) := rfl
  have ht :
      (ExtensionCategory.leftSumObj (F.core.obj T) (ExtensionCategory.mapObject F E)).row =
        (ExtensionCategory.leftSumObj (⟨F.obj T.of⟩ : Core D)
          (⟨E.row.map F, F.map_admissibleExact E.row E.admissible⟩ : ExtensionCategory D)).row :=
    congrArg₂ (fun (A : Core D) (M : ExtensionCategory D) =>
      (ExtensionCategory.leftSumObj A M).row) hCore (ExtensionCategory.mapObject_eq_mk F E)
  have hh : HEq a.hom b.hom := (conj_eqToHom_iff_heq _ _ hs ht).1 rfl
  have hi : HEq a.inv b.inv := (conj_eqToHom_iff_heq _ _ ht hs).1
    (Category.assoc (eqToHom ht) b.inv (eqToHom hs.symm))
  have ch := ShortComplex.Hom.components_heq_of_rows_eq hs ht hh
  have ci := ShortComplex.Hom.components_heq_of_rows_eq ht hs hi
  have bh₁ : HEq b.hom.τ₁ (F.mapBiprod T.of E.row.X₁).hom := heq_of_eq rfl
  have bi₁ : HEq b.inv.τ₁ (F.mapBiprod T.of E.row.X₁).inv := heq_of_eq rfl
  have bh₂ : HEq b.hom.τ₂ (F.mapBiprod T.of E.row.X₂).hom := heq_of_eq rfl
  have bi₂ : HEq b.inv.τ₂ (F.mapBiprod T.of E.row.X₂).inv := heq_of_eq rfl
  have bh₃ : HEq b.hom.τ₃ (𝟙 (F.obj E.row.X₃)) := heq_of_eq rfl
  have bi₃ : HEq b.inv.τ₃ (𝟙 (F.obj E.row.X₃)) := heq_of_eq rfl
  exact ⟨ch.1.trans bh₁, ci.1.trans bi₁, ch.2.1.trans bh₂, ci.2.1.trans bi₂,
    ch.2.2.trans bh₃, ci.2.2.trans bi₃⟩

/-- The actual row comparison retains all six original forward/inverse component values. -/
public theorem ExtensionCategory.mapLeftSumRowIso_components
    (T : Core C) (E : ExtensionCategory C) :
    HEq (ExtensionCategory.mapLeftSumRowIso F T E).hom.τ₁ (F.mapBiprod T.of E.row.X₁).hom ∧
      HEq (ExtensionCategory.mapLeftSumRowIso F T E).inv.τ₁ (F.mapBiprod T.of E.row.X₁).inv ∧
      HEq (ExtensionCategory.mapLeftSumRowIso F T E).hom.τ₂ (F.mapBiprod T.of E.row.X₂).hom ∧
      HEq (ExtensionCategory.mapLeftSumRowIso F T E).inv.τ₂ (F.mapBiprod T.of E.row.X₂).inv ∧
      HEq (ExtensionCategory.mapLeftSumRowIso F T E).hom.τ₃ (𝟙 (F.obj E.row.X₃)) ∧
      HEq (ExtensionCategory.mapLeftSumRowIso F T E).inv.τ₃ (𝟙 (F.obj E.row.X₃)) :=
  leftSumRowIsoComponentsComputed F T E


private theorem leftSumObjectRowsComputed (T : Core C) (E : ExtensionCategory C) :
    (ExtensionCategory.mapObject F (ExtensionCategory.leftSumObj T E)).row.X₁ =
        F.obj (T.of ⊞ E.row.X₁) ∧
      (ExtensionCategory.mapObject F (ExtensionCategory.leftSumObj T E)).row.X₂ =
        F.obj (T.of ⊞ E.row.X₂) ∧
      (ExtensionCategory.mapObject F (ExtensionCategory.leftSumObj T E)).row.X₃ =
        F.obj E.row.X₃ ∧
      (ExtensionCategory.leftSumObj (F.core.obj T) (ExtensionCategory.mapObject F E)).row.X₁ =
        (F.obj T.of ⊞ F.obj E.row.X₁) ∧
      (ExtensionCategory.leftSumObj (F.core.obj T) (ExtensionCategory.mapObject F E)).row.X₂ =
        (F.obj T.of ⊞ F.obj E.row.X₂) ∧
      (ExtensionCategory.leftSumObj (F.core.obj T) (ExtensionCategory.mapObject F E)).row.X₃ =
        F.obj E.row.X₃ := by
  have c := ExtensionCategory.mapObject_components F (ExtensionCategory.leftSumObj T E)
  have e := ExtensionCategory.mapObject_components F E
  have hCore : (F.core.obj T).of = F.obj T.of := rfl
  have h₁ : (ExtensionCategory.leftSumObj T E).row.X₁ = (T.of ⊞ E.row.X₁) := rfl
  have h₂ : (ExtensionCategory.leftSumObj T E).row.X₂ = (T.of ⊞ E.row.X₂) := rfl
  have h₃ : (ExtensionCategory.leftSumObj T E).row.X₃ = E.row.X₃ := rfl
  refine ⟨c.1.trans (congrArg F.obj h₁), c.2.1.trans (congrArg F.obj h₂),
    c.2.2.trans (congrArg F.obj h₃), ?_, ?_, ?_⟩
  · change ((F.core.obj T).of ⊞ (ExtensionCategory.mapObject F E).row.X₁) = _
    exact congrArg₂ (fun X Y : D => (X ⊞ Y)) hCore e.1
  · change ((F.core.obj T).of ⊞ (ExtensionCategory.mapObject F E).row.X₂) = _
    exact congrArg₂ (fun X Y : D => (X ⊞ Y)) hCore e.2.1
  · exact e.2.2

/-- Every original endpoint of the actual left-sum comparison has its mapped object view. -/
public theorem ExtensionCategory.mapLeftSum_object_views (T : Core C) (E : ExtensionCategory C) :
    (ExtensionCategory.mapObject F (ExtensionCategory.leftSumObj T E)).row.X₁ =
        F.obj (T.of ⊞ E.row.X₁) ∧
      (ExtensionCategory.mapObject F (ExtensionCategory.leftSumObj T E)).row.X₂ =
        F.obj (T.of ⊞ E.row.X₂) ∧
      (ExtensionCategory.mapObject F (ExtensionCategory.leftSumObj T E)).row.X₃ =
        F.obj E.row.X₃ ∧
      (ExtensionCategory.leftSumObj (F.core.obj T) (ExtensionCategory.mapObject F E)).row.X₁ =
        (F.obj T.of ⊞ F.obj E.row.X₁) ∧
      (ExtensionCategory.leftSumObj (F.core.obj T) (ExtensionCategory.mapObject F E)).row.X₂ =
        (F.obj T.of ⊞ F.obj E.row.X₂) ∧
      (ExtensionCategory.leftSumObj (F.core.obj T) (ExtensionCategory.mapObject F E)).row.X₃ =
        F.obj E.row.X₃ :=
  leftSumObjectRowsComputed F T E

private theorem leftSumDiagramFieldsComputed (T : Core C) (E : ExtensionCategory C) :
    HEq (ExtensionCategory.mapLeftSumDiagram F T E).alpha (F.mapBiprod T.of E.row.X₁).inv ∧
      HEq (ExtensionCategory.mapLeftSumDiagram F T E).beta (F.mapBiprod T.of E.row.X₂).hom ∧
      HEq (ExtensionCategory.mapLeftSumDiagram F T E).mu (𝟙 (F.obj E.row.X₃)) := by
  let a := ExtensionCategory.mapLeftSumRowIso F T E
  have c := ExtensionCategory.mapLeftSumRowIso_components F T E
  have d := ExtensionDiagram.ofRowIso_components a
  exact ⟨(heq_of_eq d.1).trans c.2.1,
    (heq_of_eq d.2.1).trans c.2.2.1, d.2.2.2.2.2.2.trans c.2.2.2.2.1⟩

/-- The original action-comparison diagram has the canonical biproduct and quotient legs. -/
public theorem ExtensionCategory.mapLeftSumDiagram_components
    (T : Core C) (E : ExtensionCategory C) :
    HEq (ExtensionCategory.mapLeftSumDiagram F T E).alpha (F.mapBiprod T.of E.row.X₁).inv ∧
      HEq (ExtensionCategory.mapLeftSumDiagram F T E).beta (F.mapBiprod T.of E.row.X₂).hom ∧
      HEq (ExtensionCategory.mapLeftSumDiagram F T E).mu (𝟙 (F.obj E.row.X₃)) :=
  leftSumDiagramFieldsComputed F T E

end AlgebraicKTheory

end
