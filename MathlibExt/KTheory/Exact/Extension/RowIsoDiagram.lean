/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.Target
public import MathlibExt.KTheory.Exact.Extension.FunctorMapData
public import Mathlib.Algebra.Homology.ShortComplex.Basic

/-!
# Original quotient diagrams from an ordinary isomorphism of given rows

The reverse kernel leg is the inverse first component, and the forward
middle leg is the second component. The middle quotient remains the given
source quotient, with identity left leg and the third component on the
right. Its Q target is the existing underlying-isomorphism lift. No
replacement quotient or expected target equation is supplied as data.
-/

noncomputable section

open CategoryTheory CategoryTheory.ExactCategory CategoryTheory.Limits

universe u v

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

omit [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] in
private def rowComponentIso₁ {S T : ShortComplex C} (e : S ≅ T) : S.X₁ ≅ T.X₁ where
  hom := e.hom.τ₁
  inv := e.inv.τ₁
  hom_inv_id := (ShortComplex.comp_τ₁ e.hom e.inv).symm.trans
    ((congrArg (fun f : S ⟶ S => f.τ₁) e.hom_inv_id).trans (ShortComplex.id_τ₁ S))
  inv_hom_id := (ShortComplex.comp_τ₁ e.inv e.hom).symm.trans
    ((congrArg (fun f : T ⟶ T => f.τ₁) e.inv_hom_id).trans (ShortComplex.id_τ₁ T))

omit [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] in
private def rowComponentIso₂ {S T : ShortComplex C} (e : S ≅ T) : S.X₂ ≅ T.X₂ where
  hom := e.hom.τ₂
  inv := e.inv.τ₂
  hom_inv_id := (ShortComplex.comp_τ₂ e.hom e.inv).symm.trans
    ((congrArg (fun f : S ⟶ S => f.τ₂) e.hom_inv_id).trans (ShortComplex.id_τ₂ S))
  inv_hom_id := (ShortComplex.comp_τ₂ e.inv e.hom).symm.trans
    ((congrArg (fun f : T ⟶ T => f.τ₂) e.inv_hom_id).trans (ShortComplex.id_τ₂ T))

omit [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] in
private def rowComponentIso₃ {S T : ShortComplex C} (e : S ≅ T) : S.X₃ ≅ T.X₃ where
  hom := e.hom.τ₃
  inv := e.inv.τ₃
  hom_inv_id := (ShortComplex.comp_τ₃ e.hom e.inv).symm.trans
    ((congrArg (fun f : S ⟶ S => f.τ₃) e.hom_inv_id).trans (ShortComplex.id_τ₃ S))
  inv_hom_id := (ShortComplex.comp_τ₃ e.inv e.hom).symm.trans
    ((congrArg (fun f : T ⟶ T => f.τ₃) e.inv_hom_id).trans (ShortComplex.id_τ₃ T))

/-- The actual quotient diagram induced by the given ordinary row isomorphism. -/
public def ExtensionDiagram.ofRowIso {E' E : ExtensionCategory C}
    (e : E'.row ≅ E.row) : ExtensionDiagram E' E := by
  let e₁ := rowComponentIso₁ e
  let e₂ := rowComponentIso₂ e
  let e₃ := rowComponentIso₃ e
  let j := e₁.inv ≫ E'.row.f
  have hz : j ≫ E'.row.g = 0 :=
    (Category.assoc e₁.inv E'.row.f E'.row.g).trans
      ((congrArg (fun k : E'.row.X₁ ⟶ E'.row.X₃ => e₁.inv ≫ k) E'.row.zero).trans
        (comp_zero : e₁.inv ≫ 0 = 0))
  let S := ShortComplex.mk j E'.row.g hz
  let h : S ≅ E'.row := ShortComplex.isoMk e₁.symm (Iso.refl _) (Iso.refl _)
    (by exact (Category.comp_id j).symm)
    (by exact (Category.id_comp E'.row.g).trans (Category.comp_id E'.row.g).symm)
  have hS : IsAdmissibleExact S := isAdmissibleExact_of_iso h.symm E'.admissible
  have hLeft : e₁.hom ≫ E.row.f = E'.row.f ≫ e₂.hom := e.hom.comm₁₂
  have hRight : e₂.hom ≫ E.row.g = E'.row.g ≫ e₃.hom := e.hom.comm₂₃
  exact
    { alpha := e₁.inv
      alpha_admissible := IsAdmissibleMono.of_isIso e₁.inv
      beta := e₂.hom
      beta_admissible := IsAdmissibleMono.of_isIso e₂.hom
      D := E'.row.X₃
      j := j
      q := E'.row.g
      zero := hz
      admissible := hS
      lambda := 𝟙 E'.row.X₃
      lambda_admissible := IsAdmissibleEpi.id _
      mu := e₃.hom
      mu_admissible := IsAdmissibleMono.of_isIso e₃.hom
      j_eq := rfl
      j_beta := (Category.assoc e₁.inv E'.row.f e₂.hom).trans
        ((congrArg (fun k : E'.row.X₁ ⟶ E.row.X₂ => e₁.inv ≫ k) hLeft).symm.trans
          (e₁.inv_hom_id_assoc E.row.f))
      q_lambda := Category.comp_id E'.row.g
      q_mu := hRight.symm }

private theorem rowIsoDiagramSpanComputed {E' E : ExtensionCategory C}
    (e : E'.row ≅ E.row) :
    (ExtensionDiagram.ofRowIso e).toQuillenSpan =
      QuillenQ.underlyingIsoFwdSpan ((ShortComplex.π₃ (C := C)).mapIso e) := rfl

/-- The original target span is precisely the canonical lift of the third component. -/
public theorem ExtensionDiagram.ofRowIso_toQuillenSpan {E' E : ExtensionCategory C}
    (e : E'.row ≅ E.row) :
    (ExtensionDiagram.ofRowIso e).toQuillenSpan =
      QuillenQ.underlyingIsoFwdSpan ((ShortComplex.π₃ (C := C)).mapIso e) :=
  rowIsoDiagramSpanComputed e

/-- The given row isomorphism has its actual canonical Q-target arrow. -/
public theorem ExtensionDiagram.ofRowIso_target {E' E : ExtensionCategory C}
    (e : E'.row ≅ E.row) :
    (ExtensionCategory.target (C := C)).map (ExtensionCategory.mkHom
        (ExtensionDiagram.ofRowIso e)) =
      (QuillenQ.underlyingIso ((ShortComplex.π₃ (C := C)).mapIso e)).hom := by
  have hSpan := ExtensionDiagram.ofRowIso_toQuillenSpan e
  have hMap := ExtensionCategory.target_map_mkHom (ExtensionDiagram.ofRowIso e)
  exact hMap.trans ((congrArg (fun s : QuillenSpan E'.row.X₃ E.row.X₃ =>
    QuillenQ.mkHom (X := (⟨E'.row.X₃⟩ : QuillenQ C))
      (Y := (⟨E.row.X₃⟩ : QuillenQ C)) s) hSpan).trans
        (QuillenQ.underlyingIso_hom ((ShortComplex.π₃ (C := C)).mapIso e)).symm)


private theorem rowIsoDiagramHomInv {E' E : ExtensionCategory C}
    (e : E'.row ≅ E.row) :
    ExtensionCategory.mkHom (ExtensionDiagram.ofRowIso e) ≫
        ExtensionCategory.mkHom (ExtensionDiagram.ofRowIso e.symm) = 𝟙 E' := by
  let d := ExtensionDiagram.ofRowIso e
  let r := ExtensionDiagram.ofRowIso e.symm
  have hAlpha :
      (ExtensionDiagram.ofNormalization (d.normalize ≫ r.normalize)).alpha =
        (ExtensionDiagram.id E').alpha := by
    have hComp := ExtensionDiagram.ofNormalization_comp_alpha d r
    have hCancel : r.alpha ≫ d.alpha = (ExtensionDiagram.id E').alpha := by
      change e.hom.τ₁ ≫ e.inv.τ₁ = 𝟙 E'.row.X₁
      exact (rowComponentIso₁ e).hom_inv_id
    exact hComp.trans hCancel
  have hBeta :
      (ExtensionDiagram.ofNormalization (d.normalize ≫ r.normalize)).beta =
        (ExtensionDiagram.id E').beta := by
    have hComp := ExtensionDiagram.ofNormalization_comp_beta d r
    have hCancel : d.beta ≫ r.beta = (ExtensionDiagram.id E').beta := by
      change e.hom.τ₂ ≫ e.inv.τ₂ = 𝟙 E'.row.X₂
      exact (rowComponentIso₂ e).hom_inv_id
    exact hComp.trans hCancel
  have hRel := ExtensionDiagram.rel_of_components_eq hAlpha hBeta
  exact (ExtensionCategory.mkHom_comp d r).trans
    ((ExtensionCategory.mkHom_eq_iff _ _).2 hRel)

private def rowIsoToExtensionIso {E' E : ExtensionCategory C}
    (e : E'.row ≅ E.row) : E' ≅ E where
  hom := ExtensionCategory.mkHom (ExtensionDiagram.ofRowIso e)
  inv := ExtensionCategory.mkHom (ExtensionDiagram.ofRowIso e.symm)
  hom_inv_id := rowIsoDiagramHomInv e
  inv_hom_id := rowIsoDiagramHomInv e.symm

/-- A given ordinary isomorphism of actual rows induces an actual extension-category Iso. -/
public def ExtensionCategory.isoOfRowIso {E' E : ExtensionCategory C}
    (e : E'.row ≅ E.row) : E' ≅ E :=
  rowIsoToExtensionIso e

private theorem rowIsoExtensionHomComputed {E' E : ExtensionCategory C}
    (e : E'.row ≅ E.row) :
    (ExtensionCategory.isoOfRowIso e).hom =
      ExtensionCategory.mkHom (ExtensionDiagram.ofRowIso e) := rfl

/-- Its forward arrow is the original given-source-quotient diagram. -/
public theorem ExtensionCategory.isoOfRowIso_hom {E' E : ExtensionCategory C}
    (e : E'.row ≅ E.row) :
    (ExtensionCategory.isoOfRowIso e).hom =
      ExtensionCategory.mkHom (ExtensionDiagram.ofRowIso e) :=
  rowIsoExtensionHomComputed e

private theorem rowIsoExtensionTargetComputed {E' E : ExtensionCategory C}
    (e : E'.row ≅ E.row) :
    (ExtensionCategory.target (C := C)).mapIso (ExtensionCategory.isoOfRowIso e) =
      QuillenQ.underlyingIso ((ShortComplex.π₃ (C := C)).mapIso e) := by
  apply Iso.ext
  change (ExtensionCategory.target (C := C)).map
      (ExtensionCategory.mkHom (ExtensionDiagram.ofRowIso e)) = _
  exact ExtensionDiagram.ofRowIso_target e

/-- The complete extension Iso has the same canonical third-component Q image. -/
public theorem ExtensionCategory.isoOfRowIso_target {E' E : ExtensionCategory C}
    (e : E'.row ≅ E.row) :
    (ExtensionCategory.target (C := C)).mapIso (ExtensionCategory.isoOfRowIso e) =
      QuillenQ.underlyingIso ((ShortComplex.π₃ (C := C)).mapIso e) :=
  rowIsoExtensionTargetComputed e


private theorem rowIsoDiagramComponentsComputed {E' E : ExtensionCategory C}
    (e : E'.row ≅ E.row) :
    (ExtensionDiagram.ofRowIso e).alpha = e.inv.τ₁ ∧
      (ExtensionDiagram.ofRowIso e).beta = e.hom.τ₂ ∧
      (ExtensionDiagram.ofRowIso e).D = E'.row.X₃ ∧
      (ExtensionDiagram.ofRowIso e).j = e.inv.τ₁ ≫ E'.row.f ∧
      HEq (ExtensionDiagram.ofRowIso e).q E'.row.g ∧
      HEq (ExtensionDiagram.ofRowIso e).lambda (𝟙 E'.row.X₃) ∧
      HEq (ExtensionDiagram.ofRowIso e).mu e.hom.τ₃ :=
  ⟨rfl, rfl, rfl, rfl, heq_of_eq rfl, heq_of_eq rfl, heq_of_eq rfl⟩

/-- The original quotient diagram retains the actual row-Iso component values. -/
public theorem ExtensionDiagram.ofRowIso_components {E' E : ExtensionCategory C}
    (e : E'.row ≅ E.row) :
    (ExtensionDiagram.ofRowIso e).alpha = e.inv.τ₁ ∧
      (ExtensionDiagram.ofRowIso e).beta = e.hom.τ₂ ∧
      (ExtensionDiagram.ofRowIso e).D = E'.row.X₃ ∧
      (ExtensionDiagram.ofRowIso e).j = e.inv.τ₁ ≫ E'.row.f ∧
      HEq (ExtensionDiagram.ofRowIso e).q E'.row.g ∧
      HEq (ExtensionDiagram.ofRowIso e).lambda (𝟙 E'.row.X₃) ∧
      HEq (ExtensionDiagram.ofRowIso e).mu e.hom.τ₃ :=
  rowIsoDiagramComponentsComputed e

end AlgebraicKTheory

end
