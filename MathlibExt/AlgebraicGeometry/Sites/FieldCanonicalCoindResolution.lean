/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import MathlibExt.AlgebraicGeometry.Sites.FieldGodementCoindCoaugmentation
public import MathlibExt.AlgebraicGeometry.Sites.FieldModuleCohomologyCategory
public import Mathlib.Algebra.Homology.QuasiIso

/-! The actual field coinduction complex has its canonical augmented quasi-isomorphism. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w uC vC
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped BigOperators

private theorem actualCosimplicialCoaugmentation_closed
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    (S : CosimplicialObject.Augmented C) :
    S.hom.app (SimplexCategory.mk 0) ≫ AlternatingCofaceMapComplex.objD S.right 0 = 0 := by
  let η := S.hom.app (SimplexCategory.mk 0)
  have h₀ := S.hom.naturality (SimplexCategory.δ (0 : Fin 2))
  have h₁ := S.hom.naturality (SimplexCategory.δ (1 : Fin 2))
  have he : η ≫ S.right.δ (0 : Fin 2) = η ≫ S.right.δ (1 : Fin 2) := h₀.symm.trans h₁
  change η ≫ ∑ i : Fin 2, (-1 : ℤ) ^ i.val • S.right.δ i = 0
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul,
    neg_one_zsmul, Preadditive.comp_add, Preadditive.comp_neg]
  rw [he]
  exact add_neg_cancel _

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- The same original canonical alternating coinduction complex in the actual field action category. -/
def fieldCoindCanonicalComplex
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    CochainComplex (DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) ℕ :=
  AlternatingCofaceMapComplex.obj
    (Monad.coresolution (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)) M)

/-- The original augmented monad unit is closed in the canonical complex. -/
theorem fieldCoindCanonicalCoaugmentation_closed
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    (Monad.coresolutionAugmented (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)) M).hom.app
      (SimplexCategory.mk 0) ≫ (fieldCoindCanonicalComplex.{u, w} k Ω M).d 0 1 = 0 :=
  actualCosimplicialCoaugmentation_closed
    (Monad.coresolutionAugmented (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)) M)

/-- The literal canonical monad coaugmentation on the same original field coefficient. -/
def fieldCoindCanonicalCoaugmentation
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    (CochainComplex.single₀ (DiscreteAbelianAction.{u, max u w} Gal(Ω/k))).obj M ⟶
      fieldCoindCanonicalComplex.{u, w} k Ω M :=
  (CochainComplex.fromSingle₀Equiv (fieldCoindCanonicalComplex.{u, w} k Ω M) M).symm
    ⟨(Monad.coresolutionAugmented (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)) M).hom.app
      (SimplexCategory.mk 0), fieldCoindCanonicalCoaugmentation_closed.{u, w} k Ω M⟩

/-- Its degree-zero component retains the actual augmented monad unit. -/
theorem fieldCoindCanonicalCoaugmentation_f_zero
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    (fieldCoindCanonicalCoaugmentation.{u, w} k Ω M).f 0 =
      (Monad.coresolutionAugmented (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)) M).hom.app
        (SimplexCategory.mk 0) := CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-- The actual original mapped Godement complex identifies with the same canonical coinduction complex. -/
def fieldGodementCoindCanonicalComplexIso
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (smallEtaleGodementCochainComplex.{u, w} (Spec (.of k)) F) ≅
    fieldCoindCanonicalComplex.{u, w} k Ω ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F) :=
  let J := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
  let A := smallEtaleGodementCoresolution.{u, w} (Spec (.of k)) F
  let e : AlternatingCofaceMapComplex.obj (A ⋙ J) ≅
      ((J.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (AlternatingCofaceMapComplex.obj A)) :=
    HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
      (fun i j hij => additiveAlternatingCofaceComm J A i j hij)
  e.symm ≪≫ (fieldGodementCoindCofaceIso.{u, w} k Ω F).alternatingIso

set_option backward.isDefEq.respectTransparency.types false in
/-- Every original canonical complex component retains its actual prescribed coinduction term map. -/
theorem fieldGodementCoindCanonicalComplexIso_hom_f
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ) :
    (fieldGodementCoindCanonicalComplexIso.{u, w} k Ω F).hom.f n =
      (fieldGodementCoindCoresolutionTermIso.{u, w} k Ω F n).hom := by
  rw [fieldGodementCoindCanonicalComplexIso]
  change (𝟙 _) ≫ (fieldGodementCoindCoresolutionTermIso.{u, w} k Ω F n).hom = _
  exact Category.id_comp _

set_option backward.isDefEq.respectTransparency.types false in
/-- The SAME original mapped Godement comparison commutes with the actual coaugmentations. -/
theorem fieldGodementCoindCanonicalComplexIso_coaugmentation
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (HomologicalComplex.singleMapHomologicalComplex (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
      (ComplexShape.up ℕ) 0).inv.app F ≫
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (smallEtaleGodementCochainCoaugmentation.{u, w} (Spec (.of k)) F) ≫
      (fieldGodementCoindCanonicalComplexIso.{u, w} k Ω F).hom =
    fieldCoindCanonicalCoaugmentation.{u, w} k Ω
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F) := by
  apply (CochainComplex.fromSingle₀Equiv _ _).injective
  apply Subtype.ext
  change (((HomologicalComplex.singleMapHomologicalComplex
      (fieldGeometricStalkGaloisFunctor.{u, w} k Ω) (ComplexShape.up ℕ) 0).inv.app F ≫
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapHomologicalComplex
          (ComplexShape.up ℕ)).map
            (smallEtaleGodementCochainCoaugmentation.{u, w} (Spec (.of k)) F) ≫
        (fieldGodementCoindCanonicalComplexIso.{u, w} k Ω F).hom).f 0) =
      (fieldCoindCanonicalCoaugmentation.{u, w} k Ω
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F)).f 0
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    smallEtaleGodementCochainCoaugmentation_f_zero, fieldCoindCanonicalCoaugmentation_f_zero]
  have hz : ((HomologicalComplex.singleMapHomologicalComplex
      (fieldGeometricStalkGaloisFunctor.{u, w} k Ω) (ComplexShape.up ℕ) 0).inv.app F).f 0 =
      𝟙 ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F) := by
    rw [HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      CochainComplex.single₀ObjXSelf, CochainComplex.single₀ObjXSelf]
    change (𝟙 _) ≫ (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map (𝟙 F) = _
    rw [(fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map_id, Category.id_comp]
  have hzi :
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F)).hom ≫
      (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).inv =
        𝟙 ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F) :=
    (HomologicalComplex.singleMapHomologicalComplex_inv_app_self
      (fieldGeometricStalkGaloisFunctor.{u, w} k Ω) (ComplexShape.up ℕ) 0 F).symm.trans hz
  rw [hzi, fieldGodementCoindCanonicalComplexIso_hom_f]
  change (𝟙 _) ≫ (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
      ((smallEtaleGodementUnit.{u, w} (Spec (.of k))).app F) ≫
        (fieldGodementCoindCoresolutionTermIso.{u, w} k Ω F 0).hom = _
  exact (Category.id_comp _).trans
    ((congrArg (fun q => (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map q ≫
        (fieldGodementCoindCoresolutionTermIso.{u, w} k Ω F 0).hom)
        (smallEtaleGodementAugmentedCoresolution_unit.{u, w} (Spec (.of k)) F).symm).trans
      (fieldGodementCoindCoresolutionTermIso_coaugmentation.{u, w} k Ω F))

set_option backward.isDefEq.respectTransparency.types false in
/-- The genuine mapped Godement quasi-isomorphism makes the canonical coinduction
coaugmentation a quasi-isomorphism for every original geometric coefficient. -/
theorem fieldCoindCanonicalCoaugmentation_quasiIso_geometric
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    QuasiIso (fieldCoindCanonicalCoaugmentation.{u, w} k Ω
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F)) := by
  let J := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
  let ι := smallEtaleGodementCochainCoaugmentation.{u, w} (Spec (.of k)) F
  let : QuasiIso ι := smallEtaleGodementCochainCoaugmentation_quasiIso.{u, w} (Spec (.of k)) F
  have hmap : QuasiIso ((J.mapHomologicalComplex (ComplexShape.up ℕ)).map ι) := inferInstance
  have h : QuasiIso ((HomologicalComplex.singleMapHomologicalComplex J (ComplexShape.up ℕ) 0).inv.app F ≫
      (J.mapHomologicalComplex (ComplexShape.up ℕ)).map ι ≫
      (fieldGodementCoindCanonicalComplexIso.{u, w} k Ω F).hom) := by infer_instance
  exact (fieldGodementCoindCanonicalComplexIso_coaugmentation.{u, w} k Ω F) ▸ h

end AlgebraicGeometry.Scheme.DerivedSections
