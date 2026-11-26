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

/-!
# Canonical coinduction complexes and geometric fibers

The coinduction monad on discrete `Gal(Ω/k)`-modules gives a coaugmented cosimplicial object.
Its alternating coface complex is the canonical coinduction complex, with a cochain map from
the coefficient in degree zero.

Applying the field geometric-stalk functor to the Godement complex identifies it with this
coinduction complex. The comparison has the coinduction term maps as components and respects
coaugmentation. For geometric-fiber coefficients, the canonical coaugmentation is a quasi-
isomorphism.
-/
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

/-- Canonical coinduction cochain complex.

Take the alternating coface complex of the coinduction-monad coresolution of a discrete Galois
module. -/
def fieldCoindCanonicalComplex
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    CochainComplex (DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) ℕ :=
  AlternatingCofaceMapComplex.obj
    (Monad.coresolution (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)) M)

/-- Coinduction coaugmentation is a degree zero cocycle.

The augmented monad unit at the zero simplex followed by the first coinduction differential is
zero. -/
theorem fieldCoindCanonicalCoaugmentation_closed
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    (Monad.coresolutionAugmented (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)) M).hom.app
      (SimplexCategory.mk 0) ≫ (fieldCoindCanonicalComplex.{u, w} k Ω M).d 0 1 = 0 :=
  actualCosimplicialCoaugmentation_closed
    (Monad.coresolutionAugmented (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)) M)

/-- Coinduction cochain coaugmentation.

The augmented cosimplicial unit gives a cochain map from the coefficient module concentrated
in degree zero to its canonical coinduction complex. -/
def fieldCoindCanonicalCoaugmentation
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    (CochainComplex.single₀ (DiscreteAbelianAction.{u, max u w} Gal(Ω/k))).obj M ⟶
      fieldCoindCanonicalComplex.{u, w} k Ω M :=
  (CochainComplex.fromSingle₀Equiv (fieldCoindCanonicalComplex.{u, w} k Ω M) M).symm
    ⟨(Monad.coresolutionAugmented (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)) M).hom.app
      (SimplexCategory.mk 0), fieldCoindCanonicalCoaugmentation_closed.{u, w} k Ω M⟩

/-- Degree zero coinduction coaugmentation is the augmented unit.

The coaugmentation's degree-zero component is the augmented monad-coresolution map at the zero
simplex. -/
theorem fieldCoindCanonicalCoaugmentation_f_zero
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    (fieldCoindCanonicalCoaugmentation.{u, w} k Ω M).f 0 =
      (Monad.coresolutionAugmented (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)) M).hom.app
        (SimplexCategory.mk 0) := CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-- Geometric fiber of the Godement complex is canonical coinduction.

The field geometric-stalk Galois functor sends the Godement cochain complex to a complex
isomorphic to canonical coinduction of the geometric fiber. -/
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
/-- Godement coinduction comparison has the term comparison components.

In every degree, the forward complex comparison is the corresponding Godement-to-coinduction
coresolution term map. -/
theorem fieldGodementCoindCanonicalComplexIso_hom_f
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ) :
    (fieldGodementCoindCanonicalComplexIso.{u, w} k Ω F).hom.f n =
      (fieldGodementCoindCoresolutionTermIso.{u, w} k Ω F n).hom := by
  rw [fieldGodementCoindCanonicalComplexIso]
  change (𝟙 _) ≫ (fieldGodementCoindCoresolutionTermIso.{u, w} k Ω F n).hom = _
  exact Category.id_comp _

set_option backward.isDefEq.respectTransparency.types false in
/-- Godement coinduction comparison respects coaugmentation.

After the single-complex functor coordinate, the image of the Godement coaugmentation followed
by comparison equals the canonical coinduction coaugmentation. -/
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
/-- Geometric fiber coinduction coaugmentation is a quasi isomorphism.

For the geometric fiber of a field sheaf, the canonical coinduction coaugmentation is a quasi-
isomorphism. -/
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
