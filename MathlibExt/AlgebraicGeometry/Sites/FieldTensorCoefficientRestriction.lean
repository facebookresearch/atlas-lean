/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.RepresentationTheory.Homological.ContCohomology.DiscreteCoefficientCupGroupNaturality
public import MathlibExt.AlgebraicGeometry.Sites.FieldPointTensorCoefficients
public import MathlibExt.AlgebraicGeometry.Sites.EtaleGaloisCohomologyComparison

/-! # Genuine restriction of original field coefficient tensors and cups -/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory
open scoped TensorProduct
universe u v w r


namespace AlgebraicGeometry.Scheme.DerivedSections

open Opposite
attribute [local instance] IsSepClosure.sep_closed

variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
variable (K Ψ : Type v) [Field K] [Field Ψ] [Algebra K Ψ] [IsSepClosure K Ψ]

/-- Genuine group restriction preserves the original binary integer tensor, with the
same stored coefficient modules and independent original field-group universes. -/
def fieldTensorCoefficientModuleRestrictionIso
    (φ : InfiniteGalois.profiniteGalGrp K Ψ →ₜ* InfiniteGalois.profiniteGalGrp k Ω)
    (M N : FieldCohomologyModule.{u, max v r} k Ω) :
    (fieldModuleRestriction.{u, v, r} k Ω K Ψ φ).obj
        (fieldTensorCoefficientModule.{u, max v r} k Ω M N) ≅
      fieldTensorCoefficientModule.{v, max u r} K Ψ
        ((fieldModuleRestriction.{u, v, r} k Ω K Ψ φ).obj M)
        ((fieldModuleRestriction.{u, v, r} k Ω K Ψ φ).obj N) :=
  Iso.refl _

/-- Its underlying coefficient map is the original identity on every original tensor vector. -/
theorem fieldTensorCoefficientModuleRestrictionIso_hom_apply
    (φ : InfiniteGalois.profiniteGalGrp K Ψ →ₜ* InfiniteGalois.profiniteGalGrp k Ω)
    (M N : FieldCohomologyModule.{u, max v r} k Ω)
    (x : DiscreteAbelianAction.underlying (fieldTensorCoefficientModule.{u, max v r} k Ω M N)) :
    DiscreteAbelianAction.homToAdd
      (fieldTensorCoefficientModuleRestrictionIso.{u, v, r} k Ω K Ψ φ M N).hom x = x := rfl

local instance originalFieldNativeModuleDiscrete (M : FieldCohomologyModule.{u, r} k Ω) :
    DiscreteTopology ((ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, r}
      (InfiniteGalois.profiniteGalGrp k Ω)).obj M) := M.property

/-- The actual binary integer tensor arrow of two original Galois coefficient arrows. -/
def fieldTensorCoefficientModuleMap
    {M N M' N' : FieldCohomologyModule.{u, r} k Ω} (f : M ⟶ M') (g : N ⟶ N') :
    fieldTensorCoefficientModule.{u, r} k Ω M N ⟶
        fieldTensorCoefficientModule.{u, r} k Ω M' N' := by
  let P := ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, r}
    (InfiniteGalois.profiniteGalGrp k Ω)
  let t := ContinuousCohomology.discreteTensorCoefficientMap.{0, u, r} (P.map f) (P.map g)
  exact DiscreteAbelianAction.ofAddHom ⟨t.hom.toAddMonoidHom, by
    intro h x
    exact TopRep.hom_comm_apply t h x⟩

/-- The original tensor coefficient arrow retains the SAME computed native tensor map value. -/
theorem fieldTensorCoefficientModuleMap_hom_apply
    {M N M' N' : FieldCohomologyModule.{u, r} k Ω} (f : M ⟶ M') (g : N ⟶ N')
    (x : DiscreteAbelianAction.underlying (fieldTensorCoefficientModule.{u, r} k Ω M N)) :
    let P := ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, r}
      (InfiniteGalois.profiniteGalGrp k Ω)
    DiscreteAbelianAction.homToAdd (fieldTensorCoefficientModuleMap.{u, r} k Ω f g) x =
      (ContinuousCohomology.discreteTensorCoefficientMap.{0, u, r} (P.map f) (P.map g)).hom x := by
  rfl

/-- Two original coefficient isomorphisms induce the actual binary tensor isomorphism. -/
def fieldTensorCoefficientModuleIso
    {M N M' N' : FieldCohomologyModule.{u, r} k Ω} (e : M ≅ M') (d : N ≅ N') :
    fieldTensorCoefficientModule.{u, r} k Ω M N ≅
        fieldTensorCoefficientModule.{u, r} k Ω M' N' := by
  let P := ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, r}
    (InfiniteGalois.profiniteGalGrp k Ω)
  letI : Module ℤ (P.obj M) := (P.obj M).hV2
  letI : Module ℤ (P.obj N) := (P.obj N).hV2
  letI : Module ℤ (P.obj M') := (P.obj M').hV2
  letI : Module ℤ (P.obj N') := (P.obj N').hV2
  let E := ((DiscreteAbelianAction.forget Gal(Ω/k)).mapIso e).addCommGroupIsoToAddEquiv
  let D := ((DiscreteAbelianAction.forget Gal(Ω/k)).mapIso d).addCommGroupIsoToAddEquiv
  let ef := LinearEquiv.ofBijective (P.map e.hom).hom.toLinearMap
    (show Function.Bijective (P.map e.hom).hom.toLinearMap from E.bijective)
  let df := LinearEquiv.ofBijective (P.map d.hom).hom.toLinearMap
    (show Function.Bijective (P.map d.hom).hom.toLinearMap from D.bijective)
  exact DiscreteAbelianAction.isoOfBijective
      (fieldTensorCoefficientModuleMap.{u, r} k Ω e.hom d.hom)
    (show Function.Bijective (TensorProduct.map (P.map e.hom).hom.toLinearMap
      (P.map d.hom).hom.toLinearMap) from (TensorProduct.congr ef df).bijective)

/-- The tensor isomorphism retains the actual original coefficient tensor map. -/
theorem fieldTensorCoefficientModuleIso_hom
    {M N M' N' : FieldCohomologyModule.{u, r} k Ω} (e : M ≅ M') (d : N ≅ N') :
    (fieldTensorCoefficientModuleIso.{u, r} k Ω e d).hom =
      fieldTensorCoefficientModuleMap.{u, r} k Ω e.hom d.hom := rfl

variable (K₀ Ψ₀ : Type u) [Field K₀] [Field Ψ₀]
  [Algebra K₀ Ψ₀] [IsSepClosure K₀ Ψ₀]

/-- Binary restriction on the actual original field tensor coefficient rank. -/
def originalFieldTensorRestrictionIso
    (φ : InfiniteGalois.profiniteGalGrp K₀ Ψ₀ →ₜ* InfiniteGalois.profiniteGalGrp k Ω)
    (M N : FieldCohomologyModule.{u, r} k Ω) :
    (GaloisUnits.restrictModules φ).obj (fieldTensorCoefficientModule.{u, r} k Ω M N) ≅
      fieldTensorCoefficientModule.{u, r} K₀ Ψ₀
        ((GaloisUnits.restrictModules φ).obj M) ((GaloisUnits.restrictModules φ).obj N) :=
  Iso.refl _

/-- Original tensor germs commute with genuine field module restriction. -/
def fieldTensorSheafRestrictedStalkIso
    (φ : InfiniteGalois.profiniteGalGrp K₀ Ψ₀ →ₜ* InfiniteGalois.profiniteGalGrp k Ω)
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u r}) :
    let R := fieldModuleRestriction.{u, u, r} k Ω K₀ Ψ₀ φ
    let J := fieldGeometricStalkGaloisFunctor.{u, r} k Ω
    let A := J.obj F
    let B := J.obj G
    let S := J.obj (smallEtaleTensorSheaf.{u, r} (Spec (.of k)) F G)
    let T := fieldTensorCoefficientModule.{u, r} k Ω A B
    let _ : S ≅ T := fieldPointTensorGaloisIso.{u, r} k Ω F G
    R.obj S ≅ fieldTensorCoefficientModule.{u, r} K₀ Ψ₀ (R.obj A) (R.obj B) := by
  intro R J A B S T α
  exact R.mapIso α ≪≫ originalFieldTensorRestrictionIso.{u, r} k Ω K₀ Ψ₀ φ A B

/-- The actual field change on both original fibers induces its genuine binary tensor iso. -/
def fieldTensorSheafPullbackFactorIso (e : GaloisUnits.FieldMap k Ω K₀ Ψ₀)
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u r}) :
    let L := smallEtaleInverseImage.{u, r} (fieldOriginalPullback k Ω K₀ Ψ₀ e)
    let R := fieldModuleRestriction.{u, u, r} k Ω K₀ Ψ₀ (GaloisUnits.FieldMap.restrictContinuous e)
    fieldTensorCoefficientModule.{u, r} K₀ Ψ₀
        (R.obj ((fieldGeometricStalkGaloisFunctor.{u, r} k Ω).obj F))
        (R.obj ((fieldGeometricStalkGaloisFunctor.{u, r} k Ω).obj G)) ≅
      fieldTensorCoefficientModule.{u, r} K₀ Ψ₀
        ((fieldGeometricStalkGaloisFunctor.{u, r} K₀ Ψ₀).obj (L.obj F))
        ((fieldGeometricStalkGaloisFunctor.{u, r} K₀ Ψ₀).obj (L.obj G)) := by
  intro L R
  exact fieldTensorCoefficientModuleIso.{u, r} K₀ Ψ₀
    ((fieldChangeStalkModuleIso.{u, r} k Ω K₀ Ψ₀ e).app F)
    ((fieldChangeStalkModuleIso.{u, r} k Ω K₀ Ψ₀ e).app G)

/-- The computed original field pullback coefficient tensor isomorphism uses the
actual closure-change, restriction, and original tensor-of-germs maps. -/
def fieldTensorSheafPullbackGaloisIso (e : GaloisUnits.FieldMap k Ω K₀ Ψ₀)
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u r}) :
    let L := smallEtaleInverseImage.{u, r} (fieldOriginalPullback k Ω K₀ Ψ₀ e)
    (fieldGeometricStalkGaloisFunctor.{u, r} K₀ Ψ₀).obj
        (L.obj (smallEtaleTensorSheaf.{u, r} (Spec (.of k)) F G)) ≅
      (fieldGeometricStalkGaloisFunctor.{u, r} K₀ Ψ₀).obj
        (smallEtaleTensorSheaf.{u, r} (Spec (.of K₀)) (L.obj F) (L.obj G)) := by
  intro L
  let a := ((fieldChangeStalkModuleIso.{u, r} k Ω K₀ Ψ₀ e).app
    (smallEtaleTensorSheaf.{u, r} (Spec (.of k)) F G)).symm
  let b := fieldTensorSheafRestrictedStalkIso.{u, r} k Ω K₀ Ψ₀
    (GaloisUnits.FieldMap.restrictContinuous e) F G
  let c := fieldTensorSheafPullbackFactorIso.{u, r} k Ω K₀ Ψ₀ e F G
  let d := (fieldPointTensorGaloisIso.{u, r} K₀ Ψ₀ (L.obj F) (L.obj G)).symm
  exact a ≪≫ b ≪≫ c ≪≫ d

/-- The actual field inverse image preserves the original binary integer tensor sheaf,
through the original geometric fibers, genuine restriction, and actual closure comparison. -/
def fieldTensorSheafPullbackIso (e : GaloisUnits.FieldMap k Ω K₀ Ψ₀)
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u r}) :
    (smallEtaleInverseImage.{u, r} (fieldOriginalPullback k Ω K₀ Ψ₀ e)).obj
        (smallEtaleTensorSheaf.{u, r} (Spec (.of k)) F G) ≅
      smallEtaleTensorSheaf.{u, r} (Spec (.of K₀))
        ((smallEtaleInverseImage.{u, r} (fieldOriginalPullback k Ω K₀ Ψ₀ e)).obj F)
        ((smallEtaleInverseImage.{u, r} (fieldOriginalPullback k Ω K₀ Ψ₀ e)).obj G) := by
  let C := Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u r}
  let D := Sheaf (Spec (.of K₀)).smallEtaleTopology AddCommGrpCat.{max u r}
  let L : C ⥤ D := smallEtaleInverseImage.{u, r} (fieldOriginalPullback k Ω K₀ Ψ₀ e)
  let S : D := L.obj (smallEtaleTensorSheaf.{u, r} (Spec (.of k)) F G)
  let T : D := smallEtaleTensorSheaf.{u, r} (Spec (.of K₀)) (L.obj F) (L.obj G)
  let E : D ≌ FieldCohomologyModule.{u, r} K₀ Ψ₀ :=
    fieldSheafGaloisEquivalence.{u, r} K₀ Ψ₀
  let P : D ⥤ FieldCohomologyModule.{u, r} K₀ Ψ₀ := E.functor
  let _ : P.Full := E.full_functor
  let _ : P.Faithful := E.faithful_functor
  let α : P.obj S ≅ P.obj T :=
    fieldTensorSheafPullbackGaloisIso.{u, r} k Ω K₀ Ψ₀ e F G
  exact P.preimageIso (X := S) (Y := T) α

/-- The actual target geometric-fiber functor recovers the same constructed field tensor map. -/
theorem fieldTensorSheafPullbackIso_map (e : GaloisUnits.FieldMap k Ω K₀ Ψ₀)
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u r}) :
    (fieldGeometricStalkGaloisFunctor.{u, r} K₀ Ψ₀).map
        (fieldTensorSheafPullbackIso.{u, r} k Ω K₀ Ψ₀ e F G).hom =
      (fieldTensorSheafPullbackGaloisIso.{u, r} k Ω K₀ Ψ₀ e F G).hom := by
  let L := smallEtaleInverseImage.{u, r} (fieldOriginalPullback k Ω K₀ Ψ₀ e)
  let S := L.obj (smallEtaleTensorSheaf.{u, r} (Spec (.of k)) F G)
  let T := smallEtaleTensorSheaf.{u, r} (Spec (.of K₀)) (L.obj F) (L.obj G)
  exact (fieldSheafGaloisEquivalence.{u, r} K₀ Ψ₀).functor.map_preimage (X := S) (Y := T)
    (fieldTensorSheafPullbackGaloisIso.{u, r} k Ω K₀ Ψ₀ e F G).hom

private theorem tensorPullbackIsoSquare.{c₁, c₂}
    {C : Type c₁} [Category.{c₂} C] {A B D E Z : C}
    (e : A ≅ B) (f : A ≅ D) (g : D ≅ E) (h : Z ≅ E) :
    e.hom ≫ (e.symm ≪≫ f ≪≫ g ≪≫ h.symm).hom ≫ h.hom = f.hom ≫ g.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- The actual field tensor pullback commutes with the original geometric-fiber coefficient maps. -/
theorem fieldTensorSheafPullbackIso_tensor_square (e : GaloisUnits.FieldMap k Ω K₀ Ψ₀)
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u r}) :
    let L := smallEtaleInverseImage.{u, r} (fieldOriginalPullback k Ω K₀ Ψ₀ e)
    let J' := fieldGeometricStalkGaloisFunctor.{u, r} K₀ Ψ₀
    let χ := fieldChangeStalkModuleIso.{u, r} k Ω K₀ Ψ₀ e
    let b := fieldTensorSheafRestrictedStalkIso.{u, r} k Ω K₀ Ψ₀
      (GaloisUnits.FieldMap.restrictContinuous e) F G
    let c := fieldTensorSheafPullbackFactorIso.{u, r} k Ω K₀ Ψ₀ e F G
    let α := fieldPointTensorGaloisIso.{u, r} K₀ Ψ₀ (L.obj F) (L.obj G)
    (χ.app (smallEtaleTensorSheaf.{u, r} (Spec (.of k)) F G)).hom ≫
        J'.map (fieldTensorSheafPullbackIso.{u, r} k Ω K₀ Ψ₀ e F G).hom ≫ α.hom =
      b.hom ≫ c.hom := by
  intro L J' χ b c α
  let χT := χ.app (smallEtaleTensorSheaf.{u, r} (Spec (.of k)) F G)
  have he : fieldTensorSheafPullbackGaloisIso.{u, r} k Ω K₀ Ψ₀ e F G =
      χT.symm ≪≫ b ≪≫ c ≪≫ α.symm := rfl
  rw [fieldTensorSheafPullbackIso_map, he]
  exact tensorPullbackIsoSquare χT b c α

/-- Restriction along the actual compatible field map preserves the original native cup,
using the SAME already-constructed original-rank field cohomology restriction on both factors. -/
theorem fieldOriginalRankRestrictionTensorCup
    (e : GaloisUnits.FieldMap k Ω K₀ Ψ₀) (M N : FieldCohomologyModule.{u, r} k Ω)
    (p q : ℕ) (x : (fieldContinuousCohomologyFunctor.{u, r} k Ω p).obj M)
    (y : (fieldContinuousCohomologyFunctor.{u, r} k Ω q).obj N) :
    let φ := GaloisUnits.FieldMap.restrictContinuous e
    let R := fieldModuleRestriction.{u, u, r} k Ω K₀ Ψ₀ φ
    let P := ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, r}
      (InfiniteGalois.profiniteGalGrp k Ω)
    let P' := ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, r}
      (InfiniteGalois.profiniteGalGrp K₀ Ψ₀)
    let f := fieldModuleRestrictionTopRepHom.{u, u, r} k Ω K₀ Ψ₀ φ M
    let g := fieldModuleRestrictionTopRepHom.{u, u, r} k Ω K₀ Ψ₀ φ N
    ContinuousCohomology.map φ
        (ContinuousCohomology.discreteTensorGroupCoefficientHom.{0, u, u, r}
          (A := P.obj M) (B := P.obj N) (A' := P'.obj (R.obj M))
              (B' := P'.obj (R.obj N)) φ f g) (p + q)
        (ContinuousCohomology.discreteContinuousCup.{0, u, r} (P.obj M) (P.obj N) p q x y) =
      ContinuousCohomology.discreteContinuousCup.{0, u, r} (P'.obj (R.obj M)) (P'.obj (R.obj N)) p q
        ((CategoryTheory.CohomologicalDeltaFunctor.Hom.app
          (fieldOriginalRankRestrictionDeltaHom.{u, r} k Ω K₀ Ψ₀ φ) p).app M x)
        ((CategoryTheory.CohomologicalDeltaFunctor.Hom.app
          (fieldOriginalRankRestrictionDeltaHom.{u, r} k Ω K₀ Ψ₀ φ) q).app N y) := by
  intro φ R P P' f g
  have hx := ConcreteCategory.congr_hom
    (fieldOriginalRankRestrictionDeltaHom_original_map.{u, r} k Ω K₀ Ψ₀ φ p M) x
  have hy := ConcreteCategory.congr_hom
    (fieldOriginalRankRestrictionDeltaHom_original_map.{u, r} k Ω K₀ Ψ₀ φ q N) y
  change (CategoryTheory.CohomologicalDeltaFunctor.Hom.app
      (fieldOriginalRankRestrictionDeltaHom.{u, r} k Ω K₀ Ψ₀ φ) p).app M x =
    ContinuousCohomology.map φ f p x at hx
  change (CategoryTheory.CohomologicalDeltaFunctor.Hom.app
      (fieldOriginalRankRestrictionDeltaHom.{u, r} k Ω K₀ Ψ₀ φ) q).app N y =
    ContinuousCohomology.map φ g q y at hy
  exact (ContinuousCohomology.discreteContinuousCup_group_naturality_original_rank.{0, u, r}
    (X := P.obj M) (Y := P.obj N) (X' := P'.obj (R.obj M)) (Y' := P'.obj (R.obj N))
    φ f g p q x y).trans (congrArg₂ (fun a b => ContinuousCohomology.discreteContinuousCup.{0, u, r}
      (P'.obj (R.obj M)) (P'.obj (R.obj N)) p q a b) hx.symm hy.symm)

end AlgebraicGeometry.Scheme.DerivedSections
