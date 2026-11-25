/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado

module

public import MathlibExt.AlgebraicGeometry.Sites.FieldGammaCohomologyComparison
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleDerivedConnectingComparison
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleCoefficientLiftExactness
public import MathlibExt.AlgebraicGeometry.Sites.FieldCohomologyUniverseComparison
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleDerivedGammaPullback
public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.PrecompositionCoherence
public import MathlibExt.CategoryTheory.Abelian.RightDerived.ResolutionRealization
public import MathlibExt.CategoryTheory.NatIso.ComparisonCoherence

/-!
# Original field, site and module cohomology maps on the same cochains and resolutions
-/

@[expose] public section

noncomputable section

set_option autoImplicit false


section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.DerivedSections

attribute [local instance] IsSepClosure.sep_closed
variable (k Ω K Ψ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ] [IsSepClosure k Ω] [IsSepClosure K Ψ]

local instance fieldNativeInverseImage_additive (e : GaloisUnits.FieldMap k Ω K Ψ) :
    (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).Additive :=
  smallEtaleInverseImage_additive.{u, w} (fieldOriginalPullback k Ω K Ψ e)

omit [IsSepClosure k Ω] [IsSepClosure K Ψ] in
theorem fieldNativeInverseImageShortExact (e : GaloisUnits.FieldMap k Ω K Ψ)
    (S : ShortComplex (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}))
    (hS : S.ShortExact) :
    (S.map (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))).ShortExact :=
  smallEtaleInverseImage_shortExact.{u, w} (fieldOriginalPullback k Ω K Ψ e) S hS

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- V1/V2 recorded dictionary mismatches at the same field/module functor aliases.
/-- The old original cochain restriction followed by its actual ξ coefficient map,
as one whole morphism of delta functors. -/
def fieldNativePullbackDeltaHom (e : GaloisUnits.FieldMap k Ω K Ψ) :
    CohomologicalDeltaFunctor.precompose (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
        (Functor.RightDerived.precompShortExact (fieldGeometricStalkGaloisFunctor.{u, w} k Ω))
        (fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω) ⟶
      CohomologicalDeltaFunctor.precompose
        (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
        (fieldNativeInverseImageShortExact.{u, w} k Ω K Ψ e)
        (CohomologicalDeltaFunctor.precompose (fieldGeometricStalkGaloisFunctor.{u, w} K Ψ)
          (Functor.RightDerived.precompShortExact (fieldGeometricStalkGaloisFunctor.{u, w} K Ψ))
          (fieldContinuousCohomologyDeltaFunctor.{u, w} K Ψ)) := by
  let φ := GaloisUnits.FieldMap.restrictContinuous e
  let T := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
  let T' := fieldGeometricStalkGaloisFunctor.{u, w} K Ψ
  let R := fieldModuleRestriction.{u, u, w} k Ω K Ψ φ
  letI : R.Additive := fieldModuleRestriction_additive.{u, u, w} k Ω K Ψ φ
  let L := smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)
  let hT := Functor.RightDerived.precompShortExact T
  let hT' := Functor.RightDerived.precompShortExact T'
  let hR := fieldModuleRestriction_shortExact.{u, u, w} k Ω K Ψ φ
  let hL := fieldNativeInverseImageShortExact.{u, w} k Ω K Ψ e
  let H := fieldContinuousCohomologyDeltaFunctor.{u, w} K Ψ
  let χ := fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e
  let g : CohomologicalDeltaFunctor.precompose T hT
      (fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω) ⟶
      CohomologicalDeltaFunctor.precompose T hT (CohomologicalDeltaFunctor.precompose R hR H) :=
    (CohomologicalDeltaFunctor.precomposeFunctor T hT).map
      (fieldOriginalRankRestrictionDeltaHom.{u, w} k Ω K Ψ φ)
  let a := CohomologicalDeltaFunctor.precomposeCompIso T R hT hR H
  let b := CohomologicalDeltaFunctor.precomposeCompIso L T' hL hT' H
  let c := CohomologicalDeltaFunctor.precomposeChangeHom (T ⋙ R) (L ⋙ T')
    (CohomologicalDeltaFunctor.precomposeCompShortExact T R hT hR)
    (CohomologicalDeltaFunctor.precomposeCompShortExact L T' hL hT') χ.hom H
  exact g ≫ a.hom ≫ c ≫ b.inv

/-- The native cohomology map in degree n obtained from the field change morphism
of delta functors. -/
def fieldNativePullback (e : GaloisUnits.FieldMap k Ω K Ψ) (n : ℕ) :
    fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙ fieldContinuousCohomologyFunctor.{u, w} k Ω n ⟶
      smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e) ⋙
        fieldGeometricStalkGaloisFunctor.{u, w} K Ψ ⋙ fieldContinuousCohomologyFunctor.{u, w} K Ψ n
          :=
  CohomologicalDeltaFunctor.Hom.app (fieldNativePullbackDeltaHom.{u, w} k Ω K Ψ e) n

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- V1/V2 recorded whnf failures for the same actual precomposition components.
theorem fieldNativePullback_app (e : GaloisUnits.FieldMap k Ω K Ψ) (n : ℕ)
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (fieldNativePullback.{u, w} k Ω K Ψ e n).app Q =
      (CohomologicalDeltaFunctor.Hom.app
        (fieldOriginalRankRestrictionDeltaHom.{u, w} k Ω K Ψ
          (GaloisUnits.FieldMap.restrictContinuous e)) n).app
            ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) ≫
        (fieldContinuousCohomologyFunctor.{u, w} K Ψ n).map
          ((fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.app Q) := by
  simp only [fieldNativePullback, fieldNativePullbackDeltaHom,
    CohomologicalDeltaFunctor.Hom.comp_app,
    CohomologicalDeltaFunctor.precomposeCompIso_hom_app,
    CohomologicalDeltaFunctor.precomposeChangeHom_app]
  rfl

/-- Transport the original native map through the SAME accepted field comparison. -/
def fieldNativeTransportedGammaDeltaHom (e : GaloisUnits.FieldMap k Ω K Ψ) :
    fieldOriginalGammaDeltaFunctor.{u, w} k ⟶
      fieldInverseImageGammaDeltaFunctor.{u, w} k Ω K Ψ e :=
  (fieldGammaContinuousDeltaIso.{u, w} k Ω).hom ≫
    fieldNativePullbackDeltaHom.{u, w} k Ω K Ψ e ≫
    (CohomologicalDeltaFunctor.precomposeFunctor
      (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
      (fieldNativeInverseImageShortExact.{u, w} k Ω K Ψ e)).map
      (fieldGammaContinuousDeltaIso.{u, w} K Ψ).inv

end AlgebraicGeometry.Scheme.DerivedSections

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω K Ψ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ] [IsSepClosure k Ω] [IsSepClosure K Ψ]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Typed actual original/wide model comparison, with no change to Γ or the native family.
theorem fieldOriginalRankRestrictionDeltaHom_zero
    (φ : InfiniteGalois.profiniteGalGrp K Ψ →ₜ* InfiniteGalois.profiniteGalGrp k Ω) :
    CohomologicalDeltaFunctor.Hom.app
        (fieldOriginalRankRestrictionDeltaHom.{u, w} k Ω K Ψ φ) 0 ≫
      Functor.whiskerLeft (fieldModuleRestriction.{u, u, w} k Ω K Ψ φ)
        (fieldContinuousCohomologyZeroIso.{u, w} K Ψ).hom =
    (fieldContinuousCohomologyZeroIso.{u, w} k Ω).hom ≫
      fieldInvariantRestriction.{u, u, w} k Ω K Ψ φ := by
  rw [fieldOriginalRankRestrictionDeltaHom_app]
  have htarget := rankIso_inv_zero (fieldSameRankContinuousIso.{u, w} K Ψ 0)
    (fieldContinuousCohomologyZeroIso.{u, w} K Ψ).hom
    (fieldContinuousCohomologyZeroIso.{u, max u w} K Ψ).hom
    (fieldSameRankContinuousIso_zero.{u, w} K Ψ)
  calc
    _ = (fieldSameRankContinuousIso.{u, w} k Ω 0).hom ≫
      fieldContinuousCohomologyRestriction.{u, u, w} k Ω K Ψ 0 φ ≫
      Functor.whiskerLeft (fieldModuleRestriction.{u, u, w} k Ω K Ψ φ)
        (fieldContinuousCohomologyZeroIso.{u, max u w} K Ψ).hom := by
      simpa only [Category.assoc, Functor.whiskerLeft_comp] using
        congrArg (fun a => (fieldSameRankContinuousIso.{u, w} k Ω 0).hom ≫
          fieldContinuousCohomologyRestriction.{u, u, w} k Ω K Ψ 0 φ ≫
          Functor.whiskerLeft (fieldModuleRestriction.{u, u, w} k Ω K Ψ φ) a) htarget
    _ = (fieldSameRankContinuousIso.{u, w} k Ω 0).hom ≫
      (fieldContinuousCohomologyZeroIso.{u, max u w} k Ω).hom ≫
      fieldInvariantRestriction.{u, u, w} k Ω K Ψ φ := by
      rw [fieldContinuousCohomologyRestriction_zero]
    _ = _ := by rw [← Category.assoc, fieldSameRankContinuousIso_zero]

end AlgebraicGeometry.Scheme.DerivedSections

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω K Ψ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ] [IsSepClosure k Ω] [IsSepClosure K Ψ]

/-- The SAME accepted Γ/native comparison retains the actual original invariant normalization. -/
theorem fieldGammaContinuousIso_zero
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω 0).hom.app Q ≫
      (fieldContinuousCohomologyZeroIso.{u, w} k Ω).hom.app
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) =
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u
      w}).rightDerivedZeroIsoSelf.hom.app Q ≫
      (fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom.app Q := by
  let T := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
  have h := rankIso_inv_zero (fieldContinuousDerivedInvariantsIso.{u, w} k Ω 0)
    (fieldContinuousCohomologyZeroIso.{u, w} k Ω).hom
    (fieldInvariantFunctor.{u, w} k Ω).rightDerivedZeroIsoSelf.hom
    (fieldContinuousDerivedInvariantsIso_zero.{u, w} k Ω)
  have hQ := congrArg (fun a => a.app (T.obj Q)) h
  simp only [NatTrans.comp_app] at hQ
  rw [fieldDerivedSectionsContinuousCohomologyIso, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Iso.symm_hom, Category.assoc, hQ]
  exact fieldDerivedSectionsInvariantsIso_zero.{u, w} k Ω Q

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The full unchanged field-native zero statement/proof hit whnf200000 in retained V2/V3.
-- This finite declaration scope keeps every original field, coefficient object and map.
-- The proved native map uses the fixed old-rank cochains and actual ξ coefficient arrow.
theorem fieldNativePullback_zero_invariants
    (e : GaloisUnits.FieldMap k Ω K Ψ)
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (fieldNativePullback.{u, w} k Ω K Ψ e 0).app Q ≫
      (fieldContinuousCohomologyZeroIso.{u, w} K Ψ).hom.app
        ((fieldGeometricStalkGaloisFunctor.{u, w} K Ψ).obj
          ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q)) =
    (fieldContinuousCohomologyZeroIso.{u, w} k Ω).hom.app
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) ≫
      (fieldInvariantRestriction.{u, u, w} k Ω K Ψ (GaloisUnits.FieldMap.restrictContinuous e)).app
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) ≫
      (fieldInvariantFunctor.{u, w} K Ψ).map
        ((fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.app Q) := by
  let φ : InfiniteGalois.profiniteGalGrp K Ψ →ₜ* InfiniteGalois.profiniteGalGrp k Ω :=
    GaloisUnits.FieldMap.restrictContinuous e
  let M := (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q
  let ξ := (fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.app Q
  have h := congrArg (fun a => a.app M)
    (fieldOriginalRankRestrictionDeltaHom_zero.{u, w} k Ω K Ψ φ)
  have h' := postcompose_natural_zero
    (fieldContinuousCohomologyFunctor.{u, w} K Ψ 0)
    (fieldInvariantFunctor.{u, w} K Ψ)
    (fieldContinuousCohomologyZeroIso.{u, w} K Ψ) ξ
    ((CohomologicalDeltaFunctor.Hom.app
      (fieldOriginalRankRestrictionDeltaHom.{u, w} k Ω K Ψ φ) 0).app M)
    ((fieldContinuousCohomologyZeroIso.{u, w} k Ω).hom.app M ≫
      (fieldInvariantRestriction.{u, u, w} k Ω K Ψ φ).app M) h
  exact (congrArg (fun a => a ≫ (fieldContinuousCohomologyZeroIso.{u, w} K Ψ).hom.app
      ((fieldGeometricStalkGaloisFunctor.{u, w} K Ψ).obj
        ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q)))
    (fieldNativePullback_app.{u, w} k Ω K Ψ e 0 Q)).trans h'

end AlgebraicGeometry.Scheme.DerivedSections

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω K Ψ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ] [IsSepClosure k Ω] [IsSepClosure K Ψ]

/-- The inverse component is the inverse of the same accepted all-degree comparison. -/
theorem fieldGammaContinuousDeltaIso_inv_app (q : ℕ) :
    CohomologicalDeltaFunctor.Hom.app (fieldGammaContinuousDeltaIso.{u, w} k Ω).inv q =
      (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q).inv := by
  apply (cancel_mono (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q).hom).mp
  have h := congrArg (fun a => CohomologicalDeltaFunctor.Hom.app a q)
    (fieldGammaContinuousDeltaIso.{u, w} k Ω).inv_hom_id
  change CohomologicalDeltaFunctor.Hom.app (fieldGammaContinuousDeltaIso.{u, w} k Ω).inv q ≫
    CohomologicalDeltaFunctor.Hom.app (fieldGammaContinuousDeltaIso.{u, w} k Ω).hom q = 𝟙 _ at h
  rw [fieldGammaContinuousDeltaIso_hom_app] at h
  exact h.trans (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q).inv_hom_id.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Evaluate only the existing delta-functor operations before instantiating the field components.
theorem fieldNativeTransportedGammaDeltaHom_app
    (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ) :
    CohomologicalDeltaFunctor.Hom.app
      (fieldNativeTransportedGammaDeltaHom.{u, w} k Ω K Ψ e) q =
    (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q).hom ≫
      fieldNativePullback.{u, w} k Ω K Ψ e q ≫
      Functor.whiskerLeft (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
        (fieldDerivedSectionsContinuousCohomologyIso.{u, w} K Ψ q).inv := by
  simp only [fieldNativeTransportedGammaDeltaHom, CohomologicalDeltaFunctor.Hom.comp_app,
    CohomologicalDeltaFunctor.delta_precompose_map_app,
    fieldGammaContinuousDeltaIso_hom_app, fieldGammaContinuousDeltaIso_inv_app]
  rfl

set_option linter.defProp false in
-- Actual typed restatements reached whnf200000/400000 in AgreementV1/V2.
-- Cache the complete generic proof with the same explicit original field objects; no premise is
-- added.
/-- The normalization proof for transported native pullback in degree zero,
using the fixed sections–invariants and cohomology comparisons. -/
def fieldNativeGammaZeroProof (e : GaloisUnits.FieldMap k Ω K Ψ)
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :=
  normalized_conjugate_map
    ((fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω 0).app Q)
    ((fieldDerivedSectionsContinuousCohomologyIso.{u, w} K Ψ 0).app
      ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q))
    ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u
      w}).rightDerivedZeroIsoSelf.app Q)
    ((Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf.app
      ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q))
    ((fieldGlobalSectionsInvariantsIso.{u, w} k Ω).app Q)
    ((fieldGlobalSectionsInvariantsIso.{u, w} K Ψ).app
      ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q))
    ((fieldContinuousCohomologyZeroIso.{u, w} k Ω).app
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q))
    ((fieldContinuousCohomologyZeroIso.{u, w} K Ψ).app
      ((fieldGeometricStalkGaloisFunctor.{u, w} K Ψ).obj
        ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q)))
    ((fieldPullbackGlobalSections.{u, w} k Ω K Ψ e).app Q)
    ((fieldNativePullback.{u, w} k Ω K Ψ e 0).app Q)
    ((fieldInvariantRestriction.{u, u, w} k Ω K Ψ (GaloisUnits.FieldMap.restrictContinuous e)).app
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) ≫
      (fieldInvariantFunctor.{u, w} K Ψ).map
        ((fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.app Q))
    (fieldGammaContinuousIso_zero.{u, w} k Ω Q)
    (fieldGammaContinuousIso_zero.{u, w} K Ψ
      ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q))
    (fieldNativePullback_zero_invariants.{u, w} k Ω K Ψ e Q)
    (congrArg (fun a => a.app Q)
      (fieldPullbackGlobalSections_invariants_naturality.{u, w} k Ω K Ψ e))

end AlgebraicGeometry.Scheme.DerivedSections

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω K Ψ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ] [IsSepClosure k Ω] [IsSepClosure K Ψ]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- ComponentsV1 caches the complete generic normalization proof on the same field objects.
theorem fieldNativeTransportedGammaDeltaHom_zero
    (e : GaloisUnits.FieldMap k Ω K Ψ) :
    CohomologicalDeltaFunctor.Hom.app
        (fieldNativeTransportedGammaDeltaHom.{u, w} k Ω K Ψ e) 0 ≫
      Functor.whiskerLeft (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
        (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u
          w}).rightDerivedZeroIsoSelf.hom =
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf.hom
      ≫
      fieldPullbackGlobalSections.{u, w} k Ω K Ψ e := by
  rw [fieldNativeTransportedGammaDeltaHom_app]
  apply NatTrans.ext
  funext Q
  exact fieldNativeGammaZeroProof.{u, w} k Ω K Ψ e Q

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Actual zero normalization and genuine source universality identify every degree.
theorem fieldNativeTransportedGammaDeltaHom_eq
    (e : GaloisUnits.FieldMap k Ω K Ψ) :
    fieldNativeTransportedGammaDeltaHom.{u, w} k Ω K Ψ e =
      fieldDerivedPullbackDeltaHom.{u, w} k Ω K Ψ e := by
  apply fieldDerivedPullback_unique.{u, w} k Ω K Ψ e
  apply (cancel_mono (Functor.isoWhiskerLeft
    (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
    (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u
      w}).rightDerivedZeroIsoSelf).hom).mp
  exact (fieldNativeTransportedGammaDeltaHom_zero.{u, w} k Ω K Ψ e).trans
    (fieldDerivedPullback_zero.{u, w} k Ω K Ψ e).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The same accepted comparison families and literal original native maps occur in every degree.
theorem fieldDerivedPullback_native_square
    (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ) :
    fieldDerivedPullback.{u, w} k Ω K Ψ e q ≫
      Functor.whiskerLeft (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
        (fieldDerivedSectionsContinuousCohomologyIso.{u, w} K Ψ q).hom =
    (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q).hom ≫
      fieldNativePullback.{u, w} k Ω K Ψ e q := by
  have h := congrArg (fun a => CohomologicalDeltaFunctor.Hom.app a q)
    (fieldNativeTransportedGammaDeltaHom_eq.{u, w} k Ω K Ψ e)
  rw [fieldNativeTransportedGammaDeltaHom_app] at h
  exact conjugate_map_square
    (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q)
    (Functor.isoWhiskerLeft
      (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
      (fieldDerivedSectionsContinuousCohomologyIso.{u, w} K Ψ q))
    (fieldNativePullback.{u, w} k Ω K Ψ e q)
    (fieldDerivedPullback.{u, w} k Ω K Ψ e q) h

end AlgebraicGeometry.Scheme.DerivedSections

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- Actual field identity gives the original identity scheme morphism. -/
theorem fieldOriginalPullback_id (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] :
    fieldOriginalPullback k Ω k Ω (GaloisUnits.FieldMap.id k Ω) = 𝟙 (Spec (.of k)) := by
  change Spec.map (𝟙 (CommRingCat.of k)) = 𝟙 (Spec (.of k))
  exact Spec.map_id _

/-- Actual compatible field squares give the original contravariant scheme composition. -/
theorem fieldOriginalPullback_comp
    (k Ω K Ψ L Φ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ] [Field L] [Field Φ]
    [Algebra k Ω] [Algebra K Ψ] [Algebra L Φ]
    (e₁ : GaloisUnits.FieldMap k Ω K Ψ) (e₂ : GaloisUnits.FieldMap K Ψ L Φ) :
    fieldOriginalPullback k Ω L Φ (GaloisUnits.FieldMap.comp e₂ e₁) =
      fieldOriginalPullback K Ψ L Φ e₂ ≫ fieldOriginalPullback k Ω K Ψ e₁ := by
  change Spec.map ((CommRingCat.ofHom e₁.base) ≫ (CommRingCat.ofHom e₂.base)) = _
  exact Spec.map_comp _ _

/-- Naming the original identity changes the same LF comparison only by actual
equality transport. -/
theorem smallEtaleDerivedGammaPullback_id_to (X : Scheme.{u}) (f : X ⟶ X)
    (hf : f = 𝟙 X) (q : ℕ) :
    smallEtaleDerivedGammaPullback.{u, w} f q ≫
      Functor.whiskerRight
        (smallEtaleInverseImageCongr.{u, w} hf ≪≫ smallEtaleInverseImageIdIso.{u, w} X).hom
        ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q) =
    𝟙 ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q) := by
  subst f
  simpa only [smallEtaleInverseImageCongr, eqToIso_refl, Iso.refl_trans] using
    smallEtaleDerivedGammaPullback_id.{u, w} X q

/-- Naming the genuine composite preserves the same every-degree canonical LF square. -/
theorem smallEtaleDerivedGammaPullback_comp_to
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) (q : ℕ) :
    smallEtaleDerivedGammaPullback.{u, w} g q ≫
      Functor.whiskerLeft (smallEtaleInverseImage.{u, w} g)
        (smallEtaleDerivedGammaPullback.{u, w} f q) ≫
      (Functor.associator (smallEtaleInverseImage.{u, w} g) (smallEtaleInverseImage.{u, w} f)
        ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q)).inv ≫
      Functor.whiskerRight (smallEtaleInverseImageCompTo.{u, w} f g fg hfg).hom
        ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q) =
    smallEtaleDerivedGammaPullback.{u, w} fg q := by
  subst fg
  simpa only [smallEtaleInverseImageCompTo_eq, smallEtaleInverseImageCongr, eqToIso_refl,
    Iso.trans_refl] using smallEtaleDerivedGammaPullback_comp.{u, w} f g q

variable (k Ω K Ψ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ]

/-- The field map is the SAME original unit/terminal Γ construction. -/
theorem fieldPullbackGlobalSections_eq_scheme (e : GaloisUnits.FieldMap k Ω K Ψ) :
    fieldPullbackGlobalSections.{u, w} k Ω K Ψ e =
      smallEtalePullbackGlobalSections.{u, w} (fieldOriginalPullback k Ω K Ψ e) := rfl

set_option backward.isDefEq.respectTransparency false in
-- Only actual common Γ objects and the proved same unit map are compared.
theorem fieldDerivedPullbackDeltaHom_eq_scheme (e : GaloisUnits.FieldMap k Ω K Ψ) :
    fieldDerivedPullbackDeltaHom.{u, w} k Ω K Ψ e =
      smallEtaleDerivedGammaPullbackDeltaHom.{u, w} (fieldOriginalPullback k Ω K Ψ e) := by
  unfold fieldDerivedPullbackDeltaHom smallEtaleDerivedGammaPullbackDeltaHom
  rw [fieldPullbackGlobalSections_eq_scheme]
  rfl

theorem fieldDerivedPullback_eq_scheme (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ) :
    fieldDerivedPullback.{u, w} k Ω K Ψ e q =
      smallEtaleDerivedGammaPullback.{u, w} (fieldOriginalPullback k Ω K Ψ e) q :=
  congrArg (fun a => CohomologicalDeltaFunctor.Hom.app a q)
    (fieldDerivedPullbackDeltaHom_eq_scheme.{u, w} k Ω K Ψ e)

/-- The actual identity comparison uses only the proved original field/Spec equality. -/
def fieldInverseImageIdentityIso :
    smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω k Ω (GaloisUnits.FieldMap.id k Ω)) ≅
      𝟭 (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :=
  smallEtaleInverseImageCongr.{u, w} (fieldOriginalPullback_id k Ω) ≪≫
    smallEtaleInverseImageIdIso.{u, w} (Spec (.of k))

/-- Every degree of the SAME original field pullback respects canonical identity. -/
theorem fieldDerivedPullback_id (q : ℕ) :
    fieldDerivedPullback.{u, w} k Ω k Ω (GaloisUnits.FieldMap.id k Ω) q ≫
      Functor.whiskerRight (fieldInverseImageIdentityIso.{u, w} k Ω).hom
        ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q) =
    𝟙 ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q) := by
  rw [fieldDerivedPullback_eq_scheme]
  exact smallEtaleDerivedGammaPullback_id_to.{u, w} (Spec (.of k))
    (fieldOriginalPullback k Ω k Ω (GaloisUnits.FieldMap.id k Ω)) (fieldOriginalPullback_id k Ω) q

variable (L Φ : Type u) [Field L] [Field Φ] [Algebra L Φ]

/-- The actual field composite uses the same canonical LF composition mate. -/
def fieldInverseImageCompositionIso
    (e₁ : GaloisUnits.FieldMap k Ω K Ψ) (e₂ : GaloisUnits.FieldMap K Ψ L Φ) :
    smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e₁) ⋙
      smallEtaleInverseImage.{u, w} (fieldOriginalPullback K Ψ L Φ e₂) ≅
    smallEtaleInverseImage.{u, w}
      (fieldOriginalPullback k Ω L Φ (GaloisUnits.FieldMap.comp e₂ e₁)) :=
  smallEtaleInverseImageCompTo.{u, w}
    (fieldOriginalPullback K Ψ L Φ e₂) (fieldOriginalPullback k Ω K Ψ e₁)
    (fieldOriginalPullback k Ω L Φ (GaloisUnits.FieldMap.comp e₂ e₁))
    (fieldOriginalPullback_comp k Ω K Ψ L Φ e₁ e₂)

/-- Every degree and every original sheaf obey the actual field composition square. -/
theorem fieldDerivedPullback_comp
    (e₁ : GaloisUnits.FieldMap k Ω K Ψ) (e₂ : GaloisUnits.FieldMap K Ψ L Φ) (q : ℕ) :
    fieldDerivedPullback.{u, w} k Ω K Ψ e₁ q ≫
      Functor.whiskerLeft (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e₁))
        (fieldDerivedPullback.{u, w} K Ψ L Φ e₂ q) ≫
      (Functor.associator
        (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e₁))
        (smallEtaleInverseImage.{u, w} (fieldOriginalPullback K Ψ L Φ e₂))
        ((Sheaf.Γ (Spec (.of L)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q)).inv ≫
      Functor.whiskerRight (fieldInverseImageCompositionIso.{u, w} k Ω K Ψ L Φ e₁ e₂).hom
        ((Sheaf.Γ (Spec (.of L)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q) =
    fieldDerivedPullback.{u, w} k Ω L Φ (GaloisUnits.FieldMap.comp e₂ e₁) q := by
  simp only [fieldDerivedPullback_eq_scheme]
  exact smallEtaleDerivedGammaPullback_comp_to.{u, w}
    (fieldOriginalPullback K Ψ L Φ e₂) (fieldOriginalPullback k Ω K Ψ e₁)
    (fieldOriginalPullback k Ω L Φ (GaloisUnits.FieldMap.comp e₂ e₁))
    (fieldOriginalPullback_comp k Ω K Ψ L Φ e₁ e₂) q

end AlgebraicGeometry.Scheme.DerivedSections

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- The SAME old-rank original native family respects canonical identity in every degree. -/
theorem fieldNativePullback_id (q : ℕ) :
    fieldNativePullback.{u, w} k Ω k Ω (GaloisUnits.FieldMap.id k Ω) q ≫
      Functor.whiskerRight (fieldInverseImageIdentityIso.{u, w} k Ω).hom
        (fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
          fieldContinuousCohomologyFunctor.{u, w} k Ω q) =
    𝟙 (fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
      fieldContinuousCohomologyFunctor.{u, w} k Ω q) :=
  comparison_identity (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q)
    (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω k Ω (GaloisUnits.FieldMap.id k Ω)))
    (fieldInverseImageIdentityIso.{u, w} k Ω)
    (fieldDerivedPullback.{u, w} k Ω k Ω (GaloisUnits.FieldMap.id k Ω) q)
    (fieldNativePullback.{u, w} k Ω k Ω (GaloisUnits.FieldMap.id k Ω) q)
    (fieldDerivedPullback_native_square.{u, w} k Ω k Ω (GaloisUnits.FieldMap.id k Ω) q)
    (fieldDerivedPullback_id.{u, w} k Ω q)

variable (K Ψ L Φ : Type u) [Field K] [Field Ψ] [Field L] [Field Φ]
variable [Algebra K Ψ] [Algebra L Φ] [IsSepClosure K Ψ] [IsSepClosure L Φ]

/-- The literal old-rank native pullbacks respect the SAME canonical field/LF composition. -/
theorem fieldNativePullback_comp
    (e₁ : GaloisUnits.FieldMap k Ω K Ψ) (e₂ : GaloisUnits.FieldMap K Ψ L Φ) (q : ℕ) :
    fieldNativePullback.{u, w} k Ω K Ψ e₁ q ≫
      Functor.whiskerLeft (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e₁))
        (fieldNativePullback.{u, w} K Ψ L Φ e₂ q) ≫
      (Functor.associator
        (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e₁))
        (smallEtaleInverseImage.{u, w} (fieldOriginalPullback K Ψ L Φ e₂))
        (fieldGeometricStalkGaloisFunctor.{u, w} L Φ ⋙
          fieldContinuousCohomologyFunctor.{u, w} L Φ q)).inv ≫
      Functor.whiskerRight (fieldInverseImageCompositionIso.{u, w} k Ω K Ψ L Φ e₁ e₂).hom
        (fieldGeometricStalkGaloisFunctor.{u, w} L Φ ⋙
          fieldContinuousCohomologyFunctor.{u, w} L Φ q) =
    fieldNativePullback.{u, w} k Ω L Φ (GaloisUnits.FieldMap.comp e₂ e₁) q :=
  comparison_composition
    (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q)
    (fieldDerivedSectionsContinuousCohomologyIso.{u, w} K Ψ q)
    (fieldDerivedSectionsContinuousCohomologyIso.{u, w} L Φ q)
    (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e₁))
    (smallEtaleInverseImage.{u, w} (fieldOriginalPullback K Ψ L Φ e₂))
    (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω L Φ (GaloisUnits.FieldMap.comp e₂
      e₁)))
    (fieldInverseImageCompositionIso.{u, w} k Ω K Ψ L Φ e₁ e₂)
    (fieldDerivedPullback.{u, w} k Ω K Ψ e₁ q)
    (fieldNativePullback.{u, w} k Ω K Ψ e₁ q)
    (fieldDerivedPullback.{u, w} K Ψ L Φ e₂ q)
    (fieldNativePullback.{u, w} K Ψ L Φ e₂ q)
    (fieldDerivedPullback.{u, w} k Ω L Φ (GaloisUnits.FieldMap.comp e₂ e₁) q)
    (fieldNativePullback.{u, w} k Ω L Φ (GaloisUnits.FieldMap.comp e₂ e₁) q)
    (fieldDerivedPullback_native_square.{u, w} k Ω K Ψ e₁ q)
    (fieldDerivedPullback_native_square.{u, w} K Ψ L Φ e₂ q)
    (fieldDerivedPullback_native_square.{u, w} k Ω L Φ (GaloisUnits.FieldMap.comp e₂ e₁) q)
    (fieldDerivedPullback_comp.{u, w} k Ω K Ψ L Φ e₁ e₂ q)

end AlgebraicGeometry.Scheme.DerivedSections

end


section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω K Ψ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ] [IsSepClosure k Ω] [IsSepClosure K Ψ]

/-- The SAME accepted Γ/native family realized on each actual original Γ resolution. -/
def fieldGammaNativeResolutionIso (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :
    (((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex).homology q ≅
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
      fieldContinuousCohomologyFunctor.{u, w} k Ω q).obj Q :=
  (I.isoRightDerivedObj
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) q).symm ≪≫
    (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q).app Q

/-- Realize the actual derived field map in the two chosen actual Γ resolutions. -/
def fieldDerivedPullbackResolutionMap (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q)
    (J : InjectiveResolution
      ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q)) :
    (((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex).homology q ⟶
    (((Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex).homology q :=
  (I.isoRightDerivedObj
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) q).inv ≫
    (fieldDerivedPullback.{u, w} k Ω K Ψ e q).app Q ≫
    (J.isoRightDerivedObj
      (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}) q).hom

set_option linter.defProp false in
-- V2 hit whnf200000 while restating the unchanged full field resolution square.
/-- The proof comparing field pullback on the chosen injective resolutions
with the native cohomology map. -/
def fieldResolutionNativeSquareProof
    (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q)
    (J : InjectiveResolution
      ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q)) :=
  resolution_realization_square
    (I.isoRightDerivedObj (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) q)
    (J.isoRightDerivedObj (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}) q)
    ((fieldDerivedPullback.{u, w} k Ω K Ψ e q).app Q)
    ((fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q).app Q)
    ((fieldDerivedSectionsContinuousCohomologyIso.{u, w} K Ψ q).app
      ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q))
    ((fieldNativePullback.{u, w} k Ω K Ψ e q).app Q) (congrArg (fun a => a.app Q)
      (fieldDerivedPullback_native_square.{u, w} k Ω K Ψ e q))


/-- EVERY pair of original resolution choices realizes the SAME literal native field map. -/
theorem fieldDerivedPullbackResolutionMap_native_square
    (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q)
    (J : InjectiveResolution
      ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q)) :
    fieldDerivedPullbackResolutionMap.{u, w} k Ω K Ψ e q I J ≫
      (fieldGammaNativeResolutionIso.{u, w} K Ψ q J).hom =
    (fieldGammaNativeResolutionIso.{u, w} k Ω q I).hom ≫
      (fieldNativePullback.{u, w} k Ω K Ψ e q).app Q := by
  exact fieldResolutionNativeSquareProof.{u, w} k Ω K Ψ e q I J

omit [IsSepClosure k Ω] [IsSepClosure K Ψ] in
/-- Changing either actual resolution uses the canonical stock comparison, not supplied isos. -/
theorem fieldDerivedPullbackResolutionMap_choice
    (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I I' : InjectiveResolution Q)
    (J J' : InjectiveResolution
      ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q)) :
    (InjectiveResolution.cohomologyComparisonIso I I'
      (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) q).hom ≫
      fieldDerivedPullbackResolutionMap.{u, w} k Ω K Ψ e q I' J' =
    fieldDerivedPullbackResolutionMap.{u, w} k Ω K Ψ e q I J ≫
      (InjectiveResolution.cohomologyComparisonIso J J'
        (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}) q).hom := by
  exact resolution_realization_choice
    (I.isoRightDerivedObj (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) q)
    (I'.isoRightDerivedObj (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) q)
    (J.isoRightDerivedObj (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}) q)
    (J'.isoRightDerivedObj (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}) q)
    ((fieldDerivedPullback.{u, w} k Ω K Ψ e q).app Q)

/-- Every original smaller coefficient enters the full field comparison through exactly ONE L. -/
theorem original_field_derived_pullback_native_square
    (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ)
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}) :
    (fieldDerivedPullback.{u, w} k Ω K Ψ e q).app
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F) ≫
      (fieldDerivedSectionsContinuousCohomologyIso.{u, w} K Ψ q).hom.app
        ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F)) =
    (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q).hom.app
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F) ≫
      (fieldNativePullback.{u, w} k Ω K Ψ e q).app
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F) :=
  congrArg (fun a => a.app ((liftCoefficients.{u, w} (Spec (.of k))).obj F))
    (fieldDerivedPullback_native_square.{u, w} k Ω K Ψ e q)

end AlgebraicGeometry.Scheme.DerivedSections

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω K Ψ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ]

set_option linter.defProp false in
-- Bind the SAME actual source/target augmentation equations and existing Γ naturality first.
/-- The naturality proof for field pullback realized on resolutions, with prescribed
augmented comparison maps over a sheaf morphism. -/
def fieldResolutionCoefficientNaturalityProof
    (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ)
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}} (f : Q ⟶ Q')
    (I : InjectiveResolution Q) (I' : InjectiveResolution Q')
    (J : InjectiveResolution ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj
      Q))
    (J' : InjectiveResolution ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ
      e)).obj Q'))
    (φ : I.cocomplex ⟶ I'.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ I'.ι.f 0)
    (ψ : J.cocomplex ⟶ J'.cocomplex)
    (hψ : J.ι.f 0 ≫ ψ.f 0 =
      (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).map f ≫ J'.ι.f 0) :=
  resolution_realization_naturality
    (I.isoRightDerivedObj (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) q)
    (I'.isoRightDerivedObj (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) q)
    (J.isoRightDerivedObj (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}) q)
    (J'.isoRightDerivedObj (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}) q)
    (((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q).map f)
    (((Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q).map
      ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).map f))
    (HomologicalComplex.homologyMap
      (((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).mapHomologicalComplex
        (ComplexShape.up ℕ)).map φ) q)
    (HomologicalComplex.homologyMap
      (((Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}).mapHomologicalComplex
        (ComplexShape.up ℕ)).map ψ) q)
    ((fieldDerivedPullback.{u, w} k Ω K Ψ e q).app Q)
    ((fieldDerivedPullback.{u, w} k Ω K Ψ e q).app Q')
    (InjectiveResolution.isoRightDerivedObj_hom_naturality f I I' φ hφ
      (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) q)
    (InjectiveResolution.isoRightDerivedObj_hom_naturality
      ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).map f) J J' ψ hψ
      (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}) q)
    (fieldDerivedPullback_naturality.{u, w} k Ω K Ψ e q f)

/-- Every ACTUAL augmented source and target resolution map respects the SAME field map. -/
theorem fieldDerivedPullbackResolutionMap_naturality
    (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ)
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}} (f : Q ⟶ Q')
    (I : InjectiveResolution Q) (I' : InjectiveResolution Q')
    (J : InjectiveResolution ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj
      Q))
    (J' : InjectiveResolution ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ
      e)).obj Q'))
    (φ : I.cocomplex ⟶ I'.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ I'.ι.f 0)
    (ψ : J.cocomplex ⟶ J'.cocomplex)
    (hψ : J.ι.f 0 ≫ ψ.f 0 =
      (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).map f ≫ J'.ι.f 0) :
    HomologicalComplex.homologyMap
      (((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).mapHomologicalComplex
        (ComplexShape.up ℕ)).map φ) q ≫
      fieldDerivedPullbackResolutionMap.{u, w} k Ω K Ψ e q I' J' =
    fieldDerivedPullbackResolutionMap.{u, w} k Ω K Ψ e q I J ≫
      HomologicalComplex.homologyMap
        (((Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}).mapHomologicalComplex
          (ComplexShape.up ℕ)).map ψ) q :=
  fieldResolutionCoefficientNaturalityProof.{u, w} k Ω K Ψ e q f I I' J J' φ hφ ψ hψ

end AlgebraicGeometry.Scheme.DerivedSections

end


section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite

open CategoryTheory.CohomologicalDeltaFunctor
namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω K Ψ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ] [IsSepClosure k Ω] [IsSepClosure K Ψ]

/-- EVERY actual class uses the OLD original group cochain homology map and SAME ξ arrow. -/
theorem fieldNativePullback_original_map (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ)
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (fieldNativePullback.{u, w} k Ω K Ψ e q).app Q =
      ContinuousCohomology.discreteCoefficientForget.{max u w}.map
        (HomologicalComplex.homologyMap
          (fieldOriginalRankRestrictionCochainMap.{u, w} k Ω K Ψ
            (GaloisUnits.FieldMap.restrictContinuous e)
            ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)) q) ≫
      (fieldContinuousCohomologyFunctor.{u, w} K Ψ q).map
        ((fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.app Q) :=
  (fieldNativePullback_app.{u, w} k Ω K Ψ e q Q).trans
    (congrArg (fun a => a ≫ (fieldContinuousCohomologyFunctor.{u, w} K Ψ q).map
      ((fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.app Q))
      (fieldOriginalRankRestrictionDeltaHom_original_map.{u, w} k Ω K Ψ
        (GaloisUnits.FieldMap.restrictContinuous e) q
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)))

/-- Source and target are extracted from the SAME already constructed actual delta morphism. -/
def fieldNativeSourceDeltaSystem (e : GaloisUnits.FieldMap k Ω K Ψ) :=
  (Arrow.mk (fieldNativePullbackDeltaHom.{u, w} k Ω K Ψ e)).left

/-- The target delta functor of the constructed native field pullback morphism. -/
def fieldNativeTargetDeltaSystem (e : GaloisUnits.FieldMap k Ω K Ψ) :=
  (Arrow.mk (fieldNativePullbackDeltaHom.{u, w} k Ω K Ψ e)).right

-- V1-V3 retained actual200000-heartbeat failures matching the same original connector systems.
/-- The SAME actual native field map respects both actual connector systems in every degree. -/
theorem fieldNativePullback_connecting (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ)
    (S : ShortComplex.ShortExactSequences
      (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})) :
    ((fieldNativeSourceDeltaSystem.{u, w} k Ω K Ψ e).connecting q).app S ≫
      (fieldNativePullback.{u, w} k Ω K Ψ e (q + 1)).app S.obj.X₁ =
    (fieldNativePullback.{u, w} k Ω K Ψ e q).app S.obj.X₃ ≫
      ((fieldNativeTargetDeltaSystem.{u, w} k Ω K Ψ e).connecting q).app S :=
  DeltaFunctor.System.comm (fieldNativePullbackDeltaHom.{u, w} k Ω K Ψ e).hom q S

/-- EVERY original smaller-coefficient arrow uses the SAME single lifted input in every degree. -/
theorem original_field_native_pullback_naturality
    (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ)
    {F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}} (f : F ⟶ F') :
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
      fieldContinuousCohomologyFunctor.{u, w} k Ω q).map
        ((liftCoefficients.{u, w} (Spec (.of k))).map f) ≫
      (fieldNativePullback.{u, w} k Ω K Ψ e q).app
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F') =
    (fieldNativePullback.{u, w} k Ω K Ψ e q).app
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F) ≫
      (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e) ⋙
        fieldGeometricStalkGaloisFunctor.{u, w} K Ψ ⋙
          fieldContinuousCohomologyFunctor.{u, w} K Ψ q).map
        ((liftCoefficients.{u, w} (Spec (.of k))).map f) :=
  (fieldNativePullback.{u, w} k Ω K Ψ e q).naturality
    ((liftCoefficients.{u, w} (Spec (.of k))).map f)

end AlgebraicGeometry.Scheme.DerivedSections

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω K Ψ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ] [IsSepClosure k Ω] [IsSepClosure K Ψ]

/-- The extracted source is exactly the existing old-rank original native system. -/
theorem fieldNativeSourceDeltaSystem_eq (e : GaloisUnits.FieldMap k Ω K Ψ) :
    fieldNativeSourceDeltaSystem.{u, w} k Ω K Ψ e =
      CohomologicalDeltaFunctor.precompose (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
        (Functor.RightDerived.precompShortExact (fieldGeometricStalkGaloisFunctor.{u, w} k Ω))
        (fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω) := rfl

local instance nativeSystemIdentification_inverseImage_additive
    (e : GaloisUnits.FieldMap k Ω K Ψ) :
    (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).Additive :=
  smallEtaleInverseImage_additive.{u, w} (fieldOriginalPullback k Ω K Ψ e)

/-- The extracted target is exactly actual LF and original T/native precomposition. -/
theorem fieldNativeTargetDeltaSystem_eq (e : GaloisUnits.FieldMap k Ω K Ψ) :
    fieldNativeTargetDeltaSystem.{u, w} k Ω K Ψ e =
      CohomologicalDeltaFunctor.precompose
        (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
        (fieldNativeInverseImageShortExact.{u, w} k Ω K Ψ e)
        (CohomologicalDeltaFunctor.precompose (fieldGeometricStalkGaloisFunctor.{u, w} K Ψ)
          (Functor.RightDerived.precompShortExact (fieldGeometricStalkGaloisFunctor.{u, w} K Ψ))
          (fieldContinuousCohomologyDeltaFunctor.{u, w} K Ψ)) := rfl

/-- Original source connector identification retains its dependent original degree objects. -/
theorem fieldNativeSourceConnecting_identification (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ)
    (S : ShortComplex.ShortExactSequences
      (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})) :
    HEq ((fieldNativeSourceDeltaSystem.{u, w} k Ω K Ψ e).connecting q |>.app S)
      ((CohomologicalDeltaFunctor.precompose (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
        (Functor.RightDerived.precompShortExact (fieldGeometricStalkGaloisFunctor.{u, w} k Ω))
        (fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω)).connecting q |>.app S) :=
  CohomologicalDeltaFunctor.equal_system_connecting
    (fieldNativeSourceDeltaSystem_eq.{u, w} k Ω K Ψ e) q S

/-- Original target connector identification uses the same actual LF-then-T source sequence. -/
theorem fieldNativeTargetConnecting_identification (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ)
    (S : ShortComplex.ShortExactSequences
      (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})) :
    HEq ((fieldNativeTargetDeltaSystem.{u, w} k Ω K Ψ e).connecting q |>.app S)
      ((CohomologicalDeltaFunctor.precompose
        (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
        (fieldNativeInverseImageShortExact.{u, w} k Ω K Ψ e)
        (CohomologicalDeltaFunctor.precompose (fieldGeometricStalkGaloisFunctor.{u, w} K Ψ)
          (Functor.RightDerived.precompShortExact (fieldGeometricStalkGaloisFunctor.{u, w} K Ψ))
          (fieldContinuousCohomologyDeltaFunctor.{u, w} K Ψ))).connecting q |>.app S) :=
  CohomologicalDeltaFunctor.equal_system_connecting
    (fieldNativeTargetDeltaSystem_eq.{u, w} k Ω K Ψ e) q S

/-- Source degree functors are the SAME original old-rank native functions. -/
theorem fieldNativeSourceDeltaSystem_T (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ) :
    (fieldNativeSourceDeltaSystem.{u, w} k Ω K Ψ e).T q =
      fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
        fieldContinuousCohomologyFunctor.{u, w} k Ω q := rfl

/-- Target degree functors use only actual LF and SAME original target native functions. -/
theorem fieldNativeTargetDeltaSystem_T (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ) :
    (fieldNativeTargetDeltaSystem.{u, w} k Ω K Ψ e).T q =
      smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e) ⋙
        fieldGeometricStalkGaloisFunctor.{u, w} K Ψ ⋙
          fieldContinuousCohomologyFunctor.{u, w} K Ψ q := rfl

/-- The old native field connector is literally the original coefficient boundary, not a new
  system. -/
theorem fieldOldNativeDelta_connector (q : ℕ)
    (S : ShortComplex.ShortExactSequences (FieldCohomologyModule.{u, w} k Ω)) :
    ((fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω).connecting q).app S =
      ContinuousCohomology.discreteCoefficientConnecting.{u, w}
        (G := InfiniteGalois.profiniteGalGrp k Ω) S.obj
        (fieldShortExact_discreteCoefficientExact.{u, w} k Ω S.obj S.property) q := rfl

end AlgebraicGeometry.Scheme.DerivedSections

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- The actual old native resolution comparison equals the generic actual-homology family. -/
theorem fieldNativeActualResolutionFamily (q : ℕ) (M : FieldCohomologyModule.{u, w} k Ω) :
    (fun R : InjectiveResolution M => fieldContinuousDerivedInvariantsResolutionIso.{u, w} k Ω q R)
      =
      (fun R : InjectiveResolution M => InjectiveResolution.actualHomologyResolutionIso
        (fieldInvariantFunctor.{u, w} k Ω) q R
        ((fieldContinuousDerivedInvariantsIso.{u, w} k Ω q).app M)) := rfl

/-- The canonical presentation comparison is computed from the actual original mapped resolution. -/
def fieldMappedNativePresentationIso (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :=
  InjectiveResolution.homologyResolutionPresentationIso (fieldInvariantFunctor.{u, w} k Ω) q
    (fieldMappedInjectiveResolution.{u, w} k Ω I)
    ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapInjectiveResolution I) rfl

set_option linter.defProp false in
/-- The proof relating the native comparison for a mapped injective resolution
to its canonical homology presentation. -/
def fieldMappedNativePresentationProof (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :=
  InjectiveResolution.actualHomologyResolutionIso_presentation
    (fieldInvariantFunctor.{u, w} k Ω) q
    (fieldMappedInjectiveResolution.{u, w} k Ω I)
    ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapInjectiveResolution I) rfl
    ((fieldContinuousDerivedInvariantsIso.{u, w} k Ω q).app
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q))

/-- The right factor is the SAME old resolution comparison followed by constructed canonical p. -/
def fieldMappedNativeRightIso (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :=
  fieldContinuousDerivedInvariantsResolutionIso.{u, w} k Ω q
    (fieldMappedInjectiveResolution.{u, w} k Ω I) ≪≫ fieldMappedNativePresentationIso.{u, w} k Ω q I

/-- The actual generic right factor uses the same native comparison and mapped-T resolution. -/
def fieldMappedNativeRawRightIso (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :=
  (fieldContinuousDerivedInvariantsIso.{u, w} k Ω q).app
    ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) ≪≫
    ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapInjectiveResolution I).isoRightDerivedObj
      (fieldInvariantFunctor.{u, w} k Ω) q

/-- Canonical p transports the SAME old native right factor to the cut3 homology presentation. -/
theorem fieldMappedNativeRightIso_presentation (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :
    fieldMappedNativeRightIso.{u, w} k Ω q I =
      fieldMappedNativeRawRightIso.{u, w} k Ω q I := by
  have h := congrFun (fieldNativeActualResolutionFamily.{u, w} k Ω q
    ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q))
      (fieldMappedInjectiveResolution.{u, w} k Ω I)
  exact (congrArg (fun b => b ≪≫ fieldMappedNativePresentationIso.{u, w} k Ω q I) h).trans
    (fieldMappedNativePresentationProof.{u, w} k Ω q I)

end AlgebraicGeometry.Scheme.DerivedSections

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- The SAME fixed Γ/native comparison in its generic precomposition presentation. -/
def fieldMappedNativeRawGammaIso (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :=
  (I.isoRightDerivedObj (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) q).symm
    ≪≫
    ((Functor.rightDerivedPrecompIsoOfIso (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
      (fieldInvariantFunctor.{u, w} k Ω) (fieldGlobalSectionsInvariantsIso.{u, w} k Ω) q).app Q ≪≫
      ((fieldContinuousDerivedInvariantsIso.{u, w} k Ω q).app
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)).symm)

/-- The same mapped-T cut3 homology comparison, named before dependent typing. -/
def fieldMappedNativeRawLeftIso (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :=
  Functor.rightDerivedPrecompHomologyIsoOfIso
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω) (fieldInvariantFunctor.{u, w} k Ω)
    (fieldGlobalSectionsInvariantsIso.{u, w} k Ω) q I

/-- Actual source-wrapper identity, from the generic NatIso app/whisker law. -/
theorem fieldMappedNativeGammaIso_eq (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :
    fieldGammaNativeResolutionIso.{u, w} k Ω q I = fieldMappedNativeRawGammaIso.{u, w} k Ω q I :=
  resolution_natIso_app (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
    (fieldDerivedSectionsInvariantsIso.{u, w} k Ω q)
    (fieldContinuousDerivedInvariantsIso.{u, w} k Ω q) Q
    (I.isoRightDerivedObj (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) q)

/-- Actual left-wrapper identity, with no change of resolution or map. -/
theorem fieldMappedNativeLeftIso_eq (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :
    fieldDerivedSectionsInvariantsResolutionIso.{u, w} k Ω q I =
      fieldMappedNativeRawLeftIso.{u, w} k Ω q I := rfl

set_option linter.defProp false in
-- The complete actual generic formula is an iso equality, avoiding repeated hom-codomain inference.
/-- The isomorphism equality expressing the native resolution comparison through
the fixed stalk functor and invariants comparison. -/
def fieldMappedNativeRawIsoProof (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :=
  Functor.precomp_native_resolution_iso
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω) (fieldInvariantFunctor.{u, w} k Ω)
    (fieldGlobalSectionsInvariantsIso.{u, w} k Ω) q I
    ((fieldContinuousDerivedInvariantsIso.{u, w} k Ω q).app
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q))

/-- The same original Γ/native resolution iso is cut3 followed by old-C6 inverse and canonical p. -/
theorem fieldGammaNativeResolutionIso_mapped_T_iso (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :
    fieldGammaNativeResolutionIso.{u, w} k Ω q I =
      fieldDerivedSectionsInvariantsResolutionIso.{u, w} k Ω q I ≪≫
        (fieldMappedNativeRightIso.{u, w} k Ω q I).symm := by
  have h := fieldMappedNativeRawIsoProof.{u, w} k Ω q I
  change fieldMappedNativeRawGammaIso.{u, w} k Ω q I =
    fieldMappedNativeRawLeftIso.{u, w} k Ω q I ≪≫
      (fieldMappedNativeRawRightIso.{u, w} k Ω q I).symm at h
  exact (fieldMappedNativeGammaIso_eq.{u, w} k Ω q I).trans
    (h.trans (inverse_comp_iso_eq
      (fieldMappedNativeRawLeftIso.{u, w} k Ω q I)
      (fieldDerivedSectionsInvariantsResolutionIso.{u, w} k Ω q I)
      (fieldMappedNativeRawRightIso.{u, w} k Ω q I)
      (fieldMappedNativeRightIso.{u, w} k Ω q I)
      (fieldMappedNativeLeftIso_eq.{u, w} k Ω q I).symm
      (fieldMappedNativeRightIso_presentation.{u, w} k Ω q I).symm))

/-- The fully identified canonical mapped-T homology formula, in every original degree. -/
theorem fieldGammaNativeResolutionIso_mapped_T (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :
    (fieldGammaNativeResolutionIso.{u, w} k Ω q I).hom =
      (fieldDerivedSectionsInvariantsResolutionIso.{u, w} k Ω q I).hom ≫
        (fieldMappedNativeRightIso.{u, w} k Ω q I).inv :=
  congrArg Iso.hom (fieldGammaNativeResolutionIso_mapped_T_iso.{u, w} k Ω q I)

end AlgebraicGeometry.Scheme.DerivedSections

end

section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.DerivedSections

variable (k Ω K Ψ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ]

local instance fieldOriginalConnecting_inverseImage_additive
    (e : GaloisUnits.FieldMap k Ω K Ψ) :
    (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).Additive :=
  smallEtaleInverseImage_additive.{u, w} (fieldOriginalPullback k Ω K Ψ e)

/-- The same actual field pullback respects the original transported étale
Yoneda boundary on every genuine common sequence and in every degree. -/
theorem fieldDerivedPullback_etale_connecting
    (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ)
    (S : ShortComplex (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}))
    (hS : S.ShortExact) :
    AddCommGrpCat.ofHom (CanonicalLongExactSequence.derivedBoundary.{u, w} hS q) ≫
        (fieldDerivedPullback.{u, w} k Ω K Ψ e (q + 1)).app S.X₁ =
      (fieldDerivedPullback.{u, w} k Ω K Ψ e q).app S.X₃ ≫
        AddCommGrpCat.ofHom
          (CanonicalLongExactSequence.derivedBoundary.{u, w}
            (smallEtaleInverseImage_shortExact.{u, w}
              (fieldOriginalPullback k Ω K Ψ e) S hS) q) := by
  let L := smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)
  let hL := smallEtaleInverseImage_shortExact.{u, w}
    (fieldOriginalPullback k Ω K Ψ e) S hS
  exact connector_equality_transport
    (AddCommGrpCat.ofHom (CanonicalLongExactSequence.derivedBoundary.{u, w} hS q))
    ((Functor.rightDerivedConnecting (OriginalGammaBridge.Γ.{u, w} (Spec (.of k)))
      q).app ⟨S, hS⟩)
    (AddCommGrpCat.ofHom (CanonicalLongExactSequence.derivedBoundary.{u, w} hL q))
    ((Functor.rightDerivedConnecting (OriginalGammaBridge.Γ.{u, w} (Spec (.of K)))
      q).app ⟨S.map L, hL⟩)
    ((fieldDerivedPullback.{u, w} k Ω K Ψ e (q + 1)).app S.X₁)
    ((fieldDerivedPullback.{u, w} k Ω K Ψ e q).app S.X₃)
    (OriginalGammaBridge.derivedBoundary_eq_canonicalConnecting.{u, w}
      (Spec (.of k)) S hS q)
    (OriginalGammaBridge.derivedBoundary_eq_canonicalConnecting.{u, w}
      (Spec (.of K)) (S.map L) hL q)
    (fieldDerivedPullback_connecting.{u, w} k Ω K Ψ e q ⟨S, hS⟩)

/-- Every original smaller-coefficient local sequence is lifted exactly once;
the source and target boundaries are those of this same actual lifted sequence. -/
theorem original_field_derived_pullback_etale_connecting
    (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ)
    {F' F F'' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}}
    {a : F' ⟶ F} {b : F ⟶ F''} (h : originalSmallEtaleLocalShortExact a b) :
    let S := coefficientLiftLocalShortComplex h
    let hS := coefficientLift_shortExact h
    let hL := smallEtaleInverseImage_shortExact.{u, w}
      (fieldOriginalPullback k Ω K Ψ e) S hS
    AddCommGrpCat.ofHom (CanonicalLongExactSequence.derivedBoundary.{u, w} hS q) ≫
        (fieldDerivedPullback.{u, w} k Ω K Ψ e (q + 1)).app S.X₁ =
      (fieldDerivedPullback.{u, w} k Ω K Ψ e q).app S.X₃ ≫
        AddCommGrpCat.ofHom (CanonicalLongExactSequence.derivedBoundary.{u, w} hL q) :=
  fieldDerivedPullback_etale_connecting.{u, w} k Ω K Ψ e q
    (coefficientLiftLocalShortComplex h) (coefficientLift_shortExact h)

end AlgebraicGeometry.Scheme.DerivedSections

end

section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω K Ψ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ] [IsSepClosure k Ω] [IsSepClosure K Ψ]

local instance fullFieldNaturality_inverseImage_additive (e : GaloisUnits.FieldMap k Ω K Ψ) :
    (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).Additive :=
  smallEtaleInverseImage_additive.{u, w} (fieldOriginalPullback k Ω K Ψ e)

/-- The same actual field/site/module comparison, on every original object,
map, degree and connecting family. Coefficients enter through ONE actual lift.
All equations below are literal existing equations; no comparison, universality,
injective-preservation or desired-square certificate is an input. -/
structure FieldSiteModuleCohomologyNaturalityLaws (e : GaloisUnits.FieldMap k Ω K Ψ) : Prop where
  point_fst : ∀ (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U),
      (fieldChangeOriginalPoint k Ω K Ψ e U z).left ≫
          pullback.fst U.hom (fieldOriginalPullback k Ω K Ψ e) =
        fieldChangeSpec k Ω K Ψ e ≫ z.left

  point_snd : ∀ (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U),
      (fieldChangeOriginalPoint k Ω K Ψ e U z).left ≫
          pullback.snd U.hom (fieldOriginalPullback k Ω K Ψ e) = Spec.algebraMap K Ψ

  original_germ : ∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U),
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
          U (ULift.up z) Q.obj ≫ (fieldChangeUnderlyingStalkIso.{u, w} k Ω K Ψ e).hom.app Q =
        ((smallEtaleInverseImageAdjunction.{u, w} (fieldOriginalPullback k Ω K Ψ e)).unit.app
          Q).hom.app
            (op U) ≫
          (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap K Ψ)).toPresheafFiber
            ((smallEtaleBaseChange (fieldOriginalPullback k Ω K Ψ e)).obj U)
            (ULift.up (fieldChangeOriginalPoint k Ω K Ψ e U z))
            ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q).obj

  left_action : ∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (h : Gal(Ψ/K)) (m : fieldGeometricStalkCarrier.{u, w} k Ω Q),
      (fieldChangeUnderlyingStalkIso.{u, w} k Ω K Ψ e).hom.app Q
          ((GaloisUnits.FieldMap.restrictHom e h) • m) =
        h • (show fieldGeometricStalkCarrier.{u, w} K Ψ
            ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q) from
          (fieldChangeUnderlyingStalkIso.{u, w} k Ω K Ψ e).hom.app Q m)

  same_underlying_stalk : ∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}),
      (DiscreteAbelianAction.forget Gal(Ψ/K)).map
          ((fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.app Q) =
        (fieldChangeUnderlyingStalkIso.{u, w} k Ω K Ψ e).hom.app Q

  terminal_sections : ∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}),
      (fieldPullbackGlobalSections.{u, w} k Ω K Ψ e).app Q ≫
          (fieldGammaSectionsIso.{u, w} K).hom.app
            ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q) =
        (fieldGammaSectionsIso.{u, w} k).hom.app Q ≫
          ((smallEtaleInverseImageAdjunction.{u, w}
            (fieldOriginalPullback k Ω K Ψ e)).unit.app Q).hom.app (op (fieldIdentityEtale k)) ≫
          (((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q).obj.map
            (fieldBaseChangeTerminalIso k Ω K Ψ e).inv.op)

  zero_invariants : fieldPullbackGlobalSections.{u, w} k Ω K Ψ e ≫
          Functor.whiskerLeft (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
            (fieldGlobalSectionsInvariantsIso.{u, w} K Ψ).hom =
        (fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom ≫
          Functor.whiskerLeft (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
            (fieldInvariantRestriction.{u, u, w} k Ω K Ψ
              (GaloisUnits.FieldMap.restrictContinuous e)) ≫
          Functor.whiskerRight (fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom
            (fieldInvariantFunctor.{u, w} K Ψ)

  single_lift_germ : (∀ (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
      (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
      (c : F.obj.obj (op U)),
      let Q := (liftCoefficients.{u, w} (Spec (.of k))).obj F
      (fieldChangeUnderlyingStalkIso.{u, w} k Ω K Ψ e).hom.app Q
          ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
            U (ULift.up z) Q.obj (ULift.up c)) =
        (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap K Ψ)).toPresheafFiber
          ((smallEtaleBaseChange (fieldOriginalPullback k Ω K Ψ e)).obj U)
          (ULift.up (fieldChangeOriginalPoint k Ω K Ψ e U z))
          ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q).obj
          (((smallEtaleInverseImageAdjunction.{u, w}
            (fieldOriginalPullback k Ω K Ψ e)).unit.app Q).hom.app (op U) (ULift.up c)))

  single_lift_stalk_map : ∀ {F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}} (τ :
    F ⟶ F'),
      (fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
          GaloisUnits.restrictModules (GaloisUnits.FieldMap.restrictContinuous e)).map
            ((liftCoefficients.{u, w} (Spec (.of k))).map τ) ≫
          (fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.app
            ((liftCoefficients.{u, w} (Spec (.of k))).obj F') =
        (fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.app
            ((liftCoefficients.{u, w} (Spec (.of k))).obj F) ≫
          (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e) ⋙
            fieldGeometricStalkGaloisFunctor.{u, w} K Ψ).map
              ((liftCoefficients.{u, w} (Spec (.of k))).map τ)

  gamma_naturality : ∀ (n : ℕ)
      {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}} (τ : Q ⟶ Q'),
      ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived n).map τ ≫
          (fieldDerivedPullback.{u, w} k Ω K Ψ e n).app Q' =
        (fieldDerivedPullback.{u, w} k Ω K Ψ e n).app Q ≫
          ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e) ⋙
            (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived n).map
              τ)

  gamma_zero : fieldDerivedPullback.{u, w} k Ω K Ψ e 0 ≫
          Functor.whiskerLeft (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
            (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u
              w}).rightDerivedZeroIsoSelf.hom =
        (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u
          w}).rightDerivedZeroIsoSelf.hom ≫
          fieldPullbackGlobalSections.{u, w} k Ω K Ψ e

  all_degree_comparison : ∀ (q : ℕ),
      fieldDerivedPullback.{u, w} k Ω K Ψ e q ≫
        Functor.whiskerLeft (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
          (fieldDerivedSectionsContinuousCohomologyIso.{u, w} K Ψ q).hom =
      (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q).hom ≫
        fieldNativePullback.{u, w} k Ω K Ψ e q

  literal_original_cochains : ∀ (q : ℕ)
      (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}),
      (fieldNativePullback.{u, w} k Ω K Ψ e q).app Q =
        ContinuousCohomology.discreteCoefficientForget.{max u w}.map
          (HomologicalComplex.homologyMap
            (fieldOriginalRankRestrictionCochainMap.{u, w} k Ω K Ψ
              (GaloisUnits.FieldMap.restrictContinuous e)
              ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)) q) ≫
        (fieldContinuousCohomologyFunctor.{u, w} K Ψ q).map
          ((fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.app Q)

  native_zero_invariants : ∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}),
      (fieldNativePullback.{u, w} k Ω K Ψ e 0).app Q ≫
        (fieldContinuousCohomologyZeroIso.{u, w} K Ψ).hom.app
          ((fieldGeometricStalkGaloisFunctor.{u, w} K Ψ).obj
            ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q)) =
      (fieldContinuousCohomologyZeroIso.{u, w} k Ω).hom.app
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) ≫
        (fieldInvariantRestriction.{u, u, w} k Ω K Ψ (GaloisUnits.FieldMap.restrictContinuous
          e)).app
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) ≫
        (fieldInvariantFunctor.{u, w} K Ψ).map
          ((fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.app Q)

  native_source_system : fieldNativeSourceDeltaSystem.{u, w} k Ω K Ψ e =
        CohomologicalDeltaFunctor.precompose (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
          (Functor.RightDerived.precompShortExact (fieldGeometricStalkGaloisFunctor.{u, w} k Ω))
          (fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω)

  native_target_system : fieldNativeTargetDeltaSystem.{u, w} k Ω K Ψ e =
        CohomologicalDeltaFunctor.precompose
          (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
          (fieldNativeInverseImageShortExact.{u, w} k Ω K Ψ e)
          (CohomologicalDeltaFunctor.precompose (fieldGeometricStalkGaloisFunctor.{u, w} K Ψ)
            (Functor.RightDerived.precompShortExact (fieldGeometricStalkGaloisFunctor.{u, w} K Ψ))
            (fieldContinuousCohomologyDeltaFunctor.{u, w} K Ψ))

  source_degree_objects : ∀ (q : ℕ),
      (fieldNativeSourceDeltaSystem.{u, w} k Ω K Ψ e).T q =
        fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
          fieldContinuousCohomologyFunctor.{u, w} k Ω q

  target_degree_objects : ∀ (q : ℕ),
      (fieldNativeTargetDeltaSystem.{u, w} k Ω K Ψ e).T q =
        smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e) ⋙
          fieldGeometricStalkGaloisFunctor.{u, w} K Ψ ⋙
            fieldContinuousCohomologyFunctor.{u, w} K Ψ q

  old_native_connector : ∀ (q : ℕ)
      (S : ShortComplex.ShortExactSequences (FieldCohomologyModule.{u, w} k Ω)),
      ((fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω).connecting q).app S =
        ContinuousCohomology.discreteCoefficientConnecting.{u, w}
          (G := InfiniteGalois.profiniteGalGrp k Ω) S.obj
          (fieldShortExact_discreteCoefficientExact.{u, w} k Ω S.obj S.property) q

  native_connecting : ∀ (q : ℕ)
      (S : ShortComplex.ShortExactSequences
        (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})),
      ((fieldNativeSourceDeltaSystem.{u, w} k Ω K Ψ e).connecting q).app S ≫
        (fieldNativePullback.{u, w} k Ω K Ψ e (q + 1)).app S.obj.X₁ =
      (fieldNativePullback.{u, w} k Ω K Ψ e q).app S.obj.X₃ ≫
        ((fieldNativeTargetDeltaSystem.{u, w} k Ω K Ψ e).connecting q).app S

  original_etale_connecting : ∀ (q : ℕ)
      (S : ShortComplex (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}))
      (hS : S.ShortExact),
      AddCommGrpCat.ofHom (CanonicalLongExactSequence.derivedBoundary.{u, w} hS q) ≫
          (fieldDerivedPullback.{u, w} k Ω K Ψ e (q + 1)).app S.X₁ =
        (fieldDerivedPullback.{u, w} k Ω K Ψ e q).app S.X₃ ≫
          AddCommGrpCat.ofHom
            (CanonicalLongExactSequence.derivedBoundary.{u, w}
              (smallEtaleInverseImage_shortExact.{u, w}
                (fieldOriginalPullback k Ω K Ψ e) S hS) q)

  single_lift_all_degree : ∀ (q : ℕ)
      (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}),
      (fieldDerivedPullback.{u, w} k Ω K Ψ e q).app
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F) ≫
        (fieldDerivedSectionsContinuousCohomologyIso.{u, w} K Ψ q).hom.app
          ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj
            ((liftCoefficients.{u, w} (Spec (.of k))).obj F)) =
      (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q).hom.app
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F) ≫
        (fieldNativePullback.{u, w} k Ω K Ψ e q).app
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F)

  single_lift_coefficient_maps : ∀ (q : ℕ)
      {F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}} (f : F ⟶ F'),
      (fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
        fieldContinuousCohomologyFunctor.{u, w} k Ω q).map
          ((liftCoefficients.{u, w} (Spec (.of k))).map f) ≫
        (fieldNativePullback.{u, w} k Ω K Ψ e q).app
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F') =
      (fieldNativePullback.{u, w} k Ω K Ψ e q).app
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F) ≫
        (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e) ⋙
          fieldGeometricStalkGaloisFunctor.{u, w} K Ψ ⋙
            fieldContinuousCohomologyFunctor.{u, w} K Ψ q).map
          ((liftCoefficients.{u, w} (Spec (.of k))).map f)

  resolution_square : ∀ (q : ℕ)
      {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
      (I : InjectiveResolution Q)
      (J : InjectiveResolution
        ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q)),
      fieldDerivedPullbackResolutionMap.{u, w} k Ω K Ψ e q I J ≫
        (fieldGammaNativeResolutionIso.{u, w} K Ψ q J).hom =
      (fieldGammaNativeResolutionIso.{u, w} k Ω q I).hom ≫
        (fieldNativePullback.{u, w} k Ω K Ψ e q).app Q

  resolution_choices : ∀ (q : ℕ)
      {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
      (I I' : InjectiveResolution Q)
      (J J' : InjectiveResolution
        ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q)),
      (InjectiveResolution.cohomologyComparisonIso I I'
        (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) q).hom ≫
        fieldDerivedPullbackResolutionMap.{u, w} k Ω K Ψ e q I' J' =
      fieldDerivedPullbackResolutionMap.{u, w} k Ω K Ψ e q I J ≫
        (InjectiveResolution.cohomologyComparisonIso J J'
          (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}) q).hom

  augmented_resolution_maps : ∀ (q : ℕ)
      {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}} (f : Q ⟶ Q')
      (I : InjectiveResolution Q) (I' : InjectiveResolution Q')
      (J : InjectiveResolution ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ
        e)).obj Q))
      (J' : InjectiveResolution ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ
        e)).obj Q'))
      (φ : I.cocomplex ⟶ I'.cocomplex)
      (_hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ I'.ι.f 0)
      (ψ : J.cocomplex ⟶ J'.cocomplex)
      (_hψ : J.ι.f 0 ≫ ψ.f 0 =
        (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).map f ≫ J'.ι.f 0),
      HomologicalComplex.homologyMap
        (((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).mapHomologicalComplex
          (ComplexShape.up ℕ)).map φ) q ≫
        fieldDerivedPullbackResolutionMap.{u, w} k Ω K Ψ e q I' J' =
      fieldDerivedPullbackResolutionMap.{u, w} k Ω K Ψ e q I J ≫
        HomologicalComplex.homologyMap
          (((Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u
            w}).mapHomologicalComplex
            (ComplexShape.up ℕ)).map ψ) q

  canonical_mapped_p : ∀ (q : ℕ)
      {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
      (I : InjectiveResolution Q),
      fieldMappedNativeRightIso.{u, w} k Ω q I =
        fieldMappedNativeRawRightIso.{u, w} k Ω q I

  mapped_T_homology_formula : ∀ (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q),
    (fieldGammaNativeResolutionIso.{u, w} k Ω q I).hom =
      (fieldDerivedSectionsInvariantsResolutionIso.{u, w} k Ω q I).hom ≫
        (fieldMappedNativeRightIso.{u, w} k Ω q I).inv

  gamma_identity : ∀ (q : ℕ),
      fieldDerivedPullback.{u, w} k Ω k Ω (GaloisUnits.FieldMap.id k Ω) q ≫
        Functor.whiskerRight (fieldInverseImageIdentityIso.{u, w} k Ω).hom
          ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q) =
      𝟙 ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q)

  native_identity : ∀ (q : ℕ),
      fieldNativePullback.{u, w} k Ω k Ω (GaloisUnits.FieldMap.id k Ω) q ≫
        Functor.whiskerRight (fieldInverseImageIdentityIso.{u, w} k Ω).hom
          (fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
            fieldContinuousCohomologyFunctor.{u, w} k Ω q) =
      𝟙 (fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
        fieldContinuousCohomologyFunctor.{u, w} k Ω q)

  finite_algebra_embedding :
    letI : Algebra k Ψ := GaloisUnits.FieldMap.sourceBaseAlgebra e
    ∀ A : CommAlgCat.FiniteEtale.{u} k,
      Function.Bijective (fun f : A →ₐ[k] Ω =>
        (GaloisUnits.FieldMap.extensionAlgHom e).comp f)
  gamma_composition :
    ∀ (L Φ : Type u) [Field L] [Field Φ] [Algebra L Φ] [IsSepClosure L Φ]
      (eNext : GaloisUnits.FieldMap K Ψ L Φ) (q : ℕ),
      fieldDerivedPullback.{u, w} k Ω K Ψ e q ≫
        Functor.whiskerLeft (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
          (fieldDerivedPullback.{u, w} K Ψ L Φ eNext q) ≫
        (Functor.associator
          (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
          (smallEtaleInverseImage.{u, w} (fieldOriginalPullback K Ψ L Φ eNext))
          ((Sheaf.Γ (Spec (.of L)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q)).inv
            ≫
        Functor.whiskerRight (fieldInverseImageCompositionIso.{u, w} k Ω K Ψ L Φ e eNext).hom
          ((Sheaf.Γ (Spec (.of L)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q) =
      fieldDerivedPullback.{u, w} k Ω L Φ (GaloisUnits.FieldMap.comp eNext e) q
  native_composition :
    ∀ (L Φ : Type u) [Field L] [Field Φ] [Algebra L Φ] [IsSepClosure L Φ]
      (eNext : GaloisUnits.FieldMap K Ψ L Φ) (q : ℕ),
      fieldNativePullback.{u, w} k Ω K Ψ e q ≫
        Functor.whiskerLeft (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
          (fieldNativePullback.{u, w} K Ψ L Φ eNext q) ≫
        (Functor.associator
          (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
          (smallEtaleInverseImage.{u, w} (fieldOriginalPullback K Ψ L Φ eNext))
          (fieldGeometricStalkGaloisFunctor.{u, w} L Φ ⋙
            fieldContinuousCohomologyFunctor.{u, w} L Φ q)).inv ≫
        Functor.whiskerRight (fieldInverseImageCompositionIso.{u, w} k Ω K Ψ L Φ e eNext).hom
          (fieldGeometricStalkGaloisFunctor.{u, w} L Φ ⋙
            fieldContinuousCohomologyFunctor.{u, w} L Φ q) =
      fieldNativePullback.{u, w} k Ω L Φ (GaloisUnits.FieldMap.comp eNext e) q

/-- The complete original field/site/module law family is constructed from the same actual maps. -/
theorem original_field_site_module_cohomology_naturality (e : GaloisUnits.FieldMap k Ω K Ψ) :
    FieldSiteModuleCohomologyNaturalityLaws.{u, w} k Ω K Ψ e where
  point_fst := fieldChangeOriginalPoint_fst.{u} k Ω K Ψ e
  point_snd := fieldChangeOriginalPoint_snd.{u} k Ω K Ψ e
  original_germ := fieldChangeUnderlyingStalkIso_original_germ.{u, w} k Ω K Ψ e
  left_action := fieldChangeUnderlyingStalkIso_equivariant.{u, w} k Ω K Ψ e
  same_underlying_stalk := fieldChangeStalkModuleIso_hom_underlying.{u, w} k Ω K Ψ e
  terminal_sections := fieldPullbackGlobalSections_terminal_section.{u, w} k Ω K Ψ e
  zero_invariants := fieldPullbackGlobalSections_invariants_naturality.{u, w} k Ω K Ψ e
  single_lift_germ := fieldChange_original_coefficient_germ.{u, w} k Ω K Ψ e
  single_lift_stalk_map := fieldChange_original_coefficient_naturality.{u, w} k Ω K Ψ e
  gamma_naturality := fieldDerivedPullback_naturality.{u, w} k Ω K Ψ e
  gamma_zero := fieldDerivedPullback_zero.{u, w} k Ω K Ψ e
  all_degree_comparison := fieldDerivedPullback_native_square.{u, w} k Ω K Ψ e
  literal_original_cochains := fieldNativePullback_original_map.{u, w} k Ω K Ψ e
  native_zero_invariants := fieldNativePullback_zero_invariants.{u, w} k Ω K Ψ e
  native_source_system := fieldNativeSourceDeltaSystem_eq.{u, w} k Ω K Ψ e
  native_target_system := fieldNativeTargetDeltaSystem_eq.{u, w} k Ω K Ψ e
  source_degree_objects := fieldNativeSourceDeltaSystem_T.{u, w} k Ω K Ψ e
  target_degree_objects := fieldNativeTargetDeltaSystem_T.{u, w} k Ω K Ψ e
  old_native_connector := fieldOldNativeDelta_connector.{u, w} k Ω
  native_connecting := fieldNativePullback_connecting.{u, w} k Ω K Ψ e
  original_etale_connecting := fieldDerivedPullback_etale_connecting.{u, w} k Ω K Ψ e
  single_lift_all_degree := original_field_derived_pullback_native_square.{u, w} k Ω K Ψ e
  single_lift_coefficient_maps := original_field_native_pullback_naturality.{u, w} k Ω K Ψ e
  resolution_square := fieldDerivedPullbackResolutionMap_native_square.{u, w} k Ω K Ψ e
  resolution_choices := fieldDerivedPullbackResolutionMap_choice.{u, w} k Ω K Ψ e
  augmented_resolution_maps := fieldDerivedPullbackResolutionMap_naturality.{u, w} k Ω K Ψ e
  canonical_mapped_p := fieldMappedNativeRightIso_presentation.{u, w} k Ω
  mapped_T_homology_formula := fieldGammaNativeResolutionIso_mapped_T.{u, w} k Ω
  gamma_identity := fieldDerivedPullback_id.{u, w} k Ω
  native_identity := fieldNativePullback_id.{u, w} k Ω

  finite_algebra_embedding := by
    let : Algebra k Ψ := GaloisUnits.FieldMap.sourceBaseAlgebra e
    intro A
    exact (CommAlgCat.FiniteEtale.embeddingHomEquiv k Ω Ψ
      (GaloisUnits.FieldMap.extensionAlgHom e) A).bijective
  gamma_composition := fun L Φ _ _ _ _ eNext q =>
    fieldDerivedPullback_comp.{u, w} k Ω K Ψ L Φ e eNext q
  native_composition := fun L Φ _ _ _ _ eNext q =>
    fieldNativePullback_comp.{u, w} k Ω K Ψ L Φ e eNext q

end AlgebraicGeometry.Scheme.DerivedSections

#print axioms
AlgebraicGeometry.Scheme.DerivedSections.original_field_site_module_cohomology_naturality

end
