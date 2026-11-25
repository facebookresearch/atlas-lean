/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.BaseChange
public import MathlibExt.Algebra.Category.FGProjectiveCat.RestrictScalars
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Scalar automorphisms fixing a finite-projective restriction

The actual automorphism extension is compared with inverse restriction by
its native adjunction and ring-equivalence restriction. Restricting along a
fixed coefficient homomorphism gives the same original restriction functor.
The original tensor unit and coefficient action are retained.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped ChangeOfRings

universe v uR uS

namespace ModuleCat

variable {S : Type uS} [CommRing S]

/-- The original automorphism extension is the inverse scalar restriction,
using the two existing adjunctions and their original unit maps. -/
def automorphismExtendRestrictIso (σ : S ≃+* S) :
    extendScalars.{uS, uS, max uS v} σ.toRingHom ≅
      restrictScalars.{max uS v, uS, uS} σ.symm.toRingHom :=
  Adjunction.leftAdjointUniq (extendRestrictScalarsAdj σ.toRingHom)
    (restrictScalarsEquivalenceOfRingEquiv σ).symm.toAdjunction

/-- The original extension unit maps to the original module element. -/
theorem automorphismExtendRestrictIso_hom_unit (σ : S ≃+* S)
    (M : ModuleCat.{max uS v} S) (p : M) :
    (automorphismExtendRestrictIso σ).hom.app M
        ((extendRestrictScalarsAdj σ.toRingHom).unit.app M p) =
      (show (restrictScalars σ.symm.toRingHom).obj M from p) := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (extendRestrictScalarsAdj σ.toRingHom)
    (restrictScalarsEquivalenceOfRingEquiv σ).symm.toAdjunction M
  have hv := ConcreteCategory.congr_hom h p
  exact hv

/-- Every original pure tensor keeps the inverse coefficient action. -/
theorem automorphismExtendRestrictIso_hom_pure (σ : S ≃+* S)
    (M : ModuleCat.{max uS v} S) (s : S) (p : M) :
    (automorphismExtendRestrictIso σ).hom.app M
        (s • (show (extendScalars σ.toRingHom).obj M from
          (extendRestrictScalarsAdj σ.toRingHom).unit.app M p)) =
      (show (restrictScalars σ.symm.toRingHom).obj M from σ.symm s • p) := by
  let T := (extendScalars σ.toRingHom).obj M
  let N := (restrictScalars σ.symm.toRingHom).obj M
  let unitPoint : T := (extendRestrictScalarsAdj σ.toRingHom).unit.app M p
  have hu : (automorphismExtendRestrictIso σ).hom.app M unitPoint = (show N from p) :=
    automorphismExtendRestrictIso_hom_unit σ M p
  calc
    _ = s • (automorphismExtendRestrictIso σ).hom.app M unitPoint :=
      ((automorphismExtendRestrictIso σ).hom.app M).hom.map_smul s unitPoint
    _ = s • (show N from p) := congrArg (fun z : N => s • z) hu
    _ = _ := rfl

/-- The inverse retains the original extension unit, on every module element. -/
theorem automorphismExtendRestrictIso_inv_apply (σ : S ≃+* S)
    (M : ModuleCat.{max uS v} S) (p : M) :
    (automorphismExtendRestrictIso σ).inv.app M
        (show (restrictScalars σ.symm.toRingHom).obj M from p) =
      (extendRestrictScalarsAdj σ.toRingHom).unit.app M p := by
  have h := ConcreteCategory.congr_hom
    ((automorphismExtendRestrictIso σ).hom_inv_id_app M)
    ((extendRestrictScalarsAdj σ.toRingHom).unit.app M p)
  change (automorphismExtendRestrictIso σ).inv.app M
      ((automorphismExtendRestrictIso σ).hom.app M
        ((extendRestrictScalarsAdj σ.toRingHom).unit.app M p)) =
    (extendRestrictScalarsAdj σ.toRingHom).unit.app M p at h
  rw [automorphismExtendRestrictIso_hom_unit] at h
  exact h

variable {R : Type uR} [Ring R]

/-- The inverse automorphism fixes the same coefficient map. -/
theorem automorphism_symm_comp_eq (f : R →+* S) (σ : S ≃+* S)
    (hσ : σ.toRingHom.comp f = f) : σ.symm.toRingHom.comp f = f := by
  ext r
  apply σ.injective
  have h := RingHom.congr_fun hσ r
  change σ (σ.symm (f r)) = σ (f r)
  rw [σ.apply_symm_apply]
  exact h.symm

/-- The actual automorphism extension followed by coefficient restriction is
naturally isomorphic to the same original coefficient restriction. -/
def automorphismRestrictionIso (f : R →+* S) (σ : S ≃+* S)
    (hσ : σ.toRingHom.comp f = f) :
    extendScalars.{uS, uS, max uS v} σ.toRingHom ⋙
        restrictScalars.{max uS v, uR, uS} f ≅
      restrictScalars.{max uS v, uR, uS} f :=
  Functor.isoWhiskerRight (automorphismExtendRestrictIso σ) (restrictScalars f) ≪≫
    (restrictScalarsComp f σ.symm.toRingHom).symm ≪≫
      restrictScalarsCongr (automorphism_symm_comp_eq f σ hσ)

/-- The component R-linear equivalence retains the actual native functor maps. -/
def automorphismRestrictionLinearEquiv (f : R →+* S) (σ : S ≃+* S)
    (hσ : σ.toRingHom.comp f = f) (M : ModuleCat.{max uS v} S) :
    (restrictScalars f).obj ((extendScalars σ.toRingHom).obj M) ≃ₗ[R]
      (restrictScalars f).obj M :=
  ((automorphismRestrictionIso f σ hσ).app M).toLinearEquiv

/-- The forward restricted comparison retains the original inverse coefficient
on each native pure tensor, expressed through the same original unit. -/
theorem automorphismRestrictionLinearEquiv_pure (f : R →+* S) (σ : S ≃+* S)
    (hσ : σ.toRingHom.comp f = f) (M : ModuleCat.{max uS v} S) (s : S) (p : M) :
    automorphismRestrictionLinearEquiv f σ hσ M
        (show (restrictScalars f).obj ((extendScalars σ.toRingHom).obj M) from
          s • (show (extendScalars σ.toRingHom).obj M from
            (extendRestrictScalarsAdj σ.toRingHom).unit.app M p)) =
      (show (restrictScalars f).obj M from σ.symm s • p) := by
  change (automorphismExtendRestrictIso σ).hom.app M
      (s • (show (extendScalars σ.toRingHom).obj M from
        (extendRestrictScalarsAdj σ.toRingHom).unit.app M p)) = _
  exact automorphismExtendRestrictIso_hom_pure σ M s p

/-- The inverse restricted comparison is the original unit tensor. -/
theorem automorphismRestrictionLinearEquiv_symm_apply (f : R →+* S) (σ : S ≃+* S)
    (hσ : σ.toRingHom.comp f = f) (M : ModuleCat.{max uS v} S) (p : M) :
    (automorphismRestrictionLinearEquiv f σ hσ M).symm p =
      (show (restrictScalars f).obj ((extendScalars σ.toRingHom).obj M) from
        (extendRestrictScalarsAdj σ.toRingHom).unit.app M p) := by
  change (automorphismExtendRestrictIso σ).inv.app M
      (show (restrictScalars σ.symm.toRingHom).obj M from p) = _
  exact automorphismExtendRestrictIso_inv_apply σ M p

/-- Naturality on every original tensor is the native natural-isomorphism law. -/
theorem automorphismRestrictionLinearEquiv_naturality (f : R →+* S) (σ : S ≃+* S)
    (hσ : σ.toRingHom.comp f = f) {M N : ModuleCat.{max uS v} S} (g : M ⟶ N)
    (t : (restrictScalars f).obj ((extendScalars σ.toRingHom).obj M)) :
    automorphismRestrictionLinearEquiv f σ hσ N
        ((restrictScalars f).map ((extendScalars σ.toRingHom).map g) t) =
      (restrictScalars f).map g (automorphismRestrictionLinearEquiv f σ hσ M t) :=
  ConcreteCategory.congr_hom ((automorphismRestrictionIso f σ hσ).hom.naturality g) t

end ModuleCat

namespace FGProjectiveCat

variable {R : Type uR} {S : Type uS} [Ring R] [CommRing S]

/-- The original automorphism base-change followed by finite-projective
restriction is naturally isomorphic to the same original restriction functor.
The common module world supports the actual native tensor carrier. -/
def baseChangeAutomorphismRestrictScalarsIso (f : R →+* S) (hf : f.IsFinite)
    (hp : @Module.Projective R _ S _ f.toModule) (σ : S ≃+* S)
    (hσ : σ.toRingHom.comp f = f) :
    baseChange.{max uS v} σ.toRingHom ⋙ restrictScalars.{max uS v} f hf hp ≅
      restrictScalars.{max uS v} f hf hp :=
  NatIso.ofComponents
    (fun P => (ModuleCat.isFGProjective R).isoMk
      ((ModuleCat.automorphismRestrictionIso f σ hσ).app P.obj))
    (by
      intro P Q g
      apply ObjectProperty.hom_ext
      exact (ModuleCat.automorphismRestrictionIso f σ hσ).hom.naturality g.hom)

end FGProjectiveCat

end
