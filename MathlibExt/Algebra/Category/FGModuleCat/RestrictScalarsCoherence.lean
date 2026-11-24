/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.Algebra.Category.FGModuleCat.RestrictScalars

/-!
# Coherence for finite restriction on `FGModuleCat`

Lifts `ModuleCat.restrictScalarsId.{v}` and `ModuleCat.restrictScalarsComp.{v}`
to the finite-restriction functors on `FGModuleCat`. Reuses
`restrictScalarsCompForget₂Iso.{v}` and the fully faithful inclusion of the
`isFG` full subcategory. Provides identity and composition coherence
isomorphisms for `FGModuleCat.restrictScalars.{v}`.
-/

@[expose] public section

open CategoryTheory

universe v w uR uS uT

namespace FGModuleCat

variable {R : Type uR} {S : Type uS} {T : Type uT} [Ring R] [Ring S] [Ring T]

/-- Identity coherence: `restrictScalars.{v} (RingHom.id R) ≅ 𝟭 (FGModuleCat R)`.
Orientation is from restriction along `RingHom.id` to the identity functor. -/
noncomputable def restrictScalarsId (R : Type uR) [Ring R] :
    restrictScalars.{v} (RingHom.id R) RingHom.isFinite_id ≅ 𝟭 (FGModuleCat.{v} R) :=
  Functor.fullyFaithfulCancelRight
    (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R))
    (restrictScalarsCompForget₂Iso.{v} (RingHom.id R) RingHom.isFinite_id ≪≫
      Functor.isoWhiskerLeft (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R))
        (ModuleCat.restrictScalarsId.{v} R))

/-- Composition coherence:
`restrictScalars.{v} (g.comp f) ≅ restrictScalars.{v} g ⋙ restrictScalars.{v} f`.
Orientation is from restriction along `g.comp f` to `g` then `f`. -/
noncomputable def restrictScalarsComp (f : R →+* S) (g : S →+* T)
    (hf : f.IsFinite) (hg : g.IsFinite) :
    restrictScalars.{v} (g.comp f) (RingHom.isFinite_comp hf hg) ≅
      restrictScalars.{v} g hg ⋙ restrictScalars.{v} f hf := by
  let H := forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)
  let FT := forget₂ (FGModuleCat.{v} T) (ModuleCat.{v} T)
  let FS := forget₂ (FGModuleCat.{v} S) (ModuleCat.{v} S)
  let F : FGModuleCat.{v} T ⥤ FGModuleCat.{v} R :=
    restrictScalars.{v} (g.comp f) (RingHom.isFinite_comp hf hg)
  let G : FGModuleCat.{v} T ⥤ FGModuleCat.{v} R :=
    restrictScalars.{v} g hg ⋙ restrictScalars.{v} f hf
  let isoLeft₁ : F ⋙ H ≅ FT ⋙ ModuleCat.restrictScalars.{v} (g.comp f) :=
    restrictScalarsCompForget₂Iso.{v} (g.comp f) (RingHom.isFinite_comp hf hg)
  let isoLeft₂ : FT ⋙ ModuleCat.restrictScalars.{v} (g.comp f) ≅
      FT ⋙ (ModuleCat.restrictScalars.{v} g ⋙ ModuleCat.restrictScalars.{v} f) :=
    Functor.isoWhiskerLeft FT (ModuleCat.restrictScalarsComp.{v} f g)
  let isoF : F ⋙ H ≅ FT ⋙ (ModuleCat.restrictScalars.{v} g ⋙ ModuleCat.restrictScalars.{v} f) :=
    isoLeft₁ ≪≫ isoLeft₂
  let isoMid : restrictScalars.{v} f hf ⋙ H ≅ FS ⋙ ModuleCat.restrictScalars.{v} f :=
    restrictScalarsCompForget₂Iso.{v} f hf
  let isoG₁ : G ⋙ H ≅
      restrictScalars.{v} g hg ⋙ (restrictScalars.{v} f hf ⋙ H) :=
    Functor.associator (restrictScalars.{v} g hg) (restrictScalars.{v} f hf) H
  let isoG₂ : restrictScalars.{v} g hg ⋙ (restrictScalars.{v} f hf ⋙ H) ≅
      restrictScalars.{v} g hg ⋙ (FS ⋙ ModuleCat.restrictScalars.{v} f) :=
    Functor.isoWhiskerLeft (restrictScalars.{v} g hg) isoMid
  let isoG₃ : restrictScalars.{v} g hg ⋙ (FS ⋙ ModuleCat.restrictScalars.{v} f) ≅
      (restrictScalars.{v} g hg ⋙ FS) ⋙ ModuleCat.restrictScalars.{v} f :=
    (Functor.associator (restrictScalars.{v} g hg) FS (ModuleCat.restrictScalars.{v} f)).symm
  let isoMidG : restrictScalars.{v} g hg ⋙ FS ≅ FT ⋙ ModuleCat.restrictScalars.{v} g :=
    restrictScalarsCompForget₂Iso.{v} g hg
  let isoG₄ : (restrictScalars.{v} g hg ⋙ FS) ⋙ ModuleCat.restrictScalars.{v} f ≅
      (FT ⋙ ModuleCat.restrictScalars.{v} g) ⋙ ModuleCat.restrictScalars.{v} f :=
    Functor.isoWhiskerRight isoMidG (ModuleCat.restrictScalars.{v} f)
  let isoG₅ : (FT ⋙ ModuleCat.restrictScalars.{v} g) ⋙ ModuleCat.restrictScalars.{v} f ≅
      FT ⋙ (ModuleCat.restrictScalars.{v} g ⋙ ModuleCat.restrictScalars.{v} f) :=
    Functor.associator FT (ModuleCat.restrictScalars.{v} g) (ModuleCat.restrictScalars.{v} f)
  let isoG : G ⋙ H ≅ FT ⋙ (ModuleCat.restrictScalars.{v} g ⋙ ModuleCat.restrictScalars.{v} f) :=
    isoG₁ ≪≫ isoG₂ ≪≫ isoG₃ ≪≫ isoG₄ ≪≫ isoG₅
  let isoFH : F ⋙ H ≅ G ⋙ H := isoF ≪≫ isoG.symm
  exact Functor.fullyFaithfulCancelRight H isoFH

/-- Restriction commutes with actual finite-module ULift on the original module carriers. -/
noncomputable def restrictScalarsULiftIso (f : R →+* S) (hf : f.IsFinite) :
    restrictScalars.{v} f hf ⋙ FGModuleCat.ulift.{v, w} R ≅
      FGModuleCat.ulift.{v, w} S ⋙ restrictScalars.{max v w} f hf :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y g
    exact FGModuleCat.hom_ext rfl)

/-- The ULift comparison retains every actual original lifted module element. -/
theorem restrictScalarsULiftIso_hom_apply (f : R →+* S) (hf : f.IsFinite)
    (X : FGModuleCat.{v} S) (x : X) :
    (restrictScalarsULiftIso.{v, w} f hf).hom.app X (ULift.up x) = ULift.up x := rfl

/-- The inverse ULift comparison returns the same original lifted module element. -/
theorem restrictScalarsULiftIso_inv_apply (f : R →+* S) (hf : f.IsFinite)
    (X : FGModuleCat.{v} S) (x : X) :
    (restrictScalarsULiftIso.{v, w} f hf).inv.app X (ULift.up x) = ULift.up x := rfl

end FGModuleCat
