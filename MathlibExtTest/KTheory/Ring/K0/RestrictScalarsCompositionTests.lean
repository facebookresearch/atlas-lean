/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.K0.RestrictScalarsComposition

@[expose] public section
noncomputable section

open AlgebraicKTheory
open CategoryTheory
open scoped ChangeOfRings

universe u

variable {R S : Type u} [CommRing R] [CommRing S]
variable (f : R →+* S) (hf : f.IsFinite)
variable (hp : @Module.Projective R _ S _ f.toModule)
variable (eS : letI : Module R S := f.toModule; S ≃ₗ[R] R × R)

example :
    (RingK0.restrictScalars f hf hp).comp (RingK0.mapRingHom f).toAddMonoidHom =
      2 • AddMonoidHom.id (RingK0 R) :=
  RingK0.restrictScalars_comp_mapRingHom f hf hp eS

example (x : RingK0 R) :
    RingK0.restrictScalars f hf hp (RingK0.mapRingHom f x) = x + x := by
  have h := DFunLike.congr_fun (RingK0.restrictScalars_comp_mapRingHom f hf hp eS) x
  simpa [two_nsmul] using h

example (σ : S ≃+* S) (hσ : σ.toRingHom.comp f = f)
    (e : (FGProjectiveCat.restrictScalars f hf hp ⋙ FGProjectiveCat.baseChange f).obj
      (FGProjectiveCat.regular S) ≃ₗ[S] S × S)
    (he : ∀ z w : S, e (z ⊗ₜ[R,f] w) = (z * w, z * σ w)) :
    (RingK0.mapRingHom f).toAddMonoidHom.comp (RingK0.restrictScalars f hf hp) =
      AddMonoidHom.id (RingK0 S) + (RingK0.mapRingHom σ.toRingHom).toAddMonoidHom :=
  RingK0.mapRingHom_comp_restrictScalars f hf hp σ hσ e he

example (σ : S ≃+* S) (hσ : σ.toRingHom.comp f = f)
    (e : (FGProjectiveCat.restrictScalars f hf hp ⋙ FGProjectiveCat.baseChange f).obj
      (FGProjectiveCat.regular S) ≃ₗ[S] S × S)
    (he : ∀ z w : S, e (z ⊗ₜ[R,f] w) = (z * w, z * σ w)) (x : RingK0 S) :
    RingK0.mapRingHom f (RingK0.restrictScalars f hf hp x) =
      x + RingK0.mapRingHom σ.toRingHom x :=
  DFunLike.congr_fun (RingK0.mapRingHom_comp_restrictScalars f hf hp σ hσ e he) x

end
