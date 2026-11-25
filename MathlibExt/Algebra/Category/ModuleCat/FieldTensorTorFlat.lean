/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.ModuleCat.NativeTorFlatUniverse
public import MathlibExt.Algebra.Category.ModuleCat.FieldTensorTorLocalizationComparison

/-!
# Positive local graph Tor for flat middle coefficients
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.UniverseTensor

namespace ModuleCat.UniverseTensor
universe k r v w m

variable (K : Type k) (B : Type r) (V : Type v) (W : Type w)
  [Field K] [CommRing B] [CommRing V] [CommRing W]
  [Algebra K B] [Algebra K V] [Algebra K W]
  (a : B →ₐ[K] V) (b : B →ₐ[K] W)

/-- The actual native intrinsic local Tor vanishes in every positive degree
when its original left middle coefficient is flat. -/
theorem intrinsicAmbientTorAtPrime_isZero_succ_of_flat_left
    (hflat : letI : Algebra B V := a.toRingHom.toAlgebra; Module.Flat B V)
    (p : letI : Algebra B V := a.toRingHom.toAlgebra
         let : Algebra B W := b.toRingHom.toAlgebra
         PrimeSpectrum (V ⊗[B] W)) (q : ℕ) :
    IsZero (intrinsicAmbientTorAtPrime.{k,r,v,w,m} K B V W a b p (q + 1)) := by
  let : Algebra B V := a.toRingHom.toAlgebra
  let : Algebra B W := b.toRingHom.toAlgebra
  let : Module.Flat B V := hflat
  let X := originalMiddleTor.{r,v,w,max k m} B V W (q + 1)
  let : Module (V ⊗[B] W) X := originalMiddleTorTensorModule.{r,v,w,max k m} B V W (q + 1)
  have hz : IsZero X := nativeTor_isZero_succ_of_flat_left.{r,max k v w m} B
    (ModuleCat.of B (ULift.{max k r v w m} V))
    (ModuleCat.of B (ULift.{max k r v w m} W)) q
  let : Subsingleton X := ModuleCat.subsingleton_of_isZero hz
  have hlength := intrinsicAmbientTorAtPrime_length.{k,r,v,w,m} K B V W a b p (q + 1)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply (Module.length_eq_zero_iff
    (R := Localization.AtPrime (p.asIdeal.comap (intrinsicSupportMap K B V W a b).toRingHom))).mp
  rw [hlength]
  exact Module.length_eq_zero_iff.mpr inferInstance

/-- The actual native intrinsic local Tor also vanishes when its original
resolved middle coefficient is flat, with the coefficient order retained. -/
theorem intrinsicAmbientTorAtPrime_isZero_succ_of_flat_right
    (hflat : letI : Algebra B W := b.toRingHom.toAlgebra; Module.Flat B W)
    (p : letI : Algebra B V := a.toRingHom.toAlgebra
         let : Algebra B W := b.toRingHom.toAlgebra
         PrimeSpectrum (V ⊗[B] W)) (q : ℕ) :
    IsZero (intrinsicAmbientTorAtPrime.{k,r,v,w,m} K B V W a b p (q + 1)) := by
  let : Algebra B V := a.toRingHom.toAlgebra
  let : Algebra B W := b.toRingHom.toAlgebra
  let : Module.Flat B W := hflat
  let X := originalMiddleTor.{r,v,w,max k m} B V W (q + 1)
  let : Module (V ⊗[B] W) X := originalMiddleTorTensorModule.{r,v,w,max k m} B V W (q + 1)
  have hz : IsZero X := nativeTor_isZero_succ_of_flat_right.{r,max k v w m} B
    (ModuleCat.of B (ULift.{max k r v w m} V))
    (ModuleCat.of B (ULift.{max k r v w m} W)) q
  let : Subsingleton X := ModuleCat.subsingleton_of_isZero hz
  have hlength := intrinsicAmbientTorAtPrime_length.{k,r,v,w,m} K B V W a b p (q + 1)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply (Module.length_eq_zero_iff
    (R := Localization.AtPrime (p.asIdeal.comap (intrinsicSupportMap K B V W a b).toRingHom))).mp
  rw [hlength]
  exact Module.length_eq_zero_iff.mpr inferInstance

end ModuleCat.UniverseTensor
