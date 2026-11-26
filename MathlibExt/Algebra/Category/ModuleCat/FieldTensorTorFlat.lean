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
# Positive localized graph Tor vanishes for a flat middle factor

Let K be a field, B,V,W commutative K-algebras and a:B→V,b:B→W
K-algebra maps. Put T=V⊗[B]W and D=(V⊗[K]W)⊗[K]B.
The right and left graph evaluations D→V⊗[K]W use b and a,
respectively, and the support map σ:D→T is their common quotient.

For p∈Spec(T), localize the intrinsic ambient Tor of the right graph
coefficient followed by the left graph coefficient at σ⁻¹(p).
If V is flat over B through a, or W is flat over B through b,
this local ambient Tor is zero in every positive degree.

The coefficient order is V,W in the middle-ring comparison, while
the ambient Tor uses graph-right then graph-left. Ring worlds
k,r,v,w are independent, and the common module height is
max(k,r,v,w,m).
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

/-- For a field K, commutative K-algebras B,V,W and
K-algebra maps a:B→V,b:B→W, assume V flat as a B-module via a.
For every p∈Spec(V⊗[B]W) and q≥0, the intrinsic local
ambient Tor in degree q+1 is a zero object.
Its local ring is D_(σ⁻¹p), D=(V⊗[K]W)⊗[K]B. -/
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

/-- For a field K, commutative K-algebras B,V,W and
K-algebra maps a:B→V,b:B→W, assume W flat as a B-module via b.
For every p∈Spec(V⊗[B]W) and q≥0, the intrinsic local
ambient Tor in degree q+1 is zero, with the same ordered
graph coefficients and common module height max(k,r,v,w,m). -/
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
