/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeRegularPathCoefficients
public import MathlibExt.AlgebraicTopology.LocalCoefficient.RegularModuleBasis
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.GroupTheory.Perm.Basic

/-!
# Executable regular coefficient transports

Signed integral generators test scalar preservation and inverse transport.
Noncommuting permutations make reversal of the two transport legs observable.
The module-valued case uses the actual bundled coefficient functor.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace MathlibExtTest.NativeRegularPathCoefficients

/-- Forward transport takes the signed original label 3 along +2 to label 5. -/
theorem signed_cyclic_forward_transport :
    let y := SingleObj.star (Multiplicative ℤ)
    let f : y ⟶ y :=
      (SingleObj.toEnd (Multiplicative ℤ) (Multiplicative.ofAdd (2 : ℤ))).asHom
    regularPathCoefficientTransport y f
        ((-7 : ℤ) • FreeAbelianGroup.of (Multiplicative.ofAdd (3 : ℤ))) =
      (-7 : ℤ) • FreeAbelianGroup.of (Multiplicative.ofAdd (5 : ℤ)) := by
  dsimp only
  let y := SingleObj.star (Multiplicative ℤ)
  let f : y ⟶ y :=
      (SingleObj.toEnd (Multiplicative ℤ) (Multiplicative.ofAdd (2 : ℤ))).asHom
  rewrite [map_zsmul, regularPathCoefficientTransport_of]
  rfl

/-- The actual inverse equivalence returns the original signed label, not +2 again. -/
theorem signed_cyclic_inverse_transport :
    let y := SingleObj.star (Multiplicative ℤ)
    let f : y ⟶ y :=
      (SingleObj.toEnd (Multiplicative ℤ) (Multiplicative.ofAdd (2 : ℤ))).asHom
    (regularPathCoefficientTransportEquiv y f).symm
        ((-7 : ℤ) • FreeAbelianGroup.of (Multiplicative.ofAdd (5 : ℤ))) =
      (-7 : ℤ) • FreeAbelianGroup.of (Multiplicative.ofAdd (3 : ℤ)) := by
  dsimp only
  let y := SingleObj.star (Multiplicative ℤ)
  let f : y ⟶ y :=
      (SingleObj.toEnd (Multiplicative ℤ) (Multiplicative.ofAdd (2 : ℤ))).asHom
  let e := regularPathCoefficientTransportEquiv y f
  let t := (-7 : ℤ) • FreeAbelianGroup.of (Multiplicative.ofAdd (3 : ℤ))
  have h : e t = (-7 : ℤ) • FreeAbelianGroup.of (Multiplicative.ofAdd (5 : ℤ)) := by
    rewrite [regularPathCoefficientTransportEquiv_apply]
    exact signed_cyclic_forward_transport
  exact (congrArg e.symm h.symm).trans (e.symm_apply_apply t)

/-- Reversing two noncommuting transport legs changes the actual free generator. -/
theorem noncommuting_two_leg_transport_order :
    let G := Equiv.Perm (Fin 3)
    let y := SingleObj.star G
    let φ : G ≃* End y := SingleObj.toEnd G
    let a : G := Equiv.swap (0 : Fin 3) 1
    let b : G := Equiv.swap (1 : Fin 3) 2
    let fa : y ⟶ y := (φ a).asHom
    let fb : y ⟶ y := (φ b).asHom
    let t := FreeAbelianGroup.of (φ (1 : G)).asHom
    regularPathCoefficientTransport y fb (regularPathCoefficientTransport y fa t) =
        FreeAbelianGroup.of (φ (b * a)).asHom ∧
      regularPathCoefficientTransport y fb (regularPathCoefficientTransport y fa t) ≠
        regularPathCoefficientTransport y fa (regularPathCoefficientTransport y fb t) := by
  dsimp only
  let G := Equiv.Perm (Fin 3)
  let y := SingleObj.star G
  let φ : G ≃* End y := SingleObj.toEnd G
  let a : G := Equiv.swap (0 : Fin 3) 1
  let b : G := Equiv.swap (1 : Fin 3) 2
  let fa : y ⟶ y := (φ a).asHom
  let fb : y ⟶ y := (φ b).asHom
  let t := FreeAbelianGroup.of (φ (1 : G)).asHom
  have hOne : (φ (1 : G)).asHom = 𝟙 y :=
    congrArg (fun e : End y => e.asHom) (map_one φ)
  have hABArrow : ((φ (1 : G)).asHom ≫ fa) ≫ fb = (φ (b * a)).asHom := by
    rewrite [hOne, Category.id_comp]
    exact (congrArg (fun e : End y => e.asHom) (map_mul φ b a)).symm
  have hBAArrow : ((φ (1 : G)).asHom ≫ fb) ≫ fa = (φ (a * b)).asHom := by
    rewrite [hOne, Category.id_comp]
    exact (congrArg (fun e : End y => e.asHom) (map_mul φ a b)).symm
  have hAB : regularPathCoefficientTransport y fb (regularPathCoefficientTransport y fa t) =
      FreeAbelianGroup.of (φ (b * a)).asHom := by
    rewrite [regularPathCoefficientTransport_of, regularPathCoefficientTransport_of]
    exact congrArg FreeAbelianGroup.of hABArrow
  have hBA : regularPathCoefficientTransport y fa (regularPathCoefficientTransport y fb t) =
      FreeAbelianGroup.of (φ (a * b)).asHom := by
    rewrite [regularPathCoefficientTransport_of, regularPathCoefficientTransport_of]
    exact congrArg FreeAbelianGroup.of hBAArrow
  refine ⟨hAB, ?_⟩
  intro h
  have hArrow : (φ (b * a)).asHom = (φ (a * b)).asHom :=
    FreeAbelianGroup.of_injective (hAB.symm.trans (h.trans hBA))
  have hEnd : φ (b * a) = φ (a * b) :=
    congrArg (fun f : y ⟶ y => CategoryTheory.End.of f) hArrow
  have hIndex : b * a = a * b := φ.injective hEnd
  have hAtZero := congrArg (fun p : G => p (0 : Fin 3)) hIndex
  exact (by decide : (b * a) (0 : Fin 3) ≠ (a * b) (0 : Fin 3)) hAtZero

/-- The module-valued functor keeps the integer and the order of both actual legs. -/
theorem module_transport_preserves_signed_original_coordinate :
    let y := SingleObj.star (Multiplicative ℤ)
    let f : y ⟶ y :=
      (SingleObj.toEnd (Multiplicative ℤ) (Multiplicative.ofAdd (2 : ℤ))).asHom
    let g : y ⟶ y :=
      (SingleObj.toEnd (Multiplicative ℤ) (Multiplicative.ofAdd (3 : ℤ))).asHom
    let F := regularPathModuleCoefficientFunctor y
    F.map g (F.map f ((-7 : ℤ) • FreeAbelianGroup.of (Multiplicative.ofAdd (0 : ℤ)))) =
      (-7 : ℤ) • FreeAbelianGroup.of (Multiplicative.ofAdd (5 : ℤ)) := by
  dsimp only
  let y := SingleObj.star (Multiplicative ℤ)
  let f : y ⟶ y :=
      (SingleObj.toEnd (Multiplicative ℤ) (Multiplicative.ofAdd (2 : ℤ))).asHom
  let g : y ⟶ y :=
      (SingleObj.toEnd (Multiplicative ℤ) (Multiplicative.ofAdd (3 : ℤ))).asHom
  let F := regularPathModuleCoefficientFunctor y
  let t := FreeAbelianGroup.of (Multiplicative.ofAdd (0 : ℤ))
  have hf : F.map f ((-7 : ℤ) • t) =
      (-7 : ℤ) • FreeAbelianGroup.of (Multiplicative.ofAdd (2 : ℤ)) := by
    have hScalar := (F.map f).hom.map_smul (-7 : ℤ) t
    have hBasis := regularPathModuleCoefficientFunctor_map_of y f
      (Multiplicative.ofAdd (0 : ℤ))
    exact hScalar.trans (congrArg (fun a => (-7 : ℤ) • a) hBasis)
  have hg : F.map g ((-7 : ℤ) • FreeAbelianGroup.of (Multiplicative.ofAdd (2 : ℤ))) =
      (-7 : ℤ) • FreeAbelianGroup.of (Multiplicative.ofAdd (5 : ℤ)) := by
    have hScalar := (F.map g).hom.map_smul (-7 : ℤ)
      (FreeAbelianGroup.of (Multiplicative.ofAdd (2 : ℤ)))
    have hBasis := regularPathModuleCoefficientFunctor_map_of y g
      (Multiplicative.ofAdd (2 : ℤ))
    exact hScalar.trans (congrArg (fun a => (-7 : ℤ) • a) hBasis)
  exact (congrArg (fun a => F.map g a) hf).trans hg

/-- The actual identity transport fixes a signed generator with a nonzero label. -/
theorem identity_transport_keeps_signed_original_generator :
    let y := SingleObj.star (Multiplicative ℤ)
    let t := (-7 : ℤ) • FreeAbelianGroup.of (Multiplicative.ofAdd (3 : ℤ))
    regularPathCoefficientTransport y (𝟙 y) t = t := by
  dsimp only
  let y := SingleObj.star (Multiplicative ℤ)
  let t := (-7 : ℤ) • FreeAbelianGroup.of (Multiplicative.ofAdd (3 : ℤ))
  exact congrArg (fun h : FreeAbelianGroup (y ⟶ y) →+ FreeAbelianGroup (y ⟶ y) => h t)
    (regularPathCoefficientTransport_id y y)

/-- The composite API agrees with both actual legs and the noncommuting coordinate. -/
theorem composite_transport_matches_ordered_noncommuting_legs :
    let G := Equiv.Perm (Fin 3)
    let y := SingleObj.star G
    let φ : G ≃* End y := SingleObj.toEnd G
    let a : G := Equiv.swap (0 : Fin 3) 1
    let b : G := Equiv.swap (1 : Fin 3) 2
    let fa : y ⟶ y := (φ a).asHom
    let fb : y ⟶ y := (φ b).asHom
    let t := FreeAbelianGroup.of (φ (1 : G)).asHom
    regularPathCoefficientTransport y (fa ≫ fb) t =
        regularPathCoefficientTransport y fb (regularPathCoefficientTransport y fa t) ∧
      regularPathCoefficientTransport y (fa ≫ fb) t =
        FreeAbelianGroup.of (φ (b * a)).asHom := by
  dsimp only
  let G := Equiv.Perm (Fin 3)
  let y := SingleObj.star G
  let φ : G ≃* End y := SingleObj.toEnd G
  let a : G := Equiv.swap (0 : Fin 3) 1
  let b : G := Equiv.swap (1 : Fin 3) 2
  let fa : y ⟶ y := (φ a).asHom
  let fb : y ⟶ y := (φ b).asHom
  let t := FreeAbelianGroup.of (φ (1 : G)).asHom
  have hComp := congrArg
    (fun h : FreeAbelianGroup (y ⟶ y) →+ FreeAbelianGroup (y ⟶ y) => h t)
    (regularPathCoefficientTransport_comp y fa fb)
  have hOrder : regularPathCoefficientTransport y fb
      (regularPathCoefficientTransport y fa t) = FreeAbelianGroup.of (φ (b * a)).asHom :=
    noncommuting_two_leg_transport_order.1
  exact ⟨hComp, hComp.trans hOrder⟩

end MathlibExtTest.NativeRegularPathCoefficients

end
