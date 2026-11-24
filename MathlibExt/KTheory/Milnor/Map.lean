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

public import MathlibExt.KTheory.Milnor.Basic

/-!
# Milnor K-ring functoriality

Given a ring homomorphism `f : F →+* K` between fields, we construct the induced
homomorphism between total Milnor K-rings. On symbols it sends
`{a₁, …, aₙ}` to `{f a₁, …, f aₙ}`. The construction lifts `f` to the tensor
algebras `T(Fˣ) → T(Kˣ)` and checks that the Steinberg relation `a ⊗ (1-a)`
maps to zero in `MilnorKRing K`, hence descends to the quotient.

This gives the functoriality of `MilnorKRing` with respect to field homomorphisms
and provides the computational rule for the image of symbols.
-/

@[expose] public section

open TensorAlgebra
open scoped TensorAlgebra

namespace MilnorK

variable {F K : Type*} [Field F] [Field K]

namespace MilnorKRing

/-- The additive homomorphism `Additive Fˣ →+ Additive Kˣ` induced by a field
    homomorphism `f`, sending `ofMul u` to `ofMul (f u)`. -/
def unitsAddHom (f : F →+* K) : Additive Fˣ →+ Additive Kˣ where
  toFun a := Additive.ofMul (Units.map f.toMonoidHom (Additive.toMul a))
  map_zero' := by simp
  map_add' := by intro x y; simp [map_mul]

/-- The `ℤ`-algebra homomorphism between tensor rings `T(Fˣ) →ₐ[ℤ] T(Kˣ)` induced by
    a field homomorphism, obtained by lifting `unitsAddHom`. -/
noncomputable def tensorMapAlg (f : F →+* K) : TensorRing F →ₐ[ℤ] TensorRing K :=
  TensorAlgebra.lift ℤ ((TensorAlgebra.ι ℤ).comp (unitsAddHom f).toIntLinearMap)

/-- The ring homomorphism between tensor rings `T(Fˣ) →+* T(Kˣ)` induced by a field
    homomorphism, underlying `tensorMapAlg`. -/
noncomputable def tensorMap (f : F →+* K) : TensorRing F →+* TensorRing K :=
  (tensorMapAlg f).toRingHom

/-- The `ℤ`-algebra tensor lift sends a generator `ι a` to `ι (unitsAddHom f a)`. -/
@[simp]
lemma tensorMapAlg_ι (f : F →+* K) (a : Additive Fˣ) :
    tensorMapAlg f (TensorAlgebra.ι ℤ a) = TensorAlgebra.ι ℤ (unitsAddHom f a) := by
  simp [tensorMapAlg, TensorAlgebra.lift_ι_apply]

/-- The ring-level tensor lift sends a unit generator `ι u` to `ι (f u)`. -/
@[simp]
lemma tensorMap_ι (f : F →+* K) (u : Fˣ) :
    tensorMap f (TensorAlgebra.ι ℤ (Additive.ofMul u)) =
      TensorAlgebra.ι ℤ (Additive.ofMul (Units.map f.toMonoidHom u)) := by
  simp [tensorMap, tensorMapAlg_ι, unitsAddHom]

/-- The composite `mk K ∘ tensorMap f` kills Steinberg tensors `a ⊗ (1 - a)` for
    `a ≠ 0, 1`, hence respects the defining relations of `MilnorKRing F`. This is the
    key step for descending `tensorMap` to the Milnor K-ring quotient. -/
lemma tensorMap_steinberg (f : F →+* K) (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    ((mk K).comp (tensorMap f))
      (TensorAlgebra.ι ℤ (Additive.ofMul (Units.mk0 a ha0)) *
        TensorAlgebra.ι ℤ (Additive.ofMul (Units.mk0 (1 - a) (sub_ne_zero.mpr ha1.symm)))) = 0 := by
  simp only [RingHom.comp_apply, map_mul, tensorMap_ι]
  have hfa0 : f a ≠ 0 := by intro h; apply ha0; exact f.map_eq_zero_iff.mp h
  have hfa1 : f a ≠ 1 := by intro h; apply ha1; apply f.injective; simpa using h
  have hmap_a : Units.map f.toMonoidHom (Units.mk0 a ha0) = Units.mk0 (f a) hfa0 := by ext; simp
  have hmap_sub : Units.map f.toMonoidHom (Units.mk0 (1 - a) (sub_ne_zero.mpr ha1.symm)) =
      Units.mk0 (1 - f a) (sub_ne_zero.mpr hfa1.symm) := by ext; simp [map_sub]
  simp only [hmap_a, hmap_sub]
  change mk K (TensorAlgebra.ι ℤ (Additive.ofMul (Units.mk0 (f a) hfa0)) *
      TensorAlgebra.ι ℤ (Additive.ofMul (Units.mk0 (1 - f a) _))) = 0
  rw [map_mul]
  change symbol K (Units.mk0 (f a) hfa0) * symbol K (Units.mk0 (1 - f a) _) = 0
  exact steinberg_zero K (f a) hfa0 hfa1

/-- The graded ring homomorphism `MilnorKRing F →+* MilnorKRing K` induced by a field
    homomorphism `f`, sending a symbol `{a₁,…,aₙ}` to `{f a₁,…,f aₙ}` via the
    Steinberg-respecting tensor lift. -/
noncomputable def map (f : F →+* K) : MilnorKRing F →+* MilnorKRing K :=
  MilnorKRing.lift F ((mk K).comp (tensorMap f)) (fun a ha0 ha1 => tensorMap_steinberg f a ha0 ha1)

/-- The Milnor K-ring map commutes with the quotient projection `mk`:
    `map f (mk x) = mk (tensorMap f x)`. -/
@[simp]
lemma map_mk (f : F →+* K) (x : TensorRing F) :
    map f (mk F x) = mk K (tensorMap f x) :=
  MilnorKRing.lift_mk F ((mk K).comp (tensorMap f)) _ x

/-- The induced Milnor K-ring map sends a degree-one symbol `{u}` to `{f u}`. This is
    the degree-one shadow of the functoriality `Fˣ → Kˣ` on units. -/
@[simp]
lemma map_symbol (f : F →+* K) (u : Fˣ) :
    map f (symbol F u) = symbol K (Units.map f.toMonoidHom u) := by
  unfold symbol
  rw [map_mk, tensorMap_ι]

end MilnorKRing

end MilnorK
