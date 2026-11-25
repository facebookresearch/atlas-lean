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

public import MathlibExt.RingTheory.DifferentialGraded.TwistingCochain

/-!
# Reduced cochains and augmentation annihilation for twisting cochains

This file packages the augmentation/coaugmentation
vanishing carried by twisting cochains as a reusable predicate and records how
that vanishing annihilates graded convolutions.

Primary source: no external source beyond pinned Mathlib and the
`TwistingCochain` API is used here; no match to a printed Loday–Vallette
section or sign convention is claimed.

## Reduced cochains

For explicit maps `η : 𝟙_ ⟶ C` and `ε : A ⟶ 𝟙_`, a homogeneous cochain
`f : Cochain C A m` is reduced (`IsReducedCochain η ε f`) when both outer
composites vanish: `(ofHom η).comp f = 0` and `f.comp (ofHom ε) = 0`.
Informally, `f` factors through the augmentation ideal on the right and the
coaugmentation coideal on the left; no kernel/cokernel lift is constructed
here. Degree-`+1` is the `m := 1` instantiation. Every twisting cochain is
reduced in its own maps (`TwistingCochain.reduced`), and the zero cochain is
reduced (`IsReducedCochain.zero`). Convolution preserves reducedness from
either factor alone (`IsReducedCochain.conv_of_left`,
`IsReducedCochain.conv_of_right`), via the generic `conv_precomp` /
`conv_postcomp` transport and the `conv_zero_left` / `conv_zero_right` laws.

## Declaration inventory

* `IsReducedCochain`: both-sided augmentation/coaugmentation vanishing for a
  homogeneous cochain.
* `IsReducedCochain.zero`: the zero cochain is reduced.
* `IsReducedCochain.conv_of_left`: convolution with a reduced left factor is
  reduced, from `conv_precomp`, `conv_postcomp`, and `conv_zero_left`.
* `IsReducedCochain.conv_of_right`: convolution with a reduced right factor
  is reduced, from `conv_precomp`, `conv_postcomp`, and `conv_zero_right`.
* `conv_reduced_left`: convolving the coaugmentation-side vanish composite
  `(ofHom η).comp τ` on the left gives `0`, from
  `TwistingCochain.coaug_vanish` and `conv_zero_left`.
* `conv_reduced_right`: convolving the augmentation-side vanish composite
  `τ.comp (ofHom ε)` on the right gives `0`, from
  `TwistingCochain.aug_vanish` and `conv_zero_right`.
* `TwistingCochain.reduced`: every twisting cochain is reduced in its own
  explicit coaugmentation and augmentation maps.

## Why ideal absorption holds here

Reducedness of `conv f g` follows from reducedness of either factor alone:
the outer `(ofHom η)` pushes past `ComonObj.comul` via `conv_precomp` and the
outer `(ofHom ε)` pushes past `MonObj.mul` via `conv_postcomp`, after which
the vanishing factor annihilates the convolution by `conv_zero_left` or
`conv_zero_right`. These ideal-absorption lemmas record that transport. The
annihilation lemmas below record the complementary local fact: once a vanish
composite is formed, convolution against it is zero.

## Nonclaims

* No `conv_assoc`, `conv_one_left` / `conv_one_right`, and no cochain-level
  unitor transport: those are not proved here.
* No total-level (co)augmentation map and no total-bar augmentation API.
* No twisting-cochain bijection, bar--cobar adjunction, Eilenberg--Zilber /
  Alexander--Whitney, conilpotence/completeness, derived, Koszul, operadic, or
  model-categorical result.
* No homological (`down ℤ`) API; everything is cohomological.

## Import justification

`TwistingCochain` supplies `conv`, the zero laws `conv_zero_left` and
`conv_zero_right`, and the `TwistingCochain` structure with its
`coaug_vanish` / `aug_vanish` fields. No other import is needed.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

namespace CochainComplex

variable {R : Type*} [CommRing R]
variable {C A : CochainComplex (ModuleCat R) ℤ}

variable [∀ (X₁ X₂ : GradedObject ℤ (ModuleCat R)), GradedObject.HasTensor X₁ X₂]
variable [∀ (X : ModuleCat R), PreservesColimit (Functor.empty.{0} (ModuleCat R))
  ((curriedTensor (ModuleCat R)).obj X)]
variable [∀ (X : ModuleCat R), PreservesColimit (Functor.empty.{0} (ModuleCat R))
  ((curriedTensor (ModuleCat R)).flip.obj X)]
variable [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
variable [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
variable [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

variable [MonObj A] [ComonObj C]

/-- Both-sided augmentation/coaugmentation vanishing for a homogeneous
cochain: precomposing the cochain with the explicit coaugmentation `η` and
postcomposing it with the explicit augmentation `ε` both give zero. -/
def IsReducedCochain {m : ℤ} (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ))
    (f : HomComplex.Cochain C A m) : Prop :=
  (HomComplex.Cochain.ofHom η).comp f (zero_add m) = 0 ∧
    f.comp (HomComplex.Cochain.ofHom ε) (add_zero m) = 0

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [MonObj A] [ComonObj C] in
/-- The zero homogeneous cochain is reduced in any explicit maps. -/
theorem IsReducedCochain.zero {m : ℤ}
    (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ)) :
    IsReducedCochain (m := m) η ε 0 :=
  ⟨HomComplex.Cochain.comp_zero _ _, HomComplex.Cochain.zero_comp _ _⟩

/-- Annihilation on the left: convolving the coaugmentation-side vanish
composite of a twisting cochain on the left gives zero. This is
`TwistingCochain.coaug_vanish` followed by `conv_zero_left`.
The unit comonoid is an explicit hypothesis because pinned Mathlib supplies
`ComonObj.instTensorUnit` only as a definition, deliberately not as a global
instance. -/
theorem conv_reduced_left (τ : TwistingCochain (R := R) (C := C) (A := A))
    [ComonObj (𝟙_ (CochainComplex (ModuleCat R) ℤ))]
    {n : ℤ} (g : HomComplex.Cochain (𝟙_ (CochainComplex (ModuleCat R) ℤ)) A n) :
    conv ((HomComplex.Cochain.ofHom τ.coaug).comp τ.tau (zero_add 1)) g = 0 := by
  rw [τ.coaug_vanish, conv_zero_left]

/-- Annihilation on the right: convolving the augmentation-side vanish
composite of a twisting cochain on the right gives zero. This is
`TwistingCochain.aug_vanish` followed by `conv_zero_right`
(the pinned `MonObj` unit instance needs no extra hypothesis). -/
theorem conv_reduced_right (τ : TwistingCochain (R := R) (C := C) (A := A))
    {n : ℤ} (g : HomComplex.Cochain C (𝟙_ (CochainComplex (ModuleCat R) ℤ)) n) :
    conv g (τ.tau.comp (HomComplex.Cochain.ofHom τ.aug) (add_zero 1)) = 0 := by
  rw [τ.aug_vanish, conv_zero_right]

/-- Every twisting cochain is reduced in its own explicit coaugmentation and
augmentation maps. -/
theorem TwistingCochain.reduced (τ : TwistingCochain (R := R) (C := C) (A := A)) :
    IsReducedCochain τ.coaug τ.aug τ.tau :=
  ⟨τ.coaug_vanish, τ.aug_vanish⟩

/-- Convolution with a reduced left factor is reduced: the outer maps push
through via `conv_precomp` / `conv_postcomp`, then the left vanishing
annihilates by `conv_zero_left`. -/
theorem IsReducedCochain.conv_of_left {m n : ℤ}
    {η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C}
    {ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ)}
    [ComonObj (𝟙_ (CochainComplex (ModuleCat R) ℤ))]
    [IsComonHom η] [IsMonHom ε]
    {f : HomComplex.Cochain C A m} (g : HomComplex.Cochain C A n)
    (hf : IsReducedCochain η ε f) :
    IsReducedCochain η ε (conv f g) := by
  refine ⟨?_, ?_⟩
  · rw [conv_precomp f g η, hf.1, conv_zero_left]
  · rw [conv_postcomp f g ε, hf.2, conv_zero_left]

/-- Convolution with a reduced right factor is reduced: the outer maps push
through via `conv_precomp` / `conv_postcomp`, then the right vanishing
annihilates by `conv_zero_right`. -/
theorem IsReducedCochain.conv_of_right {m n : ℤ}
    {η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C}
    {ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ)}
    [ComonObj (𝟙_ (CochainComplex (ModuleCat R) ℤ))]
    [IsComonHom η] [IsMonHom ε]
    (f : HomComplex.Cochain C A m) {g : HomComplex.Cochain C A n}
    (hg : IsReducedCochain η ε g) :
    IsReducedCochain η ε (conv f g) := by
  refine ⟨?_, ?_⟩
  · rw [conv_precomp f g η, hg.1, conv_zero_right]
  · rw [conv_postcomp f g ε, hg.2, conv_zero_right]

end CochainComplex
