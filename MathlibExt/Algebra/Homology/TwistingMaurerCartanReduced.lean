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

public import MathlibExt.Algebra.Homology.TwistingMaurerCartanFunctoriality
public import MathlibExt.RingTheory.DifferentialGraded.TwistingAugmentationFactor

/-!
# Reduced Maurer–Cartan bridge

This file connects the reduced-cochain predicate in
`TwistingAugmentationFactor.lean` to the bundled Maurer–Cartan API in
`TwistingMaurerCartanFunctoriality.lean` with the smallest consumer-driven
interface.

## Reduced cochains recalled

For explicit `η : 𝟙_ ⟶ C` and `ε : A ⟶ 𝟙_`, `IsReducedCochain η ε f` is the
both-sided vanishing `(ofHom η).comp f = 0 ∧ f.comp (ofHom ε) = 0` for a
homogeneous cochain `f : Cochain C A m` in arbitrary degree `m`. See
`MathlibExt/RingTheory/DifferentialGraded/TwistingAugmentationFactor.lean`.
This bridge specializes it to `x.tau` in degree `1`.
Every twisting cochain is reduced in its own maps
(`TwistingCochain.reduced`).

## Declaration inventory

* `IsReducedMaurerCartan`: a bundled `MaurerCartan` cochain is reduced when its
  underlying `tau` satisfies `IsReducedCochain η ε`.
* `IsReducedMaurerCartan.zero`: the bundled zero is reduced, from
  `IsReducedCochain.zero`.
* `IsReducedMaurerCartan.map`: reducedness is preserved by `MaurerCartan.map`
  along a comonoid map `ψ` and a monoid map `φ` under the explicit
  augmentation-compatibility equalities `η' ≫ ψ = η` and `φ ≫ ε' = ε`, from
  the pinned `ofHom_comp`, degree-zero cochain associativity, and the
  `comp_zero` / `zero_comp` laws. No new compatibility structure is
  introduced.

## Nonclaims

No Hom-complex identity/composition law, no free or cofree object, no
totalization, no bar–cobar adjunction, no conilpotence/completeness, no
derived or Koszul result, no operadic result, and no model-categorical result
is claimed. Only the predicate, its zero fact, and the augmentation-compatible
map preservation above are proved.

## Import justification

`TwistingMaurerCartanFunctoriality` supplies `MaurerCartan` with `map` and its
`map_tau` computation rule. `TwistingAugmentationFactor` supplies
`IsReducedCochain` with `IsReducedCochain.zero`. No further MathlibExt import
is needed.
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

variable {B : CochainComplex (ModuleCat R) ℤ} [MonObj B]
variable {C' : CochainComplex (ModuleCat R) ℤ} [ComonObj C']

/-- A bundled Maurer–Cartan cochain is reduced in explicit maps `η` and `ε`
when its underlying degree-`+1` cochain satisfies the existing
`IsReducedCochain` predicate. -/
def IsReducedMaurerCartan (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ))
    (x : MaurerCartan (R := R) (C := C) (A := A)) : Prop :=
  IsReducedCochain η ε x.tau

/-- The bundled zero Maurer–Cartan cochain is reduced in any explicit maps,
from `IsReducedCochain.zero`. -/
theorem IsReducedMaurerCartan.zero
    (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ)) :
    IsReducedMaurerCartan η ε (MaurerCartan.zero (R := R) (C := C) (A := A)) :=
  IsReducedCochain.zero η ε

/-- Reducedness is preserved by the bundled Maurer–Cartan map under explicit
augmentation compatibility: `η' ≫ ψ = η` on the coalgebra side and
`φ ≫ ε' = ε` on the algebra side. The proof reassociates the degree-zero
`ofHom` factors with the pinned cochain associativity lemmas, folds them with
`ofHom_comp`, rewrites with the two compatibility equalities, then closes with
the two vanishing hypotheses via `comp_zero` / `zero_comp`. -/
theorem IsReducedMaurerCartan.map {x : MaurerCartan (R := R) (C := C) (A := A)}
    {η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C}
    {ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ)}
    {η' : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C'}
    {ε' : B ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ)}
    (hx : IsReducedMaurerCartan η ε x)
    (ψ : C' ⟶ C) [IsComonHom ψ] (φ : A ⟶ B) [IsMonHom φ]
    (hψ : η' ≫ ψ = η) (hφ : φ ≫ ε' = ε) :
    IsReducedMaurerCartan η' ε' (x.map ψ φ) := by
  obtain ⟨hleft, hright⟩ := hx
  refine ⟨?_, ?_⟩
  · simp only [MaurerCartan.map_tau]
    rw [← HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain
      (HomComplex.Cochain.ofHom η') (HomComplex.Cochain.ofHom ψ),
      ← HomComplex.Cochain.ofHom_comp, hψ,
      ← HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain
      (HomComplex.Cochain.ofHom η) x.tau,
      hleft, HomComplex.Cochain.zero_comp]
  · simp only [MaurerCartan.map_tau,
      HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain,
      HomComplex.Cochain.comp_assoc_of_second_is_zero_cochain]
    rw [← HomComplex.Cochain.ofHom_comp, hφ, hright,
      HomComplex.Cochain.comp_zero]

end CochainComplex
