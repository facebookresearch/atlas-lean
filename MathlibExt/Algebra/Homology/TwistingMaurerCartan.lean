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
# Maurer–Cartan predicate for twisting cochains

This file packages the Maurer–Cartan equation for twisting cochains as a
reusable predicate on a bare degree-`+1` cochain, with a small bundled
interface and the zero/trivial facts used in the twisting bar–cobar
adjunction.

## Grading and sign conventions

Cohomological grading throughout, following the twisting-cochain convention: a twisting cochain is
`τ : Cochain C A 1` with `δ 1 (1 + 1) τ + conv τ τ = 0` in degree `1 + 1`,
where `δ` is the pinned `HomComplex.δ` (Conrad signs) and `conv` is the graded
convolution `μ ∘ (f ⊗ g) ∘ Δ` with the Koszul sign
`Int.negOnePow (n * i₁)`. See
`MathlibExt/RingTheory/DifferentialGraded/TwistingCochain.lean` for the full
convention map.

## Primary source

Standard reference: J.-L. Loday and B. Vallette, *Algebraic Operads*,
Grundlehren 346, Springer, 2012,
<https://doi.org/10.1007/978-3-642-30362-3>. Exact printed-section numbers
and a sign-level match against the printed text were not verified in this
environment, so none is claimed here.

## Declaration inventory

* `IsMaurerCartan`: the Maurer–Cartan equation for a degree-`+1` cochain,
  `δ 1 (1 + 1) τ + conv τ τ = 0`.
* `IsMaurerCartan.zero`: the zero cochain satisfies the equation, from the
  pinned `HomComplex.δ_zero` and `conv_zero_left`.
* `TwistingCochain.isMaurerCartan`: every twisting cochain satisfies the
  predicate on its underlying cochain, by its `maurer_cartan` field.
* `MaurerCartan`: bundled degree-`+1` cochain with the predicate, with a
  coercion to the underlying cochain and extensionality.
* `MaurerCartan.zero`: the bundled zero element.

## Nonclaims

No bar–cobar adjunction, no twisting-cochain bijection, no
conilpotence/completeness hypothesis, and no derived, Koszul, operadic,
homological (`down ℤ`), or model-categorical result is claimed. No
augmentation/coaugmentation vanishing is recorded here; that belongs to the
separate reduced-cochain module.

## Import justification

`TwistingCochain` supplies `conv`, the zero law `conv_zero_left`, and the
`TwistingCochain` structure with its `maurer_cartan` field. The
`TwistingConvolutionLaws` module (`conv_leibniz`, `convOne`) is not imported
because no Leibniz or unit lemma is needed for the predicate, coercion,
extensionality, or zero facts. `TwistingConvolutionMonoid.lean` is not imported because its public
associativity and unit laws are not consumed by this predicate-and-bundle module.
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

/-- The Maurer–Cartan equation for a degree-`+1` cochain: the pinned
differential plus the graded self-convolution vanishes in degree `1 + 1`. -/
def IsMaurerCartan (τ : HomComplex.Cochain C A 1) : Prop :=
  HomComplex.δ 1 (1 + 1) τ + conv τ τ = 0

/-- The zero degree-`+1` cochain satisfies the Maurer–Cartan equation. -/
theorem IsMaurerCartan.zero : IsMaurerCartan (R := R) (C := C) (A := A) 0 := by
  unfold IsMaurerCartan
  rw [HomComplex.δ_zero, conv_zero_left, add_zero]

/-- Every twisting cochain satisfies the Maurer–Cartan predicate on its
underlying cochain. -/
theorem TwistingCochain.isMaurerCartan
    (τ : TwistingCochain (R := R) (C := C) (A := A)) :
    IsMaurerCartan τ.tau :=
  τ.maurer_cartan

/-- Bundled Maurer–Cartan cochain: a degree-`+1` cochain with the equation. -/
structure MaurerCartan where
  /-- The underlying degree-`+1` cochain. -/
  tau : HomComplex.Cochain C A 1
  /-- The Maurer–Cartan equation. -/
  isMC : IsMaurerCartan tau

/-- Coercion to the underlying degree-`+1` cochain. -/
instance : CoeOut (MaurerCartan (R := R) (C := C) (A := A))
    (HomComplex.Cochain C A 1) :=
  ⟨MaurerCartan.tau⟩

/-- Extensionality for bundled Maurer–Cartan cochains. -/
@[ext]
theorem MaurerCartan.ext {x y : MaurerCartan (R := R) (C := C) (A := A)}
    (h : x.tau = y.tau) : x = y := by
  obtain ⟨a, ha⟩ := x
  obtain ⟨b, hb⟩ := y
  simp only at h
  subst h
  rfl

/-- The bundled zero Maurer–Cartan cochain. -/
def MaurerCartan.zero : MaurerCartan (R := R) (C := C) (A := A) :=
  ⟨0, IsMaurerCartan.zero⟩

/-- Underlying cochain of the bundled zero. -/
@[simp]
theorem MaurerCartan.zero_tau :
    (MaurerCartan.zero (R := R) (C := C) (A := A)).tau = 0 :=
  rfl

end CochainComplex
