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

public import MathlibExt.Algebra.Homology.TwistingMaurerCartan
public import MathlibExt.Algebra.Homology.TwistingConvolutionMonoid

/-!
# Twisted cobar differential

This file constructs the left-twisted cobar perturbation over the
graded-convolution/differential laws and Maurer–Cartan base in the imported
`TwistingMaurerCartan` and `TwistingConvolutionMonoid` modules. It defines the left-twisted
perturbation of the convolution differential on `Hom(C, A)`:

`twistedCobarDifferential τ f = δ f + τ ⋆ f`,

for a degree-`+1` cochain `τ` and `f : Cochain C A n`, landing in degree
`1 + n`. This is the Hom-side shadow of the cobar differential: its
square-zero follows from the Maurer–Cartan equation and is proved below as
`twistedCobar_sq_zero`. The full free-algebra cobar extension is not built
here (see Scope below).

## Why the cobar side first

The twisted bar side needs the cofree conilpotent coalgebra on the underlying
complex, for which no pinned API was verified. The perturbation defined here
needs only the graded convolution `conv` and the pinned differential
`δ`, so its underlying graded object (plain cochains) and differential are
statable without adding any coalgebra foundations. The full cobar (tensor
algebra on the desuspended reduced coalgebra with derivation extension) is not
built here.

## Grading and sign conventions

Cohomological grading throughout, following the graded convolution base: `τ : Cochain C A 1`,
`conv = μ ∘ (f ⊗ g) ∘ Δ` with the Koszul sign `Int.negOnePow (n * i₁)`, and
`δ` the pinned `HomComplex.δ` (Conrad signs). The result degree is stated as
`1 + n` rather than `n + 1` so the perturbation sum typechecks without
transport; `n + 1 = 1 + n` by `add_comm`, and `HomComplex.δ_v` computes
`δ n (1 + n)` as the genuine differential. Only the left twist `τ ⋆ -` is
defined here: its square produces the Maurer–Cartan left factor
`(δτ + τ ⋆ τ) ⋆ -`, matching `IsMaurerCartan` definitionally. The right twist
and graded commutator are not defined here.

## Primary source

Standard reference: J.-L. Loday and B. Vallette, *Algebraic Operads*,
Grundlehren 346, Springer, 2012,
<https://doi.org/10.1007/978-3-642-30362-3>. Exact printed-section numbers
and a sign-level match against the printed text were not verified in this
environment, so none is claimed here.

## Declaration inventory

* `twistedCobarDifferential`: left-twisted perturbation `δ f + conv τ f`.
* `twistedCobarDifferential_v`: component computation rule.
* `twistedCobarDifferential_zero`: the perturbation preserves zero.
* `twistedCobarDifferential_self_eq_zero`: a Maurer–Cartan cochain annihilates
  its own self-application (the curvature bridge used by the adjunction).
* `twistedCobar_sq_zero`: square-zero of the left-twisted differential from
  `IsMaurerCartan τ`, via `HomComplex.δ_δ`, `conv_leibniz` at degree one,
  additive convolution, `conv_assoc`, and the Maurer–Cartan equation.

## Scope

Square-zero of `twistedCobarDifferential τ` from `IsMaurerCartan τ` is proved
below as `twistedCobar_sq_zero`. The free-algebra derivation extension, the
right-twist pair, and the twisting bijection/adjunction are not built here.

## Nonclaims

No bar–cobar adjunction, no twisting-cochain bijection, no bar side, no free
or cofree (co)algebra object, no conilpotence/completeness hypothesis, and no
derived, Koszul, operadic, homological (`down ℤ`), realization, or
model-categorical result is claimed. No augmentation/coaugmentation vanishing
is recorded here.

## Import justification

`TwistingMaurerCartan` supplies `IsMaurerCartan` and, transitively through
`TwistingCochain`, the graded convolution `conv` with its zero laws.
`TwistingConvolutionMonoid` supplies `conv_assoc` and, transitively through
`TwistingConvolutionLaws`, `conv_leibniz` with the additive/scalar convolution
laws consumed by the square-zero proof.
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

/-- Left-twisted perturbation of the convolution differential: `δ f + τ ⋆ f`
for a degree-`+1` cochain `τ`. The target degree is `1 + n` so the sum needs
no transport; see the module documentation. -/
noncomputable def twistedCobarDifferential {n : ℤ}
    (τ : HomComplex.Cochain C A 1) (f : HomComplex.Cochain C A n) :
    HomComplex.Cochain C A (1 + n) :=
  HomComplex.δ n (1 + n) f + conv τ f

/-- Component computation rule for the twisted cobar differential. -/
@[simp]
theorem twistedCobarDifferential_v {n : ℤ}
    (τ : HomComplex.Cochain C A 1) (f : HomComplex.Cochain C A n)
    (p q : ℤ) (hpq : p + (1 + n) = q) :
    (twistedCobarDifferential τ f).v p q hpq =
      (HomComplex.δ n (1 + n) f).v p q hpq + (conv τ f).v p q hpq := rfl

/-- The twisted cobar differential preserves zero, from the pinned
`HomComplex.δ_zero` and `conv_zero_right`. -/
theorem twistedCobarDifferential_zero {n : ℤ}
    (τ : HomComplex.Cochain C A 1) :
    twistedCobarDifferential τ (0 : HomComplex.Cochain C A n) = 0 := by
  unfold twistedCobarDifferential
  rw [HomComplex.δ_zero, conv_zero_right, add_zero]

/-- A Maurer–Cartan cochain annihilates its own twisted cobar
self-application: `twistedCobarDifferential τ τ` is definitionally the
Maurer–Cartan left-hand side `δ 1 (1 + 1) τ + conv τ τ`. -/
theorem twistedCobarDifferential_self_eq_zero
    {τ : HomComplex.Cochain C A 1} (h : IsMaurerCartan τ) :
    twistedCobarDifferential τ τ = 0 := h

/-- Square-zero of the left-twisted cobar differential from the Maurer–Cartan
equation: two applications of `twistedCobarDifferential τ` annihilate any
cochain. The middle terms cancel by `conv_leibniz` at degree one (the sign
`(1 : ℤ).negOnePow = -1`), and the curvature factors on the left by
`conv_assoc` and `conv_add_left` before `IsMaurerCartan` and `conv_zero_left`
close the proof. Degree transports are all `by omega` at components, so no
tensor-level descent is needed. -/
theorem twistedCobar_sq_zero {n : ℤ}
    {τ : HomComplex.Cochain C A 1} (hMC : IsMaurerCartan τ)
    (f : HomComplex.Cochain C A n) :
    twistedCobarDifferential τ (twistedCobarDifferential τ f) = 0 := by
  unfold twistedCobarDifferential
  rw [HomComplex.δ_add, conv_add_right]
  have hδδ : HomComplex.δ (1 + n) (1 + (1 + n))
      (HomComplex.δ n (1 + n) f) = 0 :=
    HomComplex.δ_δ n (1 + n) (1 + (1 + n)) f
  rw [hδδ, zero_add]
  apply HomComplex.Cochain.ext
  intro r s hrs
  simp only [HomComplex.Cochain.add_v, HomComplex.Cochain.zero_v]
  have hsign : (1 : ℤ).negOnePow = -1 := by decide
  have hmn : n + 1 = 1 + n := by omega
  have hLeib := conv_leibniz τ f
  have hLeib_v := HomComplex.Cochain.congr_v hLeib r s (by omega)
  simp only [HomComplex.Cochain.add_v, HomComplex.Cochain.units_smul_v]
    at hLeib_v
  have hDeltaBridge :
      (HomComplex.δ (1 + n) (1 + (1 + n)) (conv τ f)).v r s hrs =
      (HomComplex.δ (1 + n) (1 + n + 1) (conv τ f)).v r s (by omega) := by
    have hDeg : (1 + (1 + n) : ℤ) = 1 + n + 1 := by omega
    have hgen : ∀ {b1 b2 : ℤ} (h : b1 = b2) (hpq1 : r + b1 = s)
        (hpq2 : r + b2 = s),
        (HomComplex.δ (1 + n) b1 (conv τ f)).v r s hpq1 =
        (HomComplex.δ (1 + n) b2 (conv τ f)).v r s hpq2 := by
      intro b1 b2 h hpq1 hpq2
      subst h
      rfl
    exact hgen hDeg hrs (by omega)
  have hXBridge :
      ((((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
        (tensorCochain (HomComplex.δ 1 (1 + 1) τ) f)
        (by omega : (0 : ℤ) + (1 + 1 + n) = 1 + n + 1)).comp
        (HomComplex.Cochain.ofHom (MonObj.mul (X := A)))
        (by omega : (1 + n + 1) + 0 = 1 + n + 1))).v r s (by omega) =
      (conv (HomComplex.δ 1 (1 + 1) τ) f).v r s (by omega) := by
    unfold conv
    rw [HomComplex.Cochain.comp_v _ _ _ r s s (by omega) (add_zero s),
      HomComplex.Cochain.comp_v _ _ _ r s s (by omega) (add_zero s),
      HomComplex.Cochain.comp_v _ _ _ r r s (add_zero r) (by omega),
      HomComplex.Cochain.comp_v _ _ _ r r s (add_zero r) (by omega)]
  have hYgen : ∀ {d1 d2 : ℤ} (hd : d1 = d2)
      (h1 : (0 : ℤ) + (1 + d1) = 1 + n + 1)
      (h2 : (1 + n + 1) + 0 = 1 + n + 1) (hpq1 : r + (1 + n + 1) = s)
      (hpq2 : r + (1 + d2) = s),
      ((((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
          (tensorCochain τ (HomComplex.δ n d1 f)) h1).comp
          (HomComplex.Cochain.ofHom (MonObj.mul (X := A))) h2)).v r s hpq1 =
        (conv τ (HomComplex.δ n d2 f)).v r s hpq2 := by
    intro d1 d2 hd h1 h2 hpq1 hpq2
    subst hd
    unfold conv
    rw [HomComplex.Cochain.comp_v _ _ _ r s s (by omega) (add_zero s),
      HomComplex.Cochain.comp_v _ _ _ r s s (by omega) (add_zero s),
      HomComplex.Cochain.comp_v _ _ _ r r s (add_zero r) (by omega),
      HomComplex.Cochain.comp_v _ _ _ r r s (add_zero r) (by omega)]
  have hYBridge :
      ((((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
        (tensorCochain τ (HomComplex.δ n (n + 1) f))
        (by omega : (0 : ℤ) + (1 + (n + 1)) = 1 + n + 1)).comp
        (HomComplex.Cochain.ofHom (MonObj.mul (X := A)))
        (by omega : (1 + n + 1) + 0 = 1 + n + 1))).v r s (by omega) =
      (conv τ (HomComplex.δ n (1 + n) f)).v r s hrs :=
    hYgen (d1 := n + 1) (d2 := 1 + n) (by omega) (by omega) (by omega)
      (by omega) hrs
  have hAssoc_v := HomComplex.Cochain.congr_v (conv_assoc τ τ f) r s hrs
  have hCast : ∀ {a b : ℤ} (hab : a = b)
      (z : HomComplex.Cochain C A a) (p q : ℤ) (hpq : p + b = q),
      (cast (congrArg (HomComplex.Cochain C A) hab) z).v p q hpq =
      z.v p q (by omega) := by
    intro a b hab z p q hpq
    subst hab
    rfl
  have hAdd : conv (HomComplex.δ 1 (1 + 1) τ + conv τ τ) f =
      conv (HomComplex.δ 1 (1 + 1) τ) f + conv (conv τ τ) f :=
    conv_add_left _ _ _
  have hAdd_v := HomComplex.Cochain.congr_v hAdd r s (by omega)
  simp only [HomComplex.Cochain.add_v] at hAdd_v
  have hZero := conv_zero_left (C := C) (A := A) (m := 1 + 1) (n := n) f
  have hZero_v := HomComplex.Cochain.congr_v hZero r s (by omega)
  simp only [HomComplex.Cochain.zero_v] at hZero_v
  rw [hDeltaBridge, hLeib_v, hsign, Units.neg_smul, one_smul, hXBridge,
    hYBridge, ← hAssoc_v] at ⊢
  rw [hCast (add_assoc 1 1 n) (conv (conv τ τ) f) r s hrs] at ⊢
  have hCancel :
      (conv (HomComplex.δ 1 (1 + 1) τ) f).v r s (by omega) +
          (-(conv τ (HomComplex.δ n (1 + n) f)).v r s hrs) +
        ((conv τ (HomComplex.δ n (1 + n) f)).v r s hrs +
          (conv (conv τ τ) f).v r s (by omega)) =
        (conv (HomComplex.δ 1 (1 + 1) τ) f).v r s (by omega) +
          (conv (conv τ τ) f).v r s (by omega) := by abel
  rw [hCancel, ← hAdd_v, hMC, hZero_v] at ⊢

end CochainComplex
