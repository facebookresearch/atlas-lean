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
# Twisted bar differential

This file defines the right-twisted perturbation of the convolution
differential on `Hom(C, A)`, building on the convolution and Maurer–Cartan
results:

`twistedBarDifferential τ f = δ f - (-1) ^ n • (f ⋆ τ)`,

for a degree-`+1` cochain `τ` and `f : Cochain C A n`, landing in degree
`n + 1`. This is the Hom-side shadow of the bar differential whose
square-zero is equivalent to the Maurer–Cartan equation; the cofree coalgebra
extension lies beyond this file (see Further constructions below).
It is the dual of the left-twisted cobar differential
`twistedCobarDifferential τ f = δ f + τ ⋆ f` in
`MathlibExt/Algebra/Homology/TwistingCobar.lean`, not a copy of it: the
twisting cochain stands on the right with the graded-commutator sign.

## Grading and sign conventions

Cohomological grading throughout, with `τ : Cochain C A 1`,
`conv = μ ∘ (f ⊗ g) ∘ Δ` with the Koszul sign `Int.negOnePow (n * i₁)`, and
`δ` the pinned `HomComplex.δ` (Conrad signs). The result degree is stated as
`n + 1` rather than `1 + n` so the perturbation sum typechecks without
transport; this mirrors the left-twisted cobar differential, which lands in
`1 + n` because
`conv τ f` has degree `1 + n`.

The sign is derived, not guessed, from the graded commutator on the
convolution algebra. For homogeneous `a b` of degrees `|a|`, `|b|`, the
commutator is `a ⋆ b - (-1) ^ (|a| * |b|) • (b ⋆ a)`. With `|τ| = 1` this
gives `[τ, f] = τ ⋆ f - (-1) ^ n • (f ⋆ τ)`. The left-twisted differential
keeps the `τ ⋆ -` leg; this differential keeps the right leg
`-(-1) ^ n • (- ⋆ τ)`. The
self-check fixes the sign: at `n = 1`, `-(-1) ^ 1 = +1`, so
`twistedBarDifferential τ τ` is `δ τ + τ ⋆ τ`, exactly the `IsMaurerCartan`
left-hand side. The Leibniz sign `δ (f ⋆ g) = (δ f) ⋆ g + (-1) ^ m • ...`
in the `conv_leibniz` law in `TwistingConvolutionLaws` uses the same `negOnePow`
convention.

## Declaration inventory

* `twistedBarDifferential`: right-twisted perturbation
  `δ f - (-1) ^ n • conv f τ`.
* `twistedBarDifferential_v`: component computation rule.
* `twistedBarDifferential_zero`: the perturbation preserves zero.
* `twistedBarDifferential_self_eq_zero`: a Maurer–Cartan cochain annihilates
  its own self-application (the curvature bridge used by the adjunction).
* `twistedBar_sq_zero`: square-zero of the right-twisted differential from
  `IsMaurerCartan τ`, with curvature factoring on the right as
  `f ⋆ (δτ + τ ⋆ τ)`.

## Further constructions

Square-zero of `twistedBarDifferential τ` from `IsMaurerCartan τ` is proved
below as `twistedBar_sq_zero` from the pinned `HomComplex.δ_δ`,
`conv_leibniz`, additive/scalar convolution laws, `conv_assoc`, and the
Maurer–Cartan equation, with `Int.negOnePow` signs normalized explicitly.
The cofree coderivation extension, the combined two-sided twist, and the
twisting bijection and adjunction lie beyond this Hom-level differential.

## Nonclaims

No bar–cobar adjunction, no twisting-cochain bijection, no bar side beyond
this Hom-level perturbation, no free or cofree (co)algebra object, no
conilpotence/completeness hypothesis, and no derived, Koszul, operadic,
homological (`down ℤ`), realization, or model-categorical result is claimed.
No augmentation/coaugmentation vanishing is recorded here.

## Import justification

`TwistingMaurerCartan` supplies `IsMaurerCartan` and re-exports `conv` and its
zero laws via `TwistingCochain`. The `TwistingConvolutionMonoid` module
(hence the `TwistingConvolutionLaws` convolution laws) is imported minimally
for the
square-zero proof only, supplying `conv_leibniz`, `conv_add_left/right`,
`conv_smul_left/right`, and `conv_assoc`; no unit lemma and no pinned
general-pair tensor rebuild is added here.

## Primary source

General background reference: J.-L. Loday and B. Vallette, *Algebraic Operads*,
Grundlehren 346, Springer, 2012,
<https://doi.org/10.1007/978-3-642-30362-3>. Exact printed-section numbers
and a sign-level match against the printed text were not verified in this
environment, so none is claimed here; the implementation follows only the
pinned `HomComplex` API and the convolution and Maurer–Cartan modules above.
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

/-- Right-twisted perturbation of the convolution differential:
`δ f - (-1) ^ n • (f ⋆ τ)` for a degree-`+1` cochain `τ`. The target degree
is `n + 1` so the sum needs no transport; see the module documentation for
the graded-commutator sign. -/
noncomputable def twistedBarDifferential {n : ℤ}
    (τ : HomComplex.Cochain C A 1) (f : HomComplex.Cochain C A n) :
    HomComplex.Cochain C A (n + 1) :=
  HomComplex.δ n (n + 1) f - n.negOnePow • conv f τ

/-- Component computation rule for the twisted bar differential. -/
@[simp]
theorem twistedBarDifferential_v {n : ℤ}
    (τ : HomComplex.Cochain C A 1) (f : HomComplex.Cochain C A n)
    (p q : ℤ) (hpq : p + (n + 1) = q) :
    (twistedBarDifferential τ f).v p q hpq =
      (HomComplex.δ n (n + 1) f).v p q hpq - n.negOnePow • (conv f τ).v p q hpq := rfl

/-- The twisted bar differential preserves zero, from the pinned
`HomComplex.δ_zero` and `conv_zero_left`. -/
theorem twistedBarDifferential_zero {n : ℤ}
    (τ : HomComplex.Cochain C A 1) :
    twistedBarDifferential τ (0 : HomComplex.Cochain C A n) = 0 := by
  unfold twistedBarDifferential
  rw [HomComplex.δ_zero, conv_zero_left, smul_zero, sub_zero]

/-- A Maurer–Cartan cochain annihilates its own twisted bar
self-application: at `n = 1` the sign `-(-1) ^ 1` is `+1`, so
`twistedBarDifferential τ τ` is the Maurer–Cartan left-hand side
`δ 1 (1 + 1) τ + conv τ τ`. -/
theorem twistedBarDifferential_self_eq_zero
    {τ : HomComplex.Cochain C A 1} (h : IsMaurerCartan τ) :
    twistedBarDifferential τ τ = 0 := by
  unfold twistedBarDifferential
  have hsign : (1 : ℤ).negOnePow = -1 := by decide
  rw [hsign, Units.neg_smul, one_smul, sub_neg_eq_add]
  exact h

/-- Square-zero of the right-twisted bar differential from the Maurer–Cartan
equation, with curvature factoring on the right as `f ⋆ (δτ + τ ⋆ τ)`.

For `f : Cochain C A n` and `τ : Cochain C A 1` with `IsMaurerCartan τ`,
two applications of `twistedBarDifferential` give the exact degree
`(n + 1) + 1` forced by the definition. Expanding with `HomComplex.δ_δ`,
`conv_leibniz`, additive/scalar convolution laws, and `conv_assoc`, the
`(δf ⋆ τ)` terms cancel by `(n + 1).negOnePow = -n.negOnePow`, the
`n.negOnePow ^ 2 = 1` normalization leaves `-f ⋆ (δτ) - f ⋆ (τ ⋆ τ)`,
and the Maurer–Cartan equation closes the curvature factor. -/
theorem twistedBar_sq_zero {n : ℤ}
    (τ : HomComplex.Cochain C A 1) (f : HomComplex.Cochain C A n)
    (h : IsMaurerCartan τ) :
    twistedBarDifferential τ (twistedBarDifferential τ f) = 0 := by
  unfold twistedBarDifferential
  have hδδ : HomComplex.δ (n + 1) ((n + 1) + 1)
      (HomComplex.δ n (n + 1) f) = 0 :=
    HomComplex.δ_δ n (n + 1) ((n + 1) + 1) f
  have hsucc : (n + 1).negOnePow = -n.negOnePow := Int.negOnePow_succ n
  have hsq : n.negOnePow * n.negOnePow = 1 := by
    rw [← Int.negOnePow_add]
    have h2 : n + n = 2 * n := by omega
    rw [h2, Int.negOnePow_two_mul]
  have hsq_smul : ∀ (x : HomComplex.Cochain C A ((n + 1) + 1)),
      n.negOnePow • (n.negOnePow • x) = x := by
    intro x
    rw [smul_smul, hsq, one_smul]
  have hLeib := conv_leibniz f τ
  have hAssoc := conv_assoc f τ τ
  have hdeg : (n + 1) + 1 = n + (1 + 1) := add_assoc n 1 1
  -- Component cast computation for integer degree transport, proved by
  -- `subst` on generic equality (cf. `TwistingCobar` `hCast`).
  have hcastV : ∀ {a b : ℤ} (hab : a = b) (z : HomComplex.Cochain C A a)
      (p q : ℤ) (hpq : p + b = q),
      (cast (congrArg (HomComplex.Cochain C A) hab) z).v p q hpq =
        z.v p q (by omega) := by
    intro a b hab z p q hpq
    subst hab
    rfl
  -- General cast bridges for integer degree transport, proved by `subst`
  -- on generic equality (cf. `TwistingCobar` `hCast`); applied below with
  -- the specific `hdeg` to avoid `cases` on compound integer equality.
  have hcast_add_general : ∀ {a b : ℤ} (hab : a = b)
      (x y : HomComplex.Cochain C A a),
      cast (congrArg (HomComplex.Cochain C A) hab) (x + y) =
        cast (congrArg (HomComplex.Cochain C A) hab) x +
        cast (congrArg (HomComplex.Cochain C A) hab) y := by
    intro a b hab x y
    subst hab
    rfl
  have hcast0_general : ∀ {a b : ℤ} (hab : a = b),
      cast (congrArg (HomComplex.Cochain C A) hab)
        (0 : HomComplex.Cochain C A a) =
        (0 : HomComplex.Cochain C A b) := by
    intro a b hab
    subst hab
    rfl
  -- Convolution is additive in the first argument (second fixed to `τ`);
  -- negation follows from `conv_add_left` + `conv_zero_left`.
  have hconv_neg_left : ∀ (x : HomComplex.Cochain C A (n + 1)),
      conv (-x) τ = -conv x τ := by
    intro x
    have h0 : conv (-x) τ + conv x τ = 0 := by
      rw [← conv_add_left, neg_add_cancel, conv_zero_left]
    exact eq_neg_of_add_eq_zero_left h0
  have hconv_sub_left : ∀ (a b : HomComplex.Cochain C A (n + 1)),
      conv (a - b) τ = conv a τ - conv b τ := by
    intro a b
    rw [sub_eq_add_neg, conv_add_left, hconv_neg_left, sub_eq_add_neg]
  -- The first Leibniz summand is definitionally `conv (δ f) τ`
  -- (same degree, same composites up to proof irrelevance).
  have hT1 : (((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
        (tensorCochain (HomComplex.δ n (n + 1) f) τ) (zero_add ((n + 1) + 1))).comp
        (HomComplex.Cochain.ofHom (MonObj.mul (X := A))) (add_zero ((n + 1) + 1))) =
      conv (HomComplex.δ n (n + 1) f) τ := rfl
  -- The second Leibniz summand is the `add_assoc` cast of `conv f (δ τ)`.
  have hT2 : ((((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
        (tensorCochain f (HomComplex.δ 1 (1 + 1) τ))
        (by omega : (0 : ℤ) + (n + (1 + 1)) = (n + 1) + 1)).comp
        (HomComplex.Cochain.ofHom (MonObj.mul (X := A)))
        (by omega : ((n + 1) + 1) + 0 = (n + 1) + 1)) :
        HomComplex.Cochain C A ((n + 1) + 1)) =
      cast (congrArg (HomComplex.Cochain C A) (hdeg.symm))
        (conv f (HomComplex.δ 1 (1 + 1) τ)) := by
    apply HomComplex.Cochain.ext
    intro p q hpq
    unfold conv
    rw [hcastV hdeg.symm,
      HomComplex.Cochain.comp_v, HomComplex.Cochain.comp_v,
      HomComplex.Cochain.ofHom_v, HomComplex.Cochain.ofHom_v, tensorCochain_v,
      HomComplex.Cochain.comp_v, HomComplex.Cochain.comp_v,
      HomComplex.Cochain.ofHom_v, HomComplex.Cochain.ofHom_v, tensorCochain_v]
    all_goals omega
  -- Leibniz in curvature-ready form: `δ(f ⋆ τ)` with the second leg cast.
  have hLeib_expand : HomComplex.δ (n + 1) ((n + 1) + 1) (conv f τ) =
      conv (HomComplex.δ n (n + 1) f) τ +
        n.negOnePow • cast
          (congrArg (HomComplex.Cochain C A) (hdeg.symm))
          (conv f (HomComplex.δ 1 (1 + 1) τ)) := by
    rw [hLeib, hT1, hT2]
  -- Associativity in the goal orientation: `(f ⋆ τ) ⋆ τ` is the cast of
  -- `f ⋆ (τ ⋆ τ)` backwards; derive the reverse direction by cast.
  have hAssoc_rev : conv (conv f τ) τ =
      cast (congrArg (HomComplex.Cochain C A) (hdeg.symm))
        (conv f (conv τ τ)) := by
    rw [← hAssoc]
    simp
  -- Expand the outer differential and the outer convolution.
  have hδ_outer : HomComplex.δ (n + 1) ((n + 1) + 1)
        (HomComplex.δ n (n + 1) f - n.negOnePow • conv f τ) =
        HomComplex.δ (n + 1) ((n + 1) + 1) (HomComplex.δ n (n + 1) f) -
          n.negOnePow • HomComplex.δ (n + 1) ((n + 1) + 1) (conv f τ) := by
    rw [HomComplex.δ_sub, HomComplex.δ_units_smul]
  have hconv_outer : conv
        (HomComplex.δ n (n + 1) f - n.negOnePow • conv f τ) τ =
        conv (HomComplex.δ n (n + 1) f) τ -
          n.negOnePow • conv (conv f τ) τ := by
    rw [hconv_sub_left, conv_smul_left]
  -- Cast distributes over `Add` by general cast; keep everything in
  -- the goal degree `((n + 1) + 1)` and factor the right curvature.
  have hcast_add : ∀ (a b : HomComplex.Cochain C A (n + (1 + 1))),
      cast (congrArg (HomComplex.Cochain C A) (hdeg.symm)) (a + b) =
        cast (congrArg (HomComplex.Cochain C A) (hdeg.symm)) a +
          cast (congrArg (HomComplex.Cochain C A) (hdeg.symm)) b := by
    intro a b
    exact hcast_add_general hdeg.symm a b
  have hcurv : conv f (HomComplex.δ 1 (1 + 1) τ) + conv f (conv τ τ) =
      conv f (HomComplex.δ 1 (1 + 1) τ + conv τ τ) := by
    rw [conv_add_right]
  have hMC0 : conv f (HomComplex.δ 1 (1 + 1) τ + conv τ τ) = 0 := by
    have h0 : HomComplex.δ 1 (1 + 1) τ + conv τ τ = 0 := h
    rw [h0, conv_zero_right]
  -- Assemble: δδ vanishes, `(δf ⋆ τ)` cancels by `hsucc`, `s_n^2 = 1`
  -- leaves the right curvature `-f ⋆ (δτ + τ ⋆ τ)`, which is zero by `h`.
  calc HomComplex.δ (n + 1) ((n + 1) + 1)
          (HomComplex.δ n (n + 1) f - n.negOnePow • conv f τ) -
          (n + 1).negOnePow • conv
            (HomComplex.δ n (n + 1) f - n.negOnePow • conv f τ) τ
        = (0 - n.negOnePow •
            (conv (HomComplex.δ n (n + 1) f) τ +
              n.negOnePow • cast
                (congrArg (HomComplex.Cochain C A) (hdeg.symm))
                (conv f (HomComplex.δ 1 (1 + 1) τ)))) -
          (n + 1).negOnePow •
            (conv (HomComplex.δ n (n + 1) f) τ -
              n.negOnePow • conv (conv f τ) τ) := by
          rw [hδ_outer, hδδ, hLeib_expand, hconv_outer]
      _ = -(cast (congrArg (HomComplex.Cochain C A) (hdeg.symm))
              (conv f (HomComplex.δ 1 (1 + 1) τ))) -
            (cast (congrArg (HomComplex.Cochain C A) (hdeg.symm))
              (conv f (conv τ τ))) := by
          rw [hsucc, Units.neg_smul, hAssoc_rev]
          simp only [zero_sub, smul_add, smul_sub, sub_neg_eq_add,
            hsq_smul]
          abel
      _ = -(cast (congrArg (HomComplex.Cochain C A) (hdeg.symm))
              (conv f (HomComplex.δ 1 (1 + 1) τ)) +
            cast (congrArg (HomComplex.Cochain C A) (hdeg.symm))
              (conv f (conv τ τ))) := by
          abel
      _ = -(cast (congrArg (HomComplex.Cochain C A) (hdeg.symm))
              (conv f (HomComplex.δ 1 (1 + 1) τ) +
                conv f (conv τ τ))) := by
          rw [hcast_add]
      _ = -(cast (congrArg (HomComplex.Cochain C A) (hdeg.symm))
              (conv f (HomComplex.δ 1 (1 + 1) τ + conv τ τ))) := by
          rw [hcurv]
      _ = 0 := by
          rw [hMC0]
          have hcast0 : cast
              (congrArg (HomComplex.Cochain C A) (hdeg.symm))
              (0 : HomComplex.Cochain C A (n + (1 + 1))) =
              (0 : HomComplex.Cochain C A ((n + 1) + 1)) := by
            exact hcast0_general hdeg.symm
          rw [hcast0, neg_zero]

end CochainComplex
