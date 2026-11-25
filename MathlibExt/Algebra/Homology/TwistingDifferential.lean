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

public import MathlibExt.Algebra.Homology.TwistingBar
public import MathlibExt.Algebra.Homology.TwistingCobar

/-!
# Hom-level two-sided twisting differential

This file defines the Hom-level two-sided twisting differential on `Hom(C, A)`,
building on the bar square-zero, cobar square-zero, convolution, and
Maurer-Cartan results. It defines the cohomological graded-commutator
perturbation on
`Hom(C, A)`:

`twistedDifferential τ f = δ f + τ ⋆ f - (-1) ^ n • (f ⋆ τ)`,

for a degree-`+1` cochain `τ` and `f : Cochain C A n`, landing in degree
`n + 1`. The left `τ ⋆ f` leg has degree `1 + n` and is transported once by
an explicit cast; the remaining legs already land in `n + 1`. This combines
the right-twisted bar differential `twistedBarDifferential` with the left-twisted
cobar differential `twistedCobarDifferential`, preserving both sign conventions
exactly.

## Grading and sign conventions

Cohomological grading throughout, following the bar/cobar differentials:
`τ : Cochain C A 1`, `conv = μ ∘ (f ⊗ g) ∘ Δ` with the Koszul sign
`Int.negOnePow (n * i₁)`, and `δ` the pinned `HomComplex.δ` (Conrad signs).
The result degree is `n + 1` so only the left leg needs transport via
`add_comm 1 n`. The sign follows the graded commutator
`[τ, f] = τ ⋆ f - (-1) ^ n • (f ⋆ τ)` with `|τ| = 1`.

At `n = 1` the two twist legs add rather than cancel: `δ τ + τ ⋆ τ + τ ⋆ τ`
up to the shared sign normalization. Hence no self-zero lemma is stated here;
the bar and cobar differentials separately retain their own self-zero facts.

## Primary source

Standard general reference: J.-L. Loday and B. Vallette, *Algebraic Operads*,
Grundlehren 346, Springer, 2012,
<https://doi.org/10.1007/978-3-642-30362-3>. Exact printed-section numbers
and a sign-level match against the printed text were not verified in this
environment, so none is claimed here. The signs and degrees follow
the `TwistingBar`/`TwistingCobar` differentials and `HomComplex.δ`.

## Declaration inventory

* `twistedDifferential`: two-sided perturbation
  `δ f + cast (τ ⋆ f) - (-1) ^ n • (f ⋆ τ)`.
* `twistedDifferential_v`: component computation rule.
* `twistedDifferential_zero`: the perturbation preserves zero.
* `twistedDifferential_sq_zero`: square-zero from `IsMaurerCartan τ`,
  with left curvature factoring as `(δτ + τ ⋆ τ) ⋆ f` and right curvature as
  `f ⋆ (δτ + τ ⋆ τ)`, plus cross cancellation of the mixed
  `(τ ⋆ f) ⋆ τ` terms by associativity and `(n + 1).negOnePow = -n.negOnePow`.

## Further constructions

The free and cofree extensions, twisting bijection and adjunction,
totalization, derived and Koszul duality, operadic, model-categorical, and
realization constructions lie beyond this file.

## Nonclaims

No adjunction, no twisting-cochain bijection, no free or cofree object, no
conilpotence/completeness hypothesis, no totalization, no derived/Koszul,
no operadic, no model-categorical, and no realization result is claimed here.

## Import justification

`TwistingBar` supplies the right-leg sign, the `n + 1` degree convention, and
the right-curvature square-zero route. `TwistingCobar` supplies the left-leg
perturbation and the left-curvature route. The convolution laws and
associativity arrive transitively for the combined square-zero proof; no unit
lemma and no new tensor rebuild is added here.

## Context

This file combines the right-twisted differential in `TwistingBar.lean` and
the left-twisted differential in `TwistingCobar.lean`, preserving sign and
composition conventions.
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

/-- Two-sided twisting perturbation of the convolution differential:
`δ f + τ ⋆ f - (-1) ^ n • (f ⋆ τ)` for a degree-`+1` cochain `τ`.
The left leg has degree `1 + n` and is cast once to `n + 1`; see the module
documentation for the graded-commutator sign. -/
noncomputable def twistedDifferential {n : ℤ}
    (τ : HomComplex.Cochain C A 1) (f : HomComplex.Cochain C A n) :
    HomComplex.Cochain C A (n + 1) :=
  HomComplex.δ n (n + 1) f +
    cast (congrArg (HomComplex.Cochain C A) (add_comm (1 : ℤ) n)) (conv τ f) -
    n.negOnePow • conv f τ

/-- Component computation rule for the two-sided twisting differential. -/
@[simp]
theorem twistedDifferential_v {n : ℤ}
    (τ : HomComplex.Cochain C A 1) (f : HomComplex.Cochain C A n)
    (p q : ℤ) (hpq : p + (n + 1) = q) :
    (twistedDifferential τ f).v p q hpq =
      (HomComplex.δ n (n + 1) f).v p q hpq +
        (cast (congrArg (HomComplex.Cochain C A) (add_comm (1 : ℤ) n))
          (conv τ f)).v p q hpq -
        n.negOnePow • (conv f τ).v p q hpq := rfl

/-- The two-sided twisting differential preserves zero, from the pinned
`HomComplex.δ_zero` and `conv_zero_left/right`. -/
theorem twistedDifferential_zero {n : ℤ}
    (τ : HomComplex.Cochain C A 1) :
    twistedDifferential τ (0 : HomComplex.Cochain C A n) = 0 := by
  unfold twistedDifferential
  rw [HomComplex.δ_zero, conv_zero_right, conv_zero_left]
  have hcast0_general : ∀ {a b : ℤ} (hab : a = b),
      cast (congrArg (HomComplex.Cochain C A) hab)
        (0 : HomComplex.Cochain C A a) =
        (0 : HomComplex.Cochain C A b) := by
    intro a b hab
    subst hab
    rfl
  have hcast0 : cast
      (congrArg (HomComplex.Cochain C A) (add_comm (1 : ℤ) n))
      (0 : HomComplex.Cochain C A (1 + n)) = 0 := by
    exact hcast0_general (add_comm (1 : ℤ) n)
  rw [hcast0, smul_zero, add_zero, sub_zero]

/-- Square-zero of the two-sided twisting differential from the Maurer-Cartan
equation.

For `f : Cochain C A n` and `τ : Cochain C A 1` with `IsMaurerCartan τ`,
two applications of `twistedDifferential` give degree `(n + 1) + 1`.
Expanding with `HomComplex.δ_δ`, `conv_leibniz` on both legs,
additive/scalar convolution laws, and `conv_assoc`, the `δf ⋆ τ` and
`τ ⋆ δf` pairs cancel by `(n + 1).negOnePow = -n.negOnePow`, the mixed
`(τ ⋆ f) ⋆ τ` terms cancel by associativity, `n.negOnePow ^ 2 = 1` leaves
the two curvatures `(δτ + τ ⋆ τ) ⋆ f` and `f ⋆ (δτ + τ ⋆ τ)`, and the
Maurer-Cartan equation closes both. -/
theorem twistedDifferential_sq_zero {n : ℤ}
    (τ : HomComplex.Cochain C A 1) (f : HomComplex.Cochain C A n)
    (h : IsMaurerCartan τ) :
    twistedDifferential τ (twistedDifferential τ f) = 0 := by
  unfold twistedDifferential
  have h1 : (1 : ℤ) + n = n + 1 := add_comm 1 n
  have h2 : (1 : ℤ) + (n + 1) = (n + 1) + 1 := add_comm 1 (n + 1)
  have hdeg : (n + 1) + 1 = n + (1 + 1) := add_assoc n 1 1
  have hsucc : (n + 1).negOnePow = -n.negOnePow := Int.negOnePow_succ n
  have hsq : n.negOnePow * n.negOnePow = 1 := by
    rw [← Int.negOnePow_add]
    have h2n : n + n = 2 * n := by omega
    rw [h2n, Int.negOnePow_two_mul]
  have hsq_smul : ∀ (x : HomComplex.Cochain C A ((n + 1) + 1)),
      n.negOnePow • (n.negOnePow • x) = x := by
    intro x
    rw [smul_smul, hsq, one_smul]
  have hδδ : HomComplex.δ (n + 1) ((n + 1) + 1)
      (HomComplex.δ n (n + 1) f) = 0 :=
    HomComplex.δ_δ n (n + 1) ((n + 1) + 1) f
  have hLeibR := conv_leibniz f τ
  have hLeibL := conv_leibniz τ f
  have hAssocR := conv_assoc f τ τ
  have hAssocL := conv_assoc τ τ f
  have hAssocM := conv_assoc τ f τ
  -- Convolution negates and subtracts in each factor, from additivity.
  -- Specialized to the actually-used `(n + 1)` / `τ` instantiation to avoid
  -- heartbeat blowups from general `{m p}` unification through casts.
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
  have hconv_neg_right : ∀ (y : HomComplex.Cochain C A (n + 1)),
      conv τ (-y) = -conv τ y := by
    intro y
    have h0 : conv τ (-y) + conv τ y = 0 := by
      rw [← conv_add_right, neg_add_cancel, conv_zero_right]
    exact eq_neg_of_add_eq_zero_left h0
  have hconv_sub_right : ∀ (a b : HomComplex.Cochain C A (n + 1)),
      conv τ (a - b) = conv τ a - conv τ b := by
    intro a b
    rw [sub_eq_add_neg, conv_add_right, hconv_neg_right, sub_eq_add_neg]
  -- Casts distribute over sums by cases via `cases; rfl`.
  have hcast_add : ∀ {a b : ℤ} (hab : a = b)
      (x y : HomComplex.Cochain C A a),
      cast (congrArg (HomComplex.Cochain C A) hab) (x + y) =
        cast (congrArg (HomComplex.Cochain C A) hab) x +
          cast (congrArg (HomComplex.Cochain C A) hab) y := by
    intro a b hab x y
    cases hab
    rfl
  have hcast_sub : ∀ {a b : ℤ} (hab : a = b)
      (x y : HomComplex.Cochain C A a),
      cast (congrArg (HomComplex.Cochain C A) hab) (x - y) =
        cast (congrArg (HomComplex.Cochain C A) hab) x -
          cast (congrArg (HomComplex.Cochain C A) hab) y := by
    intro a b hab x y
    cases hab
    rfl
  have hcast_smul : ∀ {a b : ℤ} (hab : a = b) (k : ℤˣ)
      (x : HomComplex.Cochain C A a),
      cast (congrArg (HomComplex.Cochain C A) hab) (k • x) =
        k • cast (congrArg (HomComplex.Cochain C A) hab) x := by
    intro a b hab k x
    cases hab
    rfl
  have hcast_cast : ∀ {a b c : ℤ} (h1 : a = b) (h2 : b = c)
      (x : HomComplex.Cochain C A a),
      cast (congrArg (HomComplex.Cochain C A) h2)
        (cast (congrArg (HomComplex.Cochain C A) h1) x) =
        cast (congrArg (HomComplex.Cochain C A) (Eq.trans h1 h2)) x := by
    intro a b c h1 h2 x
    cases h1
    cases h2
    rfl
  -- Inner left leg as an ordinary cochain in degree `n + 1`.
  -- General `δ`-cast bridge proved by `subst` on generic equality, applied
  -- with the specific `h1` to avoid `cases` on compound integer equality.
  have hLc_general : ∀ {a b : ℤ} (hab : a = b)
      (g : HomComplex.Cochain C A a),
      HomComplex.δ b (b + 1)
        (cast (congrArg (HomComplex.Cochain C A) hab) g) =
        cast (congrArg (HomComplex.Cochain C A) (congrArg (· + 1) hab))
          (HomComplex.δ a (a + 1) g) := by
    intro a b hab g
    subst hab
    rfl
  have hLc : ∀ (g : HomComplex.Cochain C A (1 + n)),
      HomComplex.δ (n + 1) ((n + 1) + 1)
        (cast (congrArg (HomComplex.Cochain C A) h1) g) =
        cast (congrArg (HomComplex.Cochain C A) (congrArg (· + 1) h1))
          (HomComplex.δ (1 + n) ((1 + n) + 1) g) := by
    intro g
    exact hLc_general h1 g
  -- Outer expansions of `δ`, left convolution, and right convolution.
  have hδ_outer : HomComplex.δ (n + 1) ((n + 1) + 1)
        (HomComplex.δ n (n + 1) f +
          cast (congrArg (HomComplex.Cochain C A) h1) (conv τ f) -
          n.negOnePow • conv f τ) =
        HomComplex.δ (n + 1) ((n + 1) + 1) (HomComplex.δ n (n + 1) f) +
          HomComplex.δ (n + 1) ((n + 1) + 1)
            (cast (congrArg (HomComplex.Cochain C A) h1) (conv τ f)) -
          n.negOnePow • HomComplex.δ (n + 1) ((n + 1) + 1) (conv f τ) := by
    rw [HomComplex.δ_sub, HomComplex.δ_add, HomComplex.δ_units_smul]
  have hconvL_outer : conv τ
        (HomComplex.δ n (n + 1) f +
          cast (congrArg (HomComplex.Cochain C A) h1) (conv τ f) -
          n.negOnePow • conv f τ) =
        conv τ (HomComplex.δ n (n + 1) f) +
          conv τ (cast (congrArg (HomComplex.Cochain C A) h1) (conv τ f)) -
          n.negOnePow • conv τ (conv f τ) := by
    rw [hconv_sub_right, conv_add_right, conv_smul_right]
  have hconvR_outer : conv
        (HomComplex.δ n (n + 1) f +
          cast (congrArg (HomComplex.Cochain C A) h1) (conv τ f) -
          n.negOnePow • conv f τ) τ =
        conv (HomComplex.δ n (n + 1) f) τ +
          conv (cast (congrArg (HomComplex.Cochain C A) h1) (conv τ f)) τ -
          n.negOnePow • conv (conv f τ) τ := by
    rw [hconv_sub_left, conv_add_left, conv_smul_left]
  -- Leibniz in curvature-ready cochain form for the two-sided differential.
  have hT1R : (((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
        (tensorCochain (HomComplex.δ n (n + 1) f) τ) (zero_add ((n + 1) + 1))).comp
        (HomComplex.Cochain.ofHom (MonObj.mul (X := A))) (add_zero ((n + 1) + 1))) =
      conv (HomComplex.δ n (n + 1) f) τ := rfl
  -- Component transport for degree casts, following green Cobar `hgen`/`hYgen`
  -- and `TwistingConvolutionMonoid` `cochain_cast_v`: generic variable-equality
  -- `subst` bridge, applied with specific equalities below.
  have hcast_v : ∀ {a b : ℤ} (hab : a = b)
      (z : HomComplex.Cochain C A a) (r s : ℤ) (hrs : r + b = s),
      (cast (congrArg (HomComplex.Cochain C A) hab) z).v r s hrs =
        z.v r s (by omega) := by
    intro a b hab z r s hrs
    subst hab
    rfl
  have hT2R : ((((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
        (tensorCochain f (HomComplex.δ 1 (1 + 1) τ))
        (by omega : (0 : ℤ) + (n + (1 + 1)) = (n + 1) + 1)).comp
        (HomComplex.Cochain.ofHom (MonObj.mul (X := A)))
        (by omega : ((n + 1) + 1) + 0 = (n + 1) + 1)) :
        HomComplex.Cochain C A ((n + 1) + 1)) =
      cast (congrArg (HomComplex.Cochain C A) (hdeg.symm))
        (conv f (HomComplex.δ 1 (1 + 1) τ)) := by
    apply HomComplex.Cochain.ext
    intro r s hrs
    rw [hcast_v hdeg.symm (conv f (HomComplex.δ 1 (1 + 1) τ)) r s hrs]
    unfold conv
    rw [HomComplex.Cochain.comp_v _ _ _ r s s (by omega) (add_zero s),
      HomComplex.Cochain.comp_v _ _ _ r r s (add_zero r) (by omega),
      HomComplex.Cochain.comp_v _ _ _ r s s (by omega) (add_zero s),
      HomComplex.Cochain.comp_v _ _ _ r r s (add_zero r) (by omega)]
  have hLeibR_expand : HomComplex.δ (n + 1) ((n + 1) + 1) (conv f τ) =
      conv (HomComplex.δ n (n + 1) f) τ +
        n.negOnePow • cast
          (congrArg (HomComplex.Cochain C A) (hdeg.symm))
          (conv f (HomComplex.δ 1 (1 + 1) τ)) := by
    rw [hLeibR, hT1R, hT2R]
  have hAssocR_rev : conv (conv f τ) τ =
      cast (congrArg (HomComplex.Cochain C A) (hdeg.symm))
        (conv f (conv τ τ)) := by
    apply HomComplex.Cochain.ext
    intro r s hrs
    rw [hcast_v hdeg.symm (conv f (conv τ τ)) r s hrs]
    have hA := HomComplex.Cochain.congr_v hAssocR r s
      (by omega : r + (n + (1 + 1)) = s)
    rw [hcast_v (add_assoc n 1 1) (conv (conv f τ) τ) r s
      (by omega : r + (n + (1 + 1)) = s)] at hA
    exact hA
  -- Left Leibniz with the `1 + n` to `n + 1` bridge folded in.
  -- Keeps the `(1 : ℤ).negOnePow` scalar for the final `simp` + `abel`
  -- normalization.
  have hLeibL_bridge : HomComplex.δ (n + 1) ((n + 1) + 1)
        (cast (congrArg (HomComplex.Cochain C A) h1) (conv τ f)) =
        cast (congrArg (HomComplex.Cochain C A) (show (1 + 1) + n = (n + 1) + 1 by omega))
          (conv (HomComplex.δ 1 (1 + 1) τ) f) +
        (1 : ℤ).negOnePow • cast
          (congrArg (HomComplex.Cochain C A) (show 1 + (n + 1) = (n + 1) + 1 by omega))
          (conv τ (HomComplex.δ n (n + 1) f)) := by
    rw [hLc, hLeibL, hcast_add (congrArg (· + 1) h1),
      hcast_smul (congrArg (· + 1) h1)]
    have hA : ((((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
        (tensorCochain (HomComplex.δ 1 (1 + 1) τ) f)
        (by omega : (0 : ℤ) + ((1 + 1) + n) = (1 + n) + 1)).comp
        (HomComplex.Cochain.ofHom (MonObj.mul (X := A)))
        (by omega : ((1 + n) + 1) + 0 = (1 + n) + 1)) :
        HomComplex.Cochain C A ((1 + n) + 1)) =
      cast (congrArg (HomComplex.Cochain C A) (show (1 + 1) + n = (1 + n) + 1 by omega))
        (conv (HomComplex.δ 1 (1 + 1) τ) f) := by
      apply HomComplex.Cochain.ext
      intro r s hrs
      rw [hcast_v (show (1 + 1) + n = (1 + n) + 1 by omega)
        (conv (HomComplex.δ 1 (1 + 1) τ) f) r s hrs]
      unfold conv
      rw [HomComplex.Cochain.comp_v _ _ _ r s s (by omega) (add_zero s),
        HomComplex.Cochain.comp_v _ _ _ r r s (add_zero r) (by omega),
        HomComplex.Cochain.comp_v _ _ _ r s s (by omega) (add_zero s),
        HomComplex.Cochain.comp_v _ _ _ r r s (add_zero r) (by omega)]
    have hB : ((((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
        (tensorCochain τ (HomComplex.δ n (n + 1) f))
        (by omega : (0 : ℤ) + (1 + (n + 1)) = (1 + n) + 1)).comp
        (HomComplex.Cochain.ofHom (MonObj.mul (X := A)))
        (by omega : ((1 + n) + 1) + 0 = (1 + n) + 1)) :
        HomComplex.Cochain C A ((1 + n) + 1)) =
      cast (congrArg (HomComplex.Cochain C A) (show 1 + (n + 1) = (1 + n) + 1 by omega))
        (conv τ (HomComplex.δ n (n + 1) f)) := by
      apply HomComplex.Cochain.ext
      intro r s hrs
      rw [hcast_v (show 1 + (n + 1) = (1 + n) + 1 by omega)
        (conv τ (HomComplex.δ n (n + 1) f)) r s hrs]
      unfold conv
      rw [HomComplex.Cochain.comp_v _ _ _ r s s (by omega) (add_zero s),
        HomComplex.Cochain.comp_v _ _ _ r r s (add_zero r) (by omega),
        HomComplex.Cochain.comp_v _ _ _ r s s (by omega) (add_zero s),
        HomComplex.Cochain.comp_v _ _ _ r r s (add_zero r) (by omega)]
    rw [hA, hB,
      hcast_cast (show (1 + 1) + n = (1 + n) + 1 by omega) (congrArg (· + 1) h1) _,
      hcast_cast (show 1 + (n + 1) = (1 + n) + 1 by omega) (congrArg (· + 1) h1) _]
  -- Curvature factors on each side.
  have hMC0R : conv f (HomComplex.δ 1 (1 + 1) τ + conv τ τ) = 0 := by
    have h0 : HomComplex.δ 1 (1 + 1) τ + conv τ τ = 0 := h
    rw [h0, conv_zero_right]
  have hMC0L : conv (HomComplex.δ 1 (1 + 1) τ + conv τ τ) f = 0 := by
    have h0 : HomComplex.δ 1 (1 + 1) τ + conv τ τ = 0 := h
    rw [h0, conv_zero_left]
  -- The mixed middle associativity cancels the cross terms.
  have hMid : conv τ (conv f τ) =
      cast (congrArg (HomComplex.Cochain C A) (show (1 + n) + 1 = 1 + (n + 1) by omega))
        (conv (conv τ f) τ) := by
    apply HomComplex.Cochain.ext
    intro r s hrs
    rw [hcast_v (show (1 + n) + 1 = 1 + (n + 1) by omega)
      (conv (conv τ f) τ) r s hrs]
    have hA := HomComplex.Cochain.congr_v hAssocM r s
      (by omega : r + (1 + (n + 1)) = s)
    rw [hcast_v (show (1 + n) + 1 = 1 + (n + 1) by omega) (conv (conv τ f) τ) r s
      (by omega : r + (1 + (n + 1)) = s)] at hA
    exact hA.symm
  -- Assemble: `δδ` vanishes; the remaining two-sided expansion adds
  -- the left leg. Signs normalize by `hsucc`/`hsq`, mixed terms cancel
  -- by `hMid`/`hAssocM`, and both curvatures close by `h`.
  calc HomComplex.δ (n + 1) ((n + 1) + 1)
          (HomComplex.δ n (n + 1) f +
            cast (congrArg (HomComplex.Cochain C A) h1) (conv τ f) -
            n.negOnePow • conv f τ) +
          cast (congrArg (HomComplex.Cochain C A) h2)
            (conv τ (HomComplex.δ n (n + 1) f +
              cast (congrArg (HomComplex.Cochain C A) h1) (conv τ f) -
              n.negOnePow • conv f τ)) -
          (n + 1).negOnePow • conv
            (HomComplex.δ n (n + 1) f +
              cast (congrArg (HomComplex.Cochain C A) h1) (conv τ f) -
              n.negOnePow • conv f τ) τ
        = (0 +
          (cast (congrArg (HomComplex.Cochain C A) (show (1 + 1) + n = (n + 1) + 1 by omega))
            (conv (HomComplex.δ 1 (1 + 1) τ) f) +
          (1 : ℤ).negOnePow • cast
            (congrArg (HomComplex.Cochain C A) (show 1 + (n + 1) = (n + 1) + 1 by omega))
            (conv τ (HomComplex.δ n (n + 1) f))) -
          n.negOnePow • conv (HomComplex.δ n (n + 1) f) τ -
          cast (congrArg (HomComplex.Cochain C A) hdeg.symm)
            (conv f (HomComplex.δ 1 (1 + 1) τ)) +
          cast (congrArg (HomComplex.Cochain C A) h2)
            (conv τ (HomComplex.δ n (n + 1) f)) +
          cast (congrArg (HomComplex.Cochain C A) h2)
            (conv τ (cast (congrArg (HomComplex.Cochain C A) h1) (conv τ f))) -
          cast (congrArg (HomComplex.Cochain C A) h2)
            (n.negOnePow • conv τ (conv f τ))) -
          (n + 1).negOnePow •
            (conv (HomComplex.δ n (n + 1) f) τ +
              conv (cast (congrArg (HomComplex.Cochain C A) h1) (conv τ f)) τ -
              n.negOnePow • conv (conv f τ) τ) := by
          rw [hδ_outer, hδδ, hLeibL_bridge, hLeibR_expand, hconvL_outer,
            hconvR_outer, hcast_sub h2, hcast_add h2, hcast_smul h2]
          simp only [zero_add, smul_add, smul_sub, hsq_smul, hsucc,
            Units.neg_smul]
          abel
      _ = 0 := by
          have _hBar0 := twistedBar_sq_zero τ f h
          have _hCobar0 := twistedCobar_sq_zero h f
          have hsign1 : (1 : ℤ).negOnePow = -1 := by decide
          rw [hsucc, hsign1, Units.neg_smul, one_smul]
          have hconv_cast_right : ∀ {a b : ℤ} (hab : a = b)
              (x : HomComplex.Cochain C A a),
              conv τ (cast (congrArg (HomComplex.Cochain C A) hab) x) =
              cast (congrArg (HomComplex.Cochain C A) (congrArg (1 + ·) hab))
                (conv τ x) := by
            intro a b hab x
            subst hab
            rfl
          have hconv_cast_left : ∀ {a b : ℤ} (hab : a = b)
              (x : HomComplex.Cochain C A a),
              conv (cast (congrArg (HomComplex.Cochain C A) hab) x) τ =
              cast (congrArg (HomComplex.Cochain C A) (congrArg (· + 1) hab))
                (conv x τ) := by
            intro a b hab x
            subst hab
            rfl
          have hTauLc : conv τ (cast (congrArg (HomComplex.Cochain C A) h1) (conv τ f)) =
              cast (congrArg (HomComplex.Cochain C A) (show 1 + (1 + n) = 1 + (n + 1) by omega))
                (conv τ (conv τ f)) := by
            exact hconv_cast_right h1 (conv τ f)
          have hLcTau : conv (cast (congrArg (HomComplex.Cochain C A) h1) (conv τ f)) τ =
              cast (congrArg (HomComplex.Cochain C A) (show (1 + n) + 1 = (n + 1) + 1 by omega))
                (conv (conv τ f) τ) := by
            exact hconv_cast_left h1 (conv τ f)
          have hAssocL : cast
              (congrArg (HomComplex.Cochain C A) (show (1 + 1) + n = 1 + (1 + n) by omega))
              (conv (conv τ τ) f) =
              conv τ (conv τ f) := by
            exact hAssocL
          rw [hTauLc, hLcTau, hMid, hAssocR_rev] at *
          simp only [smul_add, smul_sub, Units.neg_smul,
            sub_neg_eq_add, hsq_smul] at *
          -- Casts distribute/merge only by explicit rewrite (simp cannot use
          -- the explicit-equality transport lemmas); curvatures combine by
          -- factoring the single casts, then close by `h`.
          have hcast_zero : ∀ {a b : ℤ} (hab : a = b),
              cast (congrArg (HomComplex.Cochain C A) hab)
                (0 : HomComplex.Cochain C A a) = 0 := by
            intro a b hab
            subst hab
            rfl
          have hM0eq : cast (congrArg (HomComplex.Cochain C A) h2)
                (n.negOnePow • cast (congrArg (HomComplex.Cochain C A)
                  (show (1 + n) + 1 = 1 + (n + 1) by omega)) (conv (conv τ f) τ)) =
              n.negOnePow • cast (congrArg (HomComplex.Cochain C A)
                (show (1 + n) + 1 = (n + 1) + 1 by omega)) (conv (conv τ f) τ) := by
            rw [hcast_smul h2, hcast_cast _ h2 _]; omega
          have hL0cast : cast (congrArg (HomComplex.Cochain C A)
                  (show (1 + 1) + n = (n + 1) + 1 by omega))
                (conv (HomComplex.δ 1 (1 + 1) τ) f) +
              cast (congrArg (HomComplex.Cochain C A) h2)
                (cast (congrArg (HomComplex.Cochain C A) (congrArg (1 + ·) h1))
                  (conv τ (conv τ f))) = 0 := by
            rw [←hAssocL,
              hcast_cast (show (1 + 1) + n = 1 + (1 + n) by omega)
                (congrArg (1 + ·) h1) _,
              hcast_cast (show (1 + 1) + n = 1 + (n + 1) by omega) h2 _,
              ←hcast_add (show (1 + 1) + n = (n + 1) + 1 by omega),
              ←conv_add_left, hMC0L, hcast_zero]; omega
          have hR0cast : cast (congrArg (HomComplex.Cochain C A) hdeg.symm)
                (conv f (HomComplex.δ 1 (1 + 1) τ)) +
              cast (congrArg (HomComplex.Cochain C A) hdeg.symm)
                (conv f (conv τ τ)) = 0 := by
            rw [←hcast_add hdeg.symm, ←conv_add_right, hMC0R, hcast_zero]; omega
          have hL0' := eq_neg_of_add_eq_zero_left hL0cast
          have hR0' := eq_neg_of_add_eq_zero_left hR0cast
          rw [hL0', hR0', hM0eq]
          abel

end CochainComplex
