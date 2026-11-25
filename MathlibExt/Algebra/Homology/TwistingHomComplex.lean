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

public import MathlibExt.Algebra.Homology.TwistingDifferential

/-!
# Two-sided twisting Hom complex

This file packages the two-sided twisting differential
`twistedDifferential` and its square-zero theorem as a
`CochainComplex AddCommGrpCat ℤ` on the pinned `HomComplex C A` graded
carrier, under exactly a Maurer--Cartan hypothesis.

For `τ : Cochain C A 1` with `IsMaurerCartan τ` and `f : Cochain C A n`,
the differential is `twistedDifferential τ f` in degree `n + 1`, with the
single inherited cast via `add_comm 1 n`. No new graded carrier is built,
and no ModuleCat linearity is claimed: each differential is an
`AddMonoidHom` assembled from the existing additivity and zero laws.

## Grading and sign conventions

Cohomological grading throughout, following the two-sided twisting differential:
`τ : Cochain C A 1`, `twistedDifferential τ f = δ f + cast (τ ⋆ f) -
(-1) ^ n • (f ⋆ τ)` landing in `n + 1`. The sign is the graded commutator
with `|τ| = 1`, exactly as in `TwistingDifferential.lean`. The bundled
complex reuses `ComplexShape.up ℤ`, so `d n m` vanishes unless `n + 1 = m`
and `d` composes to zero by `twistedDifferential_sq_zero`.

## Declaration inventory

* `twistedDifferential_add`: additivity of the two-sided perturbation,
  from pinned `HomComplex.δ_add`, `conv_add_left/right`, cast
  distribution by cases, and scalar addition.
* `twistedDifferentialHom`: each differential as an `AddMonoidHom`,
  `if h : n + 1 = m` then the cast perturbation else `0`.
* `twistedHomComplex`: bundled `CochainComplex AddCommGrpCat ℤ` under
  `IsMaurerCartan τ`, with `shape` from the `ite_eq_right` branch and
  `d_comp_d'` from `twistedDifferential_sq_zero`.
* `twistedHomComplex_X`: object computation lemma.
* `twistedHomComplex_d_apply`: differential-application computation lemma
  with the explicit `if` and single cast.

## Nonclaims

No adjunction, no twisting-cochain bijection, no free or cofree object, no
conilpotence or completeness hypothesis, no totalization, no derived or
Koszul result, no operadic result, no model-categorical result, no
realization result, and no KQ-dependent consequence is claimed here. No
ModuleCat linearity is claimed; differentials are additive homomorphisms
only.

## Import justification

`TwistingDifferential` supplies `twistedDifferential`,
`twistedDifferential_zero`, `twistedDifferential_sq_zero`, and transitively
the pinned `HomComplex` API, `conv` with its additivity and zero laws, and
`IsMaurerCartan`. No further import is needed for the packaging.
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

/-- Additivity of the two-sided twisting differential, from the pinned
differential additivity, convolution additivity, cast distribution,
and scalar addition. -/
theorem twistedDifferential_add {n : ℤ}
    (τ : HomComplex.Cochain C A 1)
    (f g : HomComplex.Cochain C A n) :
    twistedDifferential τ (f + g) =
      twistedDifferential τ f + twistedDifferential τ g := by
  unfold twistedDifferential
  rw [HomComplex.δ_add, conv_add_right, conv_add_left]
  have hcast_add : ∀ {a b : ℤ} (hab : a = b)
      (x y : HomComplex.Cochain C A a),
      cast (congrArg (HomComplex.Cochain C A) hab) (x + y) =
        cast (congrArg (HomComplex.Cochain C A) hab) x +
          cast (congrArg (HomComplex.Cochain C A) hab) y := by
    intro a b hab x y
    cases hab
    rfl
  rw [hcast_add (add_comm 1 n), smul_add]
  abel

/-- Each two-sided twisting differential as an additive homomorphism:
when `n + 1 = m` the cast perturbation, otherwise `0`. The inner cast
orientation `add_comm 1 n` is inherited unchanged from
`twistedDifferential`. -/
noncomputable def twistedDifferentialHom
    (τ : HomComplex.Cochain C A 1) (n m : ℤ) :
    HomComplex.Cochain C A n →+ HomComplex.Cochain C A m where
  toFun f :=
    if h : n + 1 = m then
      cast (congrArg (HomComplex.Cochain C A) h) (twistedDifferential τ f)
    else 0
  map_zero' := by
    by_cases h : n + 1 = m
    · simp only [dite_eq_left h, twistedDifferential_zero]
      cases h
      rfl
    · simp only [dite_eq_right h]
  map_add' := by
    intro f g
    by_cases h : n + 1 = m
    · simp only [dite_eq_left h, twistedDifferential_add]
      cases h
      rfl
    · simp only [dite_eq_right h, add_zero]

/-- The bundled two-sided twisting Hom complex under exactly a
Maurer--Cartan hypothesis, on the pinned `HomComplex` carrier. The complex
relation is discharged by `twistedDifferential_sq_zero`. -/
noncomputable def twistedHomComplex
    (τ : HomComplex.Cochain C A 1) (hMC : IsMaurerCartan τ) :
    CochainComplex AddCommGrpCat ℤ where
  X n := AddCommGrpCat.of (HomComplex.Cochain C A n)
  d n m := AddCommGrpCat.ofHom (twistedDifferentialHom τ n m)
  shape n m hnm := by
    have h : ¬ n + 1 = m := by simpa [ComplexShape.up_Rel] using hnm
    ext f
    simp [twistedDifferentialHom, dite_eq_right h]
  d_comp_d' n m k hij hjk := by
    have h1 : n + 1 = m := by simpa [ComplexShape.up_Rel] using hij
    have h2 : m + 1 = k := by simpa [ComplexShape.up_Rel] using hjk
    ext f p q hpq x
    simp only [twistedDifferentialHom, dite_eq_left h1, dite_eq_left h2]
    cases h1
    cases h2
    rw [← AddCommGrpCat.ofHom_comp, AddCommGrpCat.ofHom_apply,
      AddMonoidHom.comp_apply]
    have hSq := twistedDifferential_sq_zero τ f hMC
    have hW := congrArg
      (fun g : HomComplex.Cochain C A ((n + 1) + 1) =>
        ModuleCat.Hom.hom (g.v p q hpq) x) hSq
    exact hW

/-- Object computation lemma for the twisting Hom complex. -/
@[simp]
theorem twistedHomComplex_X (τ : HomComplex.Cochain C A 1)
    (hMC : IsMaurerCartan τ) (n : ℤ) :
    (twistedHomComplex τ hMC).X n =
      AddCommGrpCat.of (HomComplex.Cochain C A n) :=
  rfl

/-- Differential-application computation lemma for the twisting Hom complex,
with the explicit `if` and single cast. -/
@[simp]
theorem twistedHomComplex_d_apply (τ : HomComplex.Cochain C A 1)
    (hMC : IsMaurerCartan τ) (n m : ℤ)
    (f : HomComplex.Cochain C A n) :
    ((twistedHomComplex τ hMC).d n m) f =
      (if h : n + 1 = m then
        cast (congrArg (HomComplex.Cochain C A) h)
          (twistedDifferential τ f)
      else 0) :=
  rfl

end CochainComplex
