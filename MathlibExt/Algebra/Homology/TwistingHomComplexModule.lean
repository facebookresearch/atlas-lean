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

public import MathlibExt.Algebra.Homology.TwistingHomComplex

/-!
# R-linear twisting Hom complex

This file packages the two-sided twisting differential as an `R`-linear map
and bundles the resulting `CochainComplex (ModuleCat R) ℤ`, under exactly a
Maurer--Cartan hypothesis. It is a thin linear layer over
`MathlibExt/Algebra/Homology/TwistingHomComplex.lean` and preserves its
carrier, degrees, casts, and signs exactly.

For `τ : Cochain C A 1` with `IsMaurerCartan τ` and `f : Cochain C A n`,
the differential is `twistedDifferential τ f` in degree `n + 1`, with the
single inherited cast via `add_comm 1 n`. The carrier objectwise is the pinned
`HomComplex.Cochain C A n` with its canonical `Module R` instance (pointwise
from `ModuleCat R` morphisms); no new global instance is introduced.

## Grading and sign conventions

Cohomological grading throughout, following `TwistingHomComplex.lean`:
`τ : Cochain C A 1`, `twistedDifferential τ f = δ f + cast (τ ⋆ f) -
(-1) ^ n • (f ⋆ τ)` landing in `n + 1`. The sign is the graded commutator
with `|τ| = 1`. The bundled complex reuses `ComplexShape.up ℤ`.

## Relation to the additive complex

`TwistingHomComplex.twistedHomComplex τ hMC : CochainComplex AddCommGrpCat ℤ`
uses the same carrier family and the same differential as an `AddMonoidHom`
(`twistedDifferentialHom`). This file reuses that additivity
(`twistedDifferential_add`) and adds `R`-linearity (`twistedDifferential_smul`)
to bundle the same differential as a linear map (`twistedDifferentialLinear`)
and the same family as `ModuleCat R` objects (`twistedHomComplexModule`).
No new graded carrier is built, no differential formula is changed, and no
additional completeness, filtration, representability, adjunction, derived,
Koszul, operadic, model-categorical, or realization claim is made.

## Declaration inventory

* `tensorHom_smul_left/right` (private): `⊗ₘ` of `ModuleCat R` morphisms is
  `R`-linear in each factor, by rewriting through `ModuleCat.hom_tensorHom`
  (and `ModuleCat.hom_smul`) with pinned `TensorProduct.map_smul_left/right`.
* `tensorCochain_smul_left/right` (private): the graded tensor product is
  `R`-linear in each factor, via pinned `smul_comm` for Koszul-sign/scalar
  commutation and the pinned `Cochain.smul_v`,
  `Linear.smul_comp`, and `Linear.comp_smul`.
* `conv_smul_left_R/right_R` (private): convolution is `R`-bilinear, from the
  tensor laws with the pinned `Cochain.smul_comp`/`Cochain.comp_smul`.
* `twistedDifferential_smul`: the two-sided perturbation is `R`-linear,
  from pinned `HomComplex.δ_smul`, the convolution laws, cast distribution
  by equality elimination, and sign commutation via `smul_comm`.
* `twistedDifferentialLinear`: each differential as a linear map,
  `if h : n + 1 = m` then the cast perturbation else `0`.
* `twistedHomComplexModule`: bundled `CochainComplex (ModuleCat R) ℤ` under
  `IsMaurerCartan τ`, with `shape` from the `ite_eq_right` branch and
  `d_comp_d'` from `twistedDifferential_sq_zero`.
* `twistedHomComplexModule_X`: object computation lemma.
* `twistedHomComplexModule_d_apply`: differential-application computation
  lemma with the explicit `if` and single cast.

## Nonclaims

No adjunction, no twisting-cochain bijection, no free or cofree object, no
conilpotence or completeness hypothesis, no totalization, no derived or
Koszul result, no operadic result, no model-categorical result, no
realization result, and no KQ-dependent consequence is claimed here. No new
global instance is introduced; the `Module R` structure on cochains is the
pinned deriving instance.

## Import justification

`TwistingHomComplex` supplies `twistedDifferential`, `twistedDifferential_add`,
`twistedDifferential_zero`, `twistedDifferential_sq_zero`, and transitively
the pinned `HomComplex` API, `conv` with its definitions, and `IsMaurerCartan`.
`TensorProduct` lemmas arrive transitively for the `⊗ₘ` linearity helpers; no
bar/cobar, totalization, or new tensor rebuild is added here.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory TensorProduct

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

omit [MonObj A] [ComonObj C] [∀ (X₁ X₂ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasTensor X₁ X₂] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃] in
/-- `⊗ₘ` of `ModuleCat R` morphisms is `R`-linear in the left factor. -/
private theorem tensorHom_smul_left {X₁ Y₁ X₂ Y₂ : ModuleCat R} (k : R)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : ((k • f) ⊗ₘ g) = k • (f ⊗ₘ g) := by
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_tensorHom, ModuleCat.hom_smul,
    TensorProduct.map_smul_left]

omit [MonObj A] [ComonObj C] [∀ (X₁ X₂ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasTensor X₁ X₂] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃] in
/-- `⊗ₘ` of `ModuleCat R` morphisms is `R`-linear in the right factor. -/
private theorem tensorHom_smul_right {X₁ Y₁ X₂ Y₂ : ModuleCat R} (k : R)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : (f ⊗ₘ (k • g)) = k • (f ⊗ₘ g) := by
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_tensorHom, ModuleCat.hom_smul,
    TensorProduct.map_smul_right]

omit [MonObj A] [ComonObj C] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃] in
/-- The graded tensor product is `R`-linear in the left factor. -/
private theorem tensorCochain_smul_left {m n : ℤ} (k : R)
    (f : HomComplex.Cochain C A m) (g : HomComplex.Cochain C A n) :
    tensorCochain (k • f) g = k • tensorCochain f g := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [tensorCochain_v, HomComplex.Cochain.smul_v, tensorCochain_v]
  apply HomologicalComplex.mapBifunctor.hom_ext (c := ComplexShape.up ℤ)
  intro i₁ i₂ hh
  have hcomm : ∀ (Z : (C.X i₁ ⊗ C.X i₂) ⟶ (HomologicalComplex.tensorObj A A).X s),
      (n * i₁).negOnePow • (k • Z) = k • ((n * i₁).negOnePow • Z) := by
    intro Z
    exact smul_comm _ _ _
  simp only [HomologicalComplex.ι_mapBifunctorDesc, convSummand,
    HomComplex.Cochain.smul_v, tensorHom_smul_left,
    Linear.smul_comp, Linear.comp_smul, hcomm]

omit [MonObj A] [ComonObj C] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃] in
/-- The graded tensor product is `R`-linear in the right factor. -/
private theorem tensorCochain_smul_right {m n : ℤ} (k : R)
    (f : HomComplex.Cochain C A m) (g : HomComplex.Cochain C A n) :
    tensorCochain f (k • g) = k • tensorCochain f g := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [tensorCochain_v, HomComplex.Cochain.smul_v, tensorCochain_v]
  apply HomologicalComplex.mapBifunctor.hom_ext (c := ComplexShape.up ℤ)
  intro i₁ i₂ hh
  have hcomm : ∀ (Z : (C.X i₁ ⊗ C.X i₂) ⟶ (HomologicalComplex.tensorObj A A).X s),
      (n * i₁).negOnePow • (k • Z) = k • ((n * i₁).negOnePow • Z) := by
    intro Z
    exact smul_comm _ _ _
  simp only [HomologicalComplex.ι_mapBifunctorDesc, convSummand,
    HomComplex.Cochain.smul_v, tensorHom_smul_right,
    Linear.smul_comp, Linear.comp_smul, hcomm]

/-- Convolution is `R`-linear in the left factor. -/
private theorem conv_smul_left_R {m n : ℤ} (k : R)
    (f : HomComplex.Cochain C A m) (g : HomComplex.Cochain C A n) :
    conv (k • f) g = k • conv f g := by
  unfold conv
  rw [tensorCochain_smul_left, HomComplex.Cochain.comp_smul,
    HomComplex.Cochain.smul_comp]

/-- Convolution is `R`-linear in the right factor. -/
private theorem conv_smul_right_R {m n : ℤ} (k : R)
    (f : HomComplex.Cochain C A m) (g : HomComplex.Cochain C A n) :
    conv f (k • g) = k • conv f g := by
  unfold conv
  rw [tensorCochain_smul_right, HomComplex.Cochain.comp_smul,
    HomComplex.Cochain.smul_comp]

/-- `R`-linearity of the two-sided twisting differential, from the pinned
differential linearity, the convolution bilinearity, cast distribution,
and sign commutation. -/
theorem twistedDifferential_smul {n : ℤ} (k : R)
    (τ : HomComplex.Cochain C A 1) (f : HomComplex.Cochain C A n) :
    twistedDifferential τ (k • f) = k • twistedDifferential τ f := by
  unfold twistedDifferential
  rw [HomComplex.δ_smul n (n + 1) k f, conv_smul_right_R k τ f, conv_smul_left_R k f τ]
  have hcast_smul : ∀ {a b : ℤ} (hab : a = b)
      (x : HomComplex.Cochain C A a),
      cast (congrArg (HomComplex.Cochain C A) hab) (k • x) =
        k • cast (congrArg (HomComplex.Cochain C A) hab) x := by
    intro a b hab x
    cases hab
    rfl
  have hcommC : ∀ (X : HomComplex.Cochain C A (n + 1)),
      n.negOnePow • (k • X) = k • (n.negOnePow • X) := by
    intro X
    exact smul_comm _ _ _
  rw [hcast_smul (add_comm (1 : ℤ) n) (conv τ f), smul_sub, smul_add, hcommC]

/-- Each two-sided twisting differential as a linear map:
when `n + 1 = m` the cast perturbation, otherwise `0`. The inner cast
orientation `add_comm 1 n` is inherited unchanged from
`twistedDifferential`. -/
noncomputable def twistedDifferentialLinear
    (τ : HomComplex.Cochain C A 1) (n m : ℤ) :
    HomComplex.Cochain C A n →ₗ[R] HomComplex.Cochain C A m where
  toFun f :=
    if h : n + 1 = m then
      cast (congrArg (HomComplex.Cochain C A) h) (twistedDifferential τ f)
    else 0
  map_add' := by
    intro f g
    by_cases h : n + 1 = m
    · simp only [dite_eq_left h, twistedDifferential_add]
      cases h
      rfl
    · simp only [dite_eq_right h, add_zero]
  map_smul' := by
    intro k f
    by_cases h : n + 1 = m
    · simp only [dite_eq_left h, twistedDifferential_smul]
      cases h
      rfl
    · simp only [dite_eq_right h, smul_zero]

/-- The bundled `R`-linear two-sided twisting Hom complex under exactly a
Maurer--Cartan hypothesis, on the pinned `HomComplex` carrier. The complex
relation is discharged by `twistedDifferential_sq_zero`. -/
noncomputable def twistedHomComplexModule
    (τ : HomComplex.Cochain C A 1) (hMC : IsMaurerCartan τ) :
    CochainComplex (ModuleCat R) ℤ where
  X n := ModuleCat.of R (HomComplex.Cochain C A n)
  d n m := ModuleCat.ofHom (twistedDifferentialLinear τ n m)
  shape n m hnm := by
    have h : ¬ n + 1 = m := by simpa [ComplexShape.up_Rel] using hnm
    ext f
    simp [twistedDifferentialLinear, dite_eq_right h]
  d_comp_d' n m k hij hjk := by
    have h1 : n + 1 = m := by simpa [ComplexShape.up_Rel] using hij
    have h2 : m + 1 = k := by simpa [ComplexShape.up_Rel] using hjk
    ext f p q hpq x
    simp only [twistedDifferentialLinear, dite_eq_left h1, dite_eq_left h2]
    cases h1
    cases h2
    rw [← ModuleCat.ofHom_comp, ModuleCat.ofHom_apply,
      LinearMap.comp_apply]
    have hSq := twistedDifferential_sq_zero τ f hMC
    have hW := congrArg
      (fun g : HomComplex.Cochain C A ((n + 1) + 1) =>
        ModuleCat.Hom.hom (g.v p q hpq) x) hSq
    exact hW

/-- Object computation lemma for the `R`-linear twisting Hom complex. -/
@[simp]
theorem twistedHomComplexModule_X (τ : HomComplex.Cochain C A 1)
    (hMC : IsMaurerCartan τ) (n : ℤ) :
    (twistedHomComplexModule τ hMC).X n =
      ModuleCat.of R (HomComplex.Cochain C A n) :=
  rfl

/-- Differential-application computation lemma for the `R`-linear twisting Hom
complex, with the explicit `if` and single cast. -/
@[simp]
theorem twistedHomComplexModule_d_apply (τ : HomComplex.Cochain C A 1)
    (hMC : IsMaurerCartan τ) (n m : ℤ)
    (f : HomComplex.Cochain C A n) :
    ((twistedHomComplexModule τ hMC).d n m) f =
      (if h : n + 1 = m then
        cast (congrArg (HomComplex.Cochain C A) h)
          (twistedDifferential τ f)
      else 0) :=
  rfl

end CochainComplex
