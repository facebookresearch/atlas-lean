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
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.ComplexShapeSigns
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.Comon_

/-!
# Convolution laws for twisting cochains

This file develops convolution laws for twisting cochains, built on the graded
convolution product of `MathlibExt/RingTheory/DifferentialGraded/TwistingCochain.lean`.
It proves the graded tensor-product reassociation coherence and the
Leibniz rule for the graded convolution product `CochainComplex.conv`, and defines
the convolution unit cochain.

## Grading and sign conventions

Cohomological grading throughout, following the graded-convolution conventions of
`TwistingCochain.lean`: for `f : Cochain C A m` and
`g : Cochain C A n`, `tensorCochain f g` acts on the `(i₁, i₂)`-summand by
`(-1) ^ (n * i₁) • (f ⊗ₘ g)` (`Int.negOnePow (n * i₁)`), matching the pinned
tensor-complex convention whose vertical sign is `(up ℤ).ε` on the second
factor (`ComplexShape.ε_up_ℤ`). Composition of cochains is written `≫`.
The differential is `HomComplex.δ` (Conrad signs): for `z₁` of degree `n₁`
and `z₂` of degree `n₂`,
`δ (z₁ ≫ z₂) = z₁ ≫ δ z₂ + (-1) ^ n₂ • (δ z₁ ≫ z₂)` (`HomComplex.δ_comp`).

## Primary source

Standard reference: J.-L. Loday and B. Vallette, *Algebraic Operads*,
Grundlehren 346, Springer, 2012,
<https://doi.org/10.1007/978-3-642-30362-3>; see the full convention map in
`MathlibExt/RingTheory/DifferentialGraded/TwistingCochain.lean`. The Leibniz
rule proved here is `δ (f ⋆ g) = (δ f) ⋆ g + (-1) ^ m • (f ⋆ (δ g))` with the
pinned `HomComplex.δ` and the Koszul sign above. Exact printed-section numbers
and a sign-level match against the printed text were not verified in this
environment, so none is claimed here.

## Declaration inventory

* `tensorCochain_assoc`: reassociation coherence for graded tensor-product
  summands through the `ModuleCat` associator, with the pinned Koszul signs.
  It is stated at summand level because `tensorCochain` in `TwistingCochain.lean`
  requires both
  factors to share one source/target pair, so a nested `tensorCochain`
  application does not typecheck; this coherence is the summand-level form of
  tensor associativity consumed by `conv_assoc`.
* `tensorCochain_δ_v` (private): component-level Leibniz splitting for
  `δ (tensorCochain f g)`, specializing the heterogeneous
  `HomComplex.Cochain.tensor_δ_v` via the `tensorCochain_eq_tensor` bridge.
* `convOne`: the degree-`0` unit cochain, `counit ≫ one` via `ComonObj.counit`
  and `MonObj.one`.
* `conv_leibniz`: `δ (f ⋆ g) = (δ f) ⋆ g + (-1) ^ m • (f ⋆ (δ g))`, with the
  right-hand summands transported to degree `m + n + 1` by explicit
  composition degree proofs.
* `conv_add_left`/`conv_add_right`: convolution distributes over addition in
  each factor, reusing `tensorCochain_add_left`/`tensorCochain_add_right` and
  the pinned `Cochain.comp_add`/`Cochain.add_comp`; degrees stay `m + n` with
  the same `zero_add`/`add_zero` transports as `conv`.
* `conv_smul_left`/`conv_smul_right`: a `ℤˣ` scalar on either factor pushes
  through convolution, reusing the private `tensorCochain_smul_left`/
  `tensorCochain_smul_right` and the pinned `Cochain.units_smul_comp`/
  `Cochain.comp_units_smul` (the units analogues proved from the named
  `Cochain.smul_comp`/`Cochain.comp_smul`); degrees stay `m + n` with no new
  transports, so sign scalars infer cleanly for the later square-zero proof.
* Private helpers: `neg_tensorHom_left`/`neg_tensorHom_right` (negation through
  `⊗ₘ`), `tensorHom_units_smul_left`/`tensorHom_units_smul_right` (unit scalars
  through `⊗ₘ`), `tensorCochain_add_left`/`tensorCochain_add_right` (additivity
  through `⊗ₘ`), `tensorCochain_smul_left`/`tensorCochain_smul_right` (unit
  scalars through `tensorCochain`, commuting with the Koszul sign by
  commutativity of `ℤˣ`), and `up_ε₁`/`up_ε₂` (evaluation of the `up ℤ`
  total-complex signs).

## A note on `convOne` and the twisting data

The twisting data in `TwistingCochain.lean` carries an explicit coaugmentation `η : 𝟙_ ⟶ C` and
augmentation `ε : A ⟶ 𝟙_`. These directions cannot pre- or post-compose into
a cochain `C ⟶ A` of degree `0`: there is no graded-convolution map `C ⟶ A` built from
`η` and `ε` alone. The convolution unit is instead the canonical
counit--unit composite `convOne`, using `ComonObj.counit` and `MonObj.one`.

## Scope and companion results

This file proves no associativity or unit law. Associativity and the one-sided
unit laws are `CochainComplex.conv_assoc`, `CochainComplex.conv_one_left`, and
`CochainComplex.conv_one_right` in
`MathlibExt/Algebra/Homology/TwistingConvolutionMonoid.lean`, which consumes
the `tensorCochain_assoc` coherence and `convOne` defined here. Nothing about
units or associativity is asserted here.

## Nonclaims

No homological (`down ℤ`) API; no bar--cobar adjunction, twisting-cochain
bijection, totalization, EZ/AW, derived/Koszul, operadic, or
model-categorical result; no homological unitor bridge beyond what is stated.

## Import justification

`TwistingCochain` supplies `tensorCochain`/`conv`/`convSummand`; `HomComplex`
supplies the cochain composition/differential API; `Monoidal`/`Bifunctor`
supply the tensor product, `mapBifunctorDesc`, and the `D₁`/`D₂`
decomposition; `ComplexShapeSigns` supplies the `up ℤ` signs; `Mon`/`Comon_`
supply the (co)monoid structures. No bar/cobar imports are needed.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

namespace CochainComplex

variable {R : Type*} [CommRing R]
variable {C A : CochainComplex (ModuleCat R) ℤ}

/-- Negation pushes through the left factor of `⊗ₘ`, from additivity. -/
private lemma neg_tensorHom_left {X₁ Y₁ X₂ Y₂ : ModuleCat R}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : ((-f) ⊗ₘ g) = -((f ⊗ₘ g)) := by
  have h : ((-f) ⊗ₘ g) + ((f ⊗ₘ g)) = 0 := by
    rw [← MonoidalPreadditive.add_tensor, neg_add_cancel,
      MonoidalPreadditive.zero_tensor]
  exact eq_neg_of_add_eq_zero_left h

/-- Negation pushes through the right factor of `⊗ₘ`, from additivity. -/
private lemma neg_tensorHom_right {X₁ Y₁ X₂ Y₂ : ModuleCat R}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : ((f ⊗ₘ (-g))) = -((f ⊗ₘ g)) := by
  have h : ((f ⊗ₘ (-g))) + ((f ⊗ₘ g)) = 0 := by
    rw [← MonoidalPreadditive.tensor_add, neg_add_cancel,
      MonoidalPreadditive.tensor_zero]
  exact eq_neg_of_add_eq_zero_left h

/-- A unit scalar pushes through the left factor of `⊗ₘ`. -/
private lemma tensorHom_units_smul_left {X₁ Y₁ X₂ Y₂ : ModuleCat R} (k : ℤˣ)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : ((k • f) ⊗ₘ g) = k • (f ⊗ₘ g) := by
  rcases Int.units_eq_one_or k with rfl | rfl
  · simp only [one_smul]
  · simp only [Units.neg_smul, one_smul, neg_tensorHom_left]

/-- A unit scalar pushes through the right factor of `⊗ₘ`. -/
private lemma tensorHom_units_smul_right {X₁ Y₁ X₂ Y₂ : ModuleCat R} (k : ℤˣ)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : ((f ⊗ₘ (k • g))) = k • (f ⊗ₘ g) := by
  rcases Int.units_eq_one_or k with rfl | rfl
  · simp only [one_smul]
  · simp only [Units.neg_smul, one_smul, neg_tensorHom_right]

/-- Reassociation coherence for graded tensor-product summands through the
`ModuleCat` associator, with the pinned Koszul signs.

The left-hand side exponent `(n + p) * i₁ + p * i₂` is the 23-first total on
12-associated maps; the right-hand side exponent `n * i₁ + p * (i₁ + i₂)` is
the 12-first total on 23-associated maps. The exponents agree by `ring`, and
the unsigned maps agree by naturality of the associator. -/
theorem tensorCochain_assoc {m n p : ℤ} (f : HomComplex.Cochain C A m)
    (g : HomComplex.Cochain C A n) (h : HomComplex.Cochain C A p)
    (i₁ i₂ i₃ : ℤ) :
    (((n + p) * i₁ + p * i₂).negOnePow •
        ((f.v i₁ (i₁ + m) rfl ⊗ₘ g.v i₂ (i₂ + n) rfl) ⊗ₘ h.v i₃ (i₃ + p) rfl)) ≫
      (α_ (A.X (i₁ + m)) (A.X (i₂ + n)) (A.X (i₃ + p))).hom =
    (α_ (C.X i₁) (C.X i₂) (C.X i₃)).hom ≫ ((n * i₁ + p * (i₁ + i₂)).negOnePow •
        (f.v i₁ (i₁ + m) rfl ⊗ₘ (g.v i₂ (i₂ + n) rfl ⊗ₘ h.v i₃ (i₃ + p) rfl))) := by
  have hsign : (n + p) * i₁ + p * i₂ = n * i₁ + p * (i₁ + i₂) := by
    rw [add_mul, mul_add, add_assoc]
  rw [hsign, Linear.units_smul_comp, Linear.comp_units_smul,
    MonoidalCategory.associator_naturality]

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

/-- The unit cochain for convolution: the counit of `C` followed by the unit
of `A`. See the module documentation for why the explicit twisting-data maps
`η : 𝟙_ ⟶ C` and `ε : A ⟶ 𝟙_` cannot induce this cochain on their own. -/
noncomputable def convOne : HomComplex.Cochain C A 0 :=
  (HomComplex.Cochain.ofHom (ComonObj.counit (X := C))).comp
    (HomComplex.Cochain.ofHom (MonObj.one (X := A))) (zero_add 0)

/-- The first-factor sign of the `up ℤ` total complex shape is trivial. -/
private lemma up_ε₁ (x : ℤ × ℤ) :
    ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) x = 1 := rfl

/-- The second-factor sign of the `up ℤ` total complex shape is the pinned
vertical sign `(up ℤ).ε` on the first index. -/
private lemma up_ε₂ (x : ℤ × ℤ) :
    ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) x = (x.1).negOnePow := rfl

omit [MonObj A] [ComonObj C] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensor₁₂Tensor X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensorTensor₂₃ X₂ X₃] in
/-- Component-level Leibniz splitting for the graded tensor product of
cochains: `δ` of `tensorCochain f g` is `tensorCochain (δ f) g` plus
`(-1) ^ m • tensorCochain f (δ g)`, as maps out of `(C ⊗ C).X r`.

This specializes the heterogeneous `HomComplex.Cochain.tensor_δ_v` via the
`tensorCochain_eq_tensor` bridge. -/
private theorem tensorCochain_δ_v {m n : ℤ} (f : HomComplex.Cochain C A m)
    (g : HomComplex.Cochain C A n) (r s : ℤ) (hrs : r + (m + n + 1) = s) :
    (HomComplex.δ (m + n) (m + n + 1) (tensorCochain f g)).v r s hrs =
      (tensorCochain (HomComplex.δ m (m + 1) f) g).v r s (by omega) +
        m.negOnePow •
          (tensorCochain f (HomComplex.δ n (n + 1) g)).v r s (by omega) := by
  simpa only [tensorCochain_eq_tensor] using
    HomComplex.Cochain.tensor_δ_v f g r s hrs

/-- Leibniz rule for the graded convolution product: differentiating
`f ⋆ g` differentiates the left factor first, then the right factor with
the Koszul sign `(-1) ^ m`.

The two right-hand summands are stated as explicit `Cochain.comp`
composites landing in degree `m + n + 1` (via explicit degree proofs),
i.e. as `conv (δ f) g` and `conv f (δ g)` up to degree transport. The
proof pushes `δ` inward with the pinned `δ_comp` (the `ofHom` comultiplication
and multiplication are cycles by `δ_ofHom`), then closes at components with
`tensorCochain_δ_v`. -/
theorem conv_leibniz {m n : ℤ} (f : HomComplex.Cochain C A m)
    (g : HomComplex.Cochain C A n) :
    HomComplex.δ (m + n) (m + n + 1) (conv f g) =
      (((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
        (tensorCochain (HomComplex.δ m (m + 1) f) g)
        (by omega : (0 : ℤ) + (m + 1 + n) = m + n + 1)).comp
        (HomComplex.Cochain.ofHom (MonObj.mul (X := A)))
        (by omega : (m + n + 1) + 0 = m + n + 1)) +
      m.negOnePow • ((((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
        (tensorCochain f (HomComplex.δ n (n + 1) g))
        (by omega : (0 : ℤ) + (m + (n + 1)) = m + n + 1)).comp
        (HomComplex.Cochain.ofHom (MonObj.mul (X := A)))
        (by omega : (m + n + 1) + 0 = m + n + 1))) := by
  unfold conv
  rw [HomComplex.δ_comp (n₁ := m + n) (n₂ := 0) (n₁₂ := m + n) _ _
    (add_zero (m + n)) (m + n + 1) 1 (m + n + 1) rfl rfl (zero_add 1)]
  simp only [HomComplex.δ_ofHom, HomComplex.Cochain.comp_zero, zero_add,
    Int.negOnePow_zero, one_smul]
  rw [HomComplex.δ_comp (n₁ := 0) (n₂ := m + n) (n₁₂ := m + n) _ _
    (zero_add (m + n)) 1 (m + n + 1) (m + n + 1) rfl (zero_add 1) rfl]
  simp only [HomComplex.δ_ofHom, HomComplex.Cochain.zero_comp, smul_zero,
    add_zero]
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [HomComplex.Cochain.comp_v _ _ _ r s s (by omega) (add_zero s),
    HomComplex.Cochain.comp_v _ _ _ r r s (add_zero r) hrs]
  rw [tensorCochain_δ_v f g r s hrs]
  simp only [HomComplex.Cochain.add_v, HomComplex.Cochain.units_smul_v]
  rw [HomComplex.Cochain.comp_v _ _ _ r s s (by omega) (add_zero s),
    HomComplex.Cochain.comp_v _ _ _ r r s (add_zero r) (by omega),
    HomComplex.Cochain.comp_v _ _ _ r s s (by omega) (add_zero s),
    HomComplex.Cochain.comp_v _ _ _ r r s (add_zero r) (by omega)]
  simp only [tensorCochain_v, HomComplex.Cochain.ofHom_v,
    Preadditive.comp_add, Preadditive.add_comp,
    Linear.comp_units_smul, Linear.units_smul_comp]

omit [MonObj A] [ComonObj C] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensor₁₂Tensor X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensorTensor₂₃ X₂ X₃] in
/-- The graded tensor product distributes over addition on the left, from
additivity of `⊗ₘ` through the pinned `mapBifunctor` descriptor. -/
private theorem tensorCochain_add_left {m n : ℤ}
    (f₁ f₂ : HomComplex.Cochain C A m) (g : HomComplex.Cochain C A n) :
    tensorCochain (f₁ + f₂) g = tensorCochain f₁ g + tensorCochain f₂ g := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [tensorCochain_v, HomComplex.Cochain.add_v, tensorCochain_v, tensorCochain_v]
  apply HomologicalComplex.mapBifunctor.hom_ext (c := ComplexShape.up ℤ)
  intro i₁ i₂ hh
  simp only [HomologicalComplex.ι_mapBifunctorDesc, Preadditive.comp_add,
    convSummand, HomComplex.Cochain.add_v, MonoidalPreadditive.add_tensor,
    smul_add, Preadditive.add_comp]

omit [MonObj A] [ComonObj C] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensor₁₂Tensor X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensorTensor₂₃ X₂ X₃] in
/-- The graded tensor product distributes over addition on the right, from
additivity of `⊗ₘ` through the pinned `mapBifunctor` descriptor. -/
private theorem tensorCochain_add_right {m n : ℤ}
    (f : HomComplex.Cochain C A m) (g₁ g₂ : HomComplex.Cochain C A n) :
    tensorCochain f (g₁ + g₂) = tensorCochain f g₁ + tensorCochain f g₂ := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [tensorCochain_v, HomComplex.Cochain.add_v, tensorCochain_v, tensorCochain_v]
  apply HomologicalComplex.mapBifunctor.hom_ext (c := ComplexShape.up ℤ)
  intro i₁ i₂ hh
  simp only [HomologicalComplex.ι_mapBifunctorDesc, Preadditive.comp_add,
    convSummand, HomComplex.Cochain.add_v, MonoidalPreadditive.tensor_add,
    smul_add, Preadditive.add_comp]

omit [MonObj A] [ComonObj C] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensor₁₂Tensor X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensorTensor₂₃ X₂ X₃] in
/-- A `ℤˣ` scalar on the left factor pushes through the graded tensor product,
commuting with the Koszul sign by commutativity of `ℤˣ`. Reuses the existing
`tensorHom_units_smul_left`; no new `⊗ₘ` helper is needed. -/
private theorem tensorCochain_smul_left {m n : ℤ} (k : ℤˣ)
    (f : HomComplex.Cochain C A m) (g : HomComplex.Cochain C A n) :
    tensorCochain (k • f) g = k • tensorCochain f g := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [tensorCochain_v, HomComplex.Cochain.units_smul_v, tensorCochain_v]
  apply HomologicalComplex.mapBifunctor.hom_ext (c := ComplexShape.up ℤ)
  intro i₁ i₂ hh
  have hcomm : ∀ (Z : (C.X i₁ ⊗ C.X i₂) ⟶ (HomologicalComplex.tensorObj A A).X s),
      (n * i₁).negOnePow • (k • Z) = k • ((n * i₁).negOnePow • Z) := by
    intro Z
    rw [smul_smul, smul_smul, mul_comm ((n * i₁).negOnePow) k]
  simp only [HomologicalComplex.ι_mapBifunctorDesc, convSummand,
    HomComplex.Cochain.units_smul_v, tensorHom_units_smul_left,
    Linear.units_smul_comp, Linear.comp_units_smul, hcomm]

omit [MonObj A] [ComonObj C] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensor₁₂Tensor X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensorTensor₂₃ X₂ X₃] in
/-- A `ℤˣ` scalar on the right factor pushes through the graded tensor product,
commuting with the Koszul sign by commutativity of `ℤˣ`. Reuses the existing
`tensorHom_units_smul_right`; no new `⊗ₘ` helper is needed. -/
private theorem tensorCochain_smul_right {m n : ℤ} (k : ℤˣ)
    (f : HomComplex.Cochain C A m) (g : HomComplex.Cochain C A n) :
    tensorCochain f (k • g) = k • tensorCochain f g := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [tensorCochain_v, HomComplex.Cochain.units_smul_v, tensorCochain_v]
  apply HomologicalComplex.mapBifunctor.hom_ext (c := ComplexShape.up ℤ)
  intro i₁ i₂ hh
  have hcomm : ∀ (Z : (C.X i₁ ⊗ C.X i₂) ⟶ (HomologicalComplex.tensorObj A A).X s),
      (n * i₁).negOnePow • (k • Z) = k • ((n * i₁).negOnePow • Z) := by
    intro Z
    rw [smul_smul, smul_smul, mul_comm ((n * i₁).negOnePow) k]
  simp only [HomologicalComplex.ι_mapBifunctorDesc, convSummand,
    HomComplex.Cochain.units_smul_v, tensorHom_units_smul_right,
    Linear.units_smul_comp, Linear.comp_units_smul, hcomm]

/-- Convolution distributes over addition on the left, reusing
`tensorCochain_add_left` and the pinned `Cochain.comp_add`/`Cochain.add_comp`.
Degrees stay `m + n` with the same `zero_add`/`add_zero` transports as `conv`. -/
theorem conv_add_left {m n : ℤ} (f₁ f₂ : HomComplex.Cochain C A m)
    (g : HomComplex.Cochain C A n) :
    conv (f₁ + f₂) g = conv f₁ g + conv f₂ g := by
  unfold conv
  rw [tensorCochain_add_left, HomComplex.Cochain.comp_add,
    HomComplex.Cochain.add_comp]

/-- Convolution distributes over addition on the right, reusing
`tensorCochain_add_right` and the pinned `Cochain.comp_add`/`Cochain.add_comp`.
Degrees stay `m + n` with the same `zero_add`/`add_zero` transports as `conv`. -/
theorem conv_add_right {m n : ℤ} (f : HomComplex.Cochain C A m)
    (g₁ g₂ : HomComplex.Cochain C A n) :
    conv f (g₁ + g₂) = conv f g₁ + conv f g₂ := by
  unfold conv
  rw [tensorCochain_add_right, HomComplex.Cochain.comp_add,
    HomComplex.Cochain.add_comp]

/-- A `ℤˣ` scalar on the left factor pushes through convolution, reusing
`tensorCochain_smul_left` and the pinned `Cochain.comp_units_smul`/
`Cochain.units_smul_comp`. Degrees stay `m + n` with the same `zero_add`/
`add_zero` transports as `conv`. -/
theorem conv_smul_left {m n : ℤ} (k : ℤˣ)
    (f : HomComplex.Cochain C A m) (g : HomComplex.Cochain C A n) :
    conv (k • f) g = k • conv f g := by
  unfold conv
  rw [tensorCochain_smul_left, HomComplex.Cochain.comp_units_smul,
    HomComplex.Cochain.units_smul_comp]

/-- A `ℤˣ` scalar on the right factor pushes through convolution, reusing
`tensorCochain_smul_right` and the pinned `Cochain.comp_units_smul`/
`Cochain.units_smul_comp`. Degrees stay `m + n` with the same `zero_add`/
`add_zero` transports as `conv`. -/
theorem conv_smul_right {m n : ℤ} (k : ℤˣ)
    (f : HomComplex.Cochain C A m) (g : HomComplex.Cochain C A n) :
    conv f (k • g) = k • conv f g := by
  unfold conv
  rw [tensorCochain_smul_right, HomComplex.Cochain.comp_units_smul,
    HomComplex.Cochain.units_smul_comp]

end CochainComplex
