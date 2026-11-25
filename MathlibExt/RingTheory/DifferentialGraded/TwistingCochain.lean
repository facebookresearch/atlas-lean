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

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.ComplexShapeSigns
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.Comon_
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import MathlibExt.Algebra.Homology.TensorCochainCoherence

/-!
# Twisting cochains between dg coalgebras and dg algebras

Let `R` be a commutative ring and `C A : CochainComplex (ModuleCat R) ℤ` with
`[ComonObj C]` and `[MonObj A]` for the pinned tensor product of cochain
complexes (`HomologicalComplex.monoidalCategory` at the cohomological
`ComplexShape.up ℤ` shape).

This file defines the graded
convolution product of homogeneous cochains and the type of twisting cochains:
degree-`+1` solutions of the Maurer–Cartan equation with explicit
augmentation/coaugmentation vanishing.

## Grading and sign conventions

* Cohomological grading throughout: `HomComplex.Cochain C A n` is a family
  `C.X p ⟶ A.X q` with `p + n = q`, and `HomComplex.δ` is the pinned
  differential (Conrad signs).
* For `f : Cochain C A m` and `g : Cochain C A n`, the graded tensor product
  `tensorCochain f g : Cochain (C ⊗ C) (A ⊗ A) (m + n)` acts on the
  `(i₁, i₂)`-summand (`i₁ + i₂ = r`) by the Koszul rule
  `(f ⊗ g)(x ⊗ y) = (-1) ^ (n * i₁) • (f x ⊗ g y)`,
  where the sign is `Int.negOnePow (n * i₁)`. This matches the pinned
  tensor-complex convention, whose vertical sign is `(up ℤ).ε` on the second
  factor (`ComplexShape.ε_up_ℤ`).
* The convolution is `f ⋆ g = μ ∘ (f ⊗ g) ∘ Δ`, assembled from
  `ComonObj.comul`, `tensorCochain`, and `MonObj.mul` via `Cochain.comp`.
* Convolution commutes with postcomposition by a monoid morphism
  (`conv_postcomp`) and precomposition by a comonoid morphism
  (`conv_precomp`), via the pinned tensor coherence.
* A twisting cochain is `τ : Cochain C A 1` carried together with a comonoid
  coaugmentation `η : 𝟙_ _ ⟶ C` (see `TwistingCochain.coaug_isComonHom`) and a
  monoid augmentation `ε : A ⟶ 𝟙_ _` (see `TwistingCochain.aug_isMonHom`) such
  that `τ ∘ η = 0`, `ε ∘ τ = 0` (as degree-`1` cochains), and the
  Maurer–Cartan equation `δ 1 (1 + 1) τ + τ ⋆ τ = 0` holds in degree `1 + 1`.
  The bundled morphisms are `TwistingCochain.coaugHom` and
  `TwistingCochain.augHom`.

## Primary source and convention map

The standard general reference for convolution products, twisting morphisms as
Maurer–Cartan elements, and the bar–cobar adjunction is J.-L. Loday and
B. Vallette, *Algebraic Operads*, Grundlehren 346, Springer, 2012,
<https://doi.org/10.1007/978-3-642-30362-3>.

Explicit map to this implementation (without a sign-match claim): everything
here is cohomological (`up ℤ`); a twisting cochain is a degree-`+1` cochain
with Maurer–Cartan equation `δ 1 (1 + 1) τ + conv τ τ = 0` in degree `1 + 1`;
the differential is the pinned `HomComplex.δ` (Conrad signs) and the Koszul
sign is `Int.negOnePow (n * i₁)` as stated above. The classical homological
degree `-1` translates to cohomological degree `+1` by negation. Exact
printed-section numbers and a sign-level match against the printed text were
not verified in this environment, so none is claimed here.

## Nonclaims

* No homological (`down ℤ`) API is provided; everything is cohomological.
* `MonObj`/`ComonObj` do not supply (co)augmentations; those are explicit
  comonoid/monoid-morphism fields and are not inferred from the (co)unit.
* The ungraded `WithConv` convolution ring on `C →ₗ[R] A` is not used here and
  is not claimed to agree with the graded product.
* No bar–cobar adjunction, no conilpotence/completeness hypothesis, and no
  derived, Koszul, operadic, or model-categorical result is claimed.
* Associativity, unitality, and the Leibniz rule for the graded product are
  not proved here.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

namespace CochainComplex

variable {R : Type*} [CommRing R]
variable {C A : CochainComplex (ModuleCat R) ℤ}

variable [∀ (X₁ X₂ : GradedObject ℤ (ModuleCat R)), GradedObject.HasTensor X₁ X₂]

/-- The `(i₁, i₂)`-summand of the graded tensor product of the cochains `f`
and `g`: the Koszul-signed map
`(-1) ^ (n * i₁) • (f ⊗ₘ g)` followed by the summand inclusion into
`(A ⊗ A).X s`. -/
noncomputable def convSummand {m n : ℤ} (f : HomComplex.Cochain C A m)
    (g : HomComplex.Cochain C A n) (r s : ℤ) (hrs : r + (m + n) = s)
    (i₁ i₂ : ℤ)
    (hij : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⟨i₁, i₂⟩ = r) :
    C.X i₁ ⊗ C.X i₂ ⟶ (HomologicalComplex.tensorObj A A).X s := by
  have h12 : i₁ + i₂ = r := hij
  exact (n * i₁).negOnePow •
      (f.v i₁ (i₁ + m) rfl ⊗ₘ g.v i₂ (i₂ + n) rfl) ≫
    HomologicalComplex.ιTensorObj A A (i₁ + m) (i₂ + n) s (by omega)

/-- The graded tensor product of homogeneous cochains, of degree `m + n`,
built from the pinned tensor-complex inclusions via `mapBifunctorDesc`. -/
noncomputable def tensorCochain {m n : ℤ} (f : HomComplex.Cochain C A m)
    (g : HomComplex.Cochain C A n) :
    HomComplex.Cochain (HomologicalComplex.tensorObj C C)
      (HomologicalComplex.tensorObj A A) (m + n) :=
  HomComplex.Cochain.mk fun r s hrs =>
    HomologicalComplex.mapBifunctorDesc (F := curriedTensor (ModuleCat R))
      (c := ComplexShape.up ℤ) fun i₁ i₂ hij =>
      convSummand f g r s hrs i₁ i₂ hij

/-- Computation rule for the graded tensor product of cochains. -/
@[simp]
lemma tensorCochain_v {m n : ℤ} (f : HomComplex.Cochain C A m)
    (g : HomComplex.Cochain C A n) (r s : ℤ) (hrs : r + (m + n) = s) :
    (tensorCochain f g).v r s hrs =
      HomologicalComplex.mapBifunctorDesc (F := curriedTensor (ModuleCat R))
        (c := ComplexShape.up ℤ) fun i₁ i₂ hij =>
        convSummand f g r s hrs i₁ i₂ hij := rfl

/-- Diagonal specialization of the graded tensor product: on the same-source/target
`ModuleCat R` pair, `tensorCochain` agrees with the heterogeneous
`HomComplex.Cochain.tensor`. Both sides use the Koszul orientation
`(f ⊗ g)(x ⊗ y) = (-1) ^ (n * i₁) • (f x ⊗ g y)`. This bridge lets downstream
convolution reuse the heterogeneous functoriality/associativity API. It does not by
itself prove convolution associativity. -/
theorem tensorCochain_eq_tensor {m n : ℤ} (f : HomComplex.Cochain C A m)
    (g : HomComplex.Cochain C A n) :
    tensorCochain f g = HomComplex.Cochain.tensor f g := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [tensorCochain_v, HomComplex.Cochain.tensor_v]
  rfl

/-- The graded tensor product vanishes when the left factor vanishes. -/
lemma tensorCochain_zero_left {m n : ℤ} (g : HomComplex.Cochain C A n) :
    tensorCochain (0 : HomComplex.Cochain C A m) g = 0 := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [tensorCochain_v, HomComplex.Cochain.zero_v]
  apply HomologicalComplex.mapBifunctor.hom_ext (c := ComplexShape.up ℤ)
  intro i₁ i₂ hh
  rw [HomologicalComplex.ι_mapBifunctorDesc]
  simp only [convSummand, HomComplex.Cochain.zero_v,
    MonoidalPreadditive.zero_tensor, smul_zero, zero_comp, comp_zero]

/-- The graded tensor product vanishes when the right factor vanishes. -/
lemma tensorCochain_zero_right {m n : ℤ} (f : HomComplex.Cochain C A m) :
    tensorCochain f (0 : HomComplex.Cochain C A n) = 0 := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [tensorCochain_v, HomComplex.Cochain.zero_v]
  apply HomologicalComplex.mapBifunctor.hom_ext (c := ComplexShape.up ℤ)
  intro i₁ i₂ hh
  rw [HomologicalComplex.ι_mapBifunctorDesc]
  simp only [convSummand, HomComplex.Cochain.zero_v,
    MonoidalPreadditive.tensor_zero, smul_zero, zero_comp, comp_zero]

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

/-- The graded convolution product `f ⋆ g = μ ∘ (f ⊗ g) ∘ Δ` of homogeneous
cochains, of degree `m + n`. -/
noncomputable def conv {m n : ℤ} (f : HomComplex.Cochain C A m)
    (g : HomComplex.Cochain C A n) : HomComplex.Cochain C A (m + n) :=
  ((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
    (tensorCochain f g) (zero_add (m + n))).comp
    (HomComplex.Cochain.ofHom (MonObj.mul (X := A))) (add_zero (m + n))

/-- The graded convolution product vanishes when the left factor vanishes. -/
lemma conv_zero_left {m n : ℤ} (g : HomComplex.Cochain C A n) :
    conv (0 : HomComplex.Cochain C A m) g = 0 := by
  unfold conv
  rw [tensorCochain_zero_left, HomComplex.Cochain.comp_zero,
    HomComplex.Cochain.zero_comp]

/-- The graded convolution product vanishes when the right factor vanishes. -/
lemma conv_zero_right {m n : ℤ} (f : HomComplex.Cochain C A m) :
    conv f (0 : HomComplex.Cochain C A n) = 0 := by
  unfold conv
  rw [tensorCochain_zero_right, HomComplex.Cochain.comp_zero,
    HomComplex.Cochain.zero_comp]

/-- Convolution commutes with postcomposition by a monoid morphism.

For `f : Cochain C A m`, `g : Cochain C A n`, and `φ : A ⟶ B` with
`IsMonHom φ`, postcomposing `conv f g` equals the convolution of the
postcomposed factors. The proof reuses the heterogeneous tensor postcomposition
coherence and the cochain lift of `IsMonHom.mul_hom`. -/
theorem conv_postcomp {m n : ℤ} (f : HomComplex.Cochain C A m)
    (g : HomComplex.Cochain C A n) (φ : A ⟶ B) [IsMonHom φ] :
    (conv f g).comp (HomComplex.Cochain.ofHom φ) (add_zero (m + n)) =
      conv (f.comp (HomComplex.Cochain.ofHom φ) (add_zero m))
        (g.comp (HomComplex.Cochain.ofHom φ) (add_zero n)) := by
  have hmul : MonObj.mul (X := A) ≫ φ =
      HomologicalComplex.tensorHom φ φ ≫ MonObj.mul (X := B) :=
    IsMonHom.mul_hom φ
  have hmul_ofHom :
      (HomComplex.Cochain.ofHom (MonObj.mul (X := A))).comp
        (HomComplex.Cochain.ofHom φ) (zero_add 0) =
      (HomComplex.Cochain.ofHom (HomologicalComplex.tensorHom φ φ)).comp
        (HomComplex.Cochain.ofHom (MonObj.mul (X := B))) (zero_add 0) := by
    have hOf := congrArg HomComplex.Cochain.ofHom hmul
    rw [HomComplex.Cochain.ofHom_comp] at hOf
    rw [HomComplex.Cochain.ofHom_comp] at hOf
    exact hOf
  unfold conv
  rw [tensorCochain_eq_tensor, tensorCochain_eq_tensor]
  simp only [HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain,
    HomComplex.Cochain.comp_assoc_of_second_is_zero_cochain]
  rw [hmul_ofHom]
  rw [← HomComplex.Cochain.comp_assoc_of_second_is_zero_cochain]
  rw [HomComplex.Cochain.tensor_comp_ofHom_tensorHom]

/-- Convolution commutes with precomposition by a comonoid morphism.

For `f : Cochain C A m`, `g : Cochain C A n`, and `ψ : C' ⟶ C` with
`IsComonHom ψ`, precomposing `conv f g` equals the convolution of the
precomposed factors. The proof reuses the heterogeneous tensor precomposition
coherence and the cochain lift of `IsComonHom.hom_comul`. -/
theorem conv_precomp {m n : ℤ} (f : HomComplex.Cochain C A m)
    (g : HomComplex.Cochain C A n) (ψ : C' ⟶ C) [IsComonHom ψ] :
    (HomComplex.Cochain.ofHom ψ).comp (conv f g) (zero_add (m + n)) =
      conv ((HomComplex.Cochain.ofHom ψ).comp f (zero_add m))
        ((HomComplex.Cochain.ofHom ψ).comp g (zero_add n)) := by
  have hcomul : ψ ≫ ComonObj.comul (X := C) =
      ComonObj.comul (X := C') ≫ HomologicalComplex.tensorHom ψ ψ :=
    IsComonHom.hom_comul ψ
  have hcomul_ofHom :
      (HomComplex.Cochain.ofHom ψ).comp
        (HomComplex.Cochain.ofHom (ComonObj.comul (X := C))) (zero_add 0) =
      (HomComplex.Cochain.ofHom (ComonObj.comul (X := C'))).comp
        (HomComplex.Cochain.ofHom (HomologicalComplex.tensorHom ψ ψ))
        (zero_add 0) := by
    have hOf := congrArg HomComplex.Cochain.ofHom hcomul
    rw [HomComplex.Cochain.ofHom_comp] at hOf
    rw [HomComplex.Cochain.ofHom_comp] at hOf
    exact hOf
  unfold conv
  rw [tensorCochain_eq_tensor, tensorCochain_eq_tensor]
  simp only [HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [← HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [hcomul_ofHom]
  rw [HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [← HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain
    (HomComplex.Cochain.ofHom (HomologicalComplex.tensorHom ψ ψ))]
  rw [HomComplex.Cochain.ofHom_tensorHom_comp_tensor]

/-- A twisting cochain from the dg coalgebra `C` to the dg algebra `A`: a
degree-`+1` cochain with comonoid/monoid (co)augmentation morphisms, explicit
(co)augmentation vanishing, and the Maurer–Cartan equation `δ τ + τ ⋆ τ = 0`
in degree `1 + 1`. -/
structure TwistingCochain where
  /-- The underlying degree-`+1` cochain. -/
  tau : HomComplex.Cochain C A 1
  /-- Explicit coaugmentation of the source, as a comonoid morphism from the
  tensor-unit comonoid (see `coaug_isComonHom` and `coaugHom`). -/
  coaug : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C
  /-- Explicit augmentation of the target, as a monoid morphism to the
  tensor-unit monoid (see `aug_isMonHom` and `augHom`). -/
  aug : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ)
  /-- Coaugmentation is a comonoid morphism from the canonical tensor-unit
  comonoid `ComonObj.instTensorUnit`. -/
  coaug_isComonHom : letI := ComonObj.instTensorUnit (CochainComplex (ModuleCat R) ℤ)
    ; IsComonHom coaug
  /-- Augmentation is a monoid morphism to the tensor-unit monoid. -/
  aug_isMonHom : IsMonHom aug
  /-- Vanishing on the coaugmentation: `τ ∘ η = 0`. -/
  coaug_vanish : (HomComplex.Cochain.ofHom coaug).comp tau (zero_add 1) = 0
  /-- Vanishing on the augmentation: `ε ∘ τ = 0`. -/
  aug_vanish : tau.comp (HomComplex.Cochain.ofHom aug) (add_zero 1) = 0
  /-- Maurer–Cartan equation in degree `1 + 1`. -/
  maurer_cartan : HomComplex.δ 1 (1 + 1) tau + conv tau tau = 0

/-- Bundled coaugmentation as a comonoid morphism from the trivial comonoid.
Uses a local tensor-unit `ComonObj` instance only; no global instance is
introduced. -/
def TwistingCochain.coaugHom (τ : TwistingCochain (R := R) (C := C) (A := A)) :
    Comon.trivial _ ⟶ Comon.mk C :=
  letI := ComonObj.instTensorUnit (CochainComplex (ModuleCat R) ℤ)
  { hom := τ.coaug, isComonHom_hom := τ.coaug_isComonHom }

/-- Bundled augmentation as a monoid morphism to the trivial monoid. -/
def TwistingCochain.augHom (τ : TwistingCochain (R := R) (C := C) (A := A)) :
    Mon.mk A ⟶ Mon.trivial _ :=
  { hom := τ.aug, isMonHom_hom := τ.aug_isMonHom }

/-- Underlying map of the bundled coaugmentation. -/
@[simp]
lemma TwistingCochain.coaugHom_hom (τ : TwistingCochain (R := R) (C := C) (A := A)) :
    (τ.coaugHom).hom = τ.coaug := by
  unfold TwistingCochain.coaugHom
  rfl

/-- Underlying map of the bundled augmentation. -/
@[simp]
lemma TwistingCochain.augHom_hom (τ : TwistingCochain (R := R) (C := C) (A := A)) :
    (τ.augHom).hom = τ.aug := rfl

end CochainComplex
