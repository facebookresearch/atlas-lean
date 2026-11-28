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
# Graded convolution and augmented twisting cochains

Let R be commutative and C,A cochain complexes of R-modules indexed by ℤ. A degree-m cochain
is a family f_i : C_i → A_{i+m}. Its Hom differential has component f_i ≫ d_A + (−1)^{m+1} d_C
≫ f_{i+1}. For degree-m and degree-n cochains f,g, their tensor product acts on source degrees
i,j by (−1)^{ni}(f_i ⊗ g_j), with total degree m+n.

With C a comonoid and A a monoid in the cochain tensor category, define f⋆g = Δ_C followed by
f⊗g and then μ_A. The stated graded coproduct, empty-colimit preservation and iterated tensor
coherence hypotheses provide these maps. Convolution preserves the two zero laws and commutes
with monoid postcomposition and comonoid precomposition.

An augmented twisting cochain consists of τ of degree one, a comonoid coaugmentation η : I →
C, a monoid augmentation ε : A → I, the equations τ∘η=0 and ε∘τ=0, and δτ+τ⋆τ=0 in degree 1+1.
The unit comonoid in the coaugmentation field is the canonical tensor-unit structure.

Reference: J.-L. Loday and B. Vallette, Algebraic Operads, Grundlehren 346, Springer, 2012,
https://doi.org/10.1007/978-3-642-30362-3.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

namespace CochainComplex

variable {R : Type*} [CommRing R]
variable {C A : CochainComplex (ModuleCat R) ℤ}

variable [∀ (X₁ X₂ : GradedObject ℤ (ModuleCat R)), GradedObject.HasTensor X₁ X₂]

/-- Koszul sign on a tensor summand of homogeneous cochains.

For f of degree m, g of degree n and source degrees i₁+i₂=r, the map to (A⊗A)_s with s=r+m+n
is (−1)^{ni₁}(f_{i₁} ⊗ g_{i₂}) followed by the inclusion of output degrees i₁+m and i₂+n. -/
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

/-- Tensor product of homogeneous cochains.

For f,g : C → A of integer degrees m,n, use the graded tensor coproduct to assemble the maps
(−1)^{ni}(f_i⊗g_j). This gives a cochain C⊗C → A⊗A of degree m+n. -/
noncomputable def tensorCochain {m n : ℤ} (f : HomComplex.Cochain C A m)
    (g : HomComplex.Cochain C A n) :
    HomComplex.Cochain (HomologicalComplex.tensorObj C C)
      (HomologicalComplex.tensorObj A A) (m + n) :=
  HomComplex.Cochain.mk fun r s hrs =>
    HomologicalComplex.mapBifunctorDesc (F := curriedTensor (ModuleCat R))
      (c := ComplexShape.up ℤ) fun i₁ i₂ hij =>
      convSummand f g r s hrs i₁ i₂ hij

/-- Degree component of the tensor product of cochains.

At r,s with r+m+n=s, tensorCochain(f,g) is the coproduct descendant of the signed tensor maps
on every source bidegree i+j=r. -/
@[simp]
lemma tensorCochain_v {m n : ℤ} (f : HomComplex.Cochain C A m)
    (g : HomComplex.Cochain C A n) (r s : ℤ) (hrs : r + (m + n) = s) :
    (tensorCochain f g).v r s hrs =
      HomologicalComplex.mapBifunctorDesc (F := curriedTensor (ModuleCat R))
        (c := ComplexShape.up ℤ) fun i₁ i₂ hij =>
        convSummand f g r s hrs i₁ i₂ hij := rfl

/-- Agreement with the general tensor product of Hom cochains.

For cochains f,g with the same source C and target A, tensorCochain f g equals
HomComplex.Cochain.tensor f g. Both use the sign (−1)^{ni} for the right cochain degree n and
left source degree i. -/
theorem tensorCochain_eq_tensor {m n : ℤ} (f : HomComplex.Cochain C A m)
    (g : HomComplex.Cochain C A n) :
    tensorCochain f g = HomComplex.Cochain.tensor f g := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [tensorCochain_v, HomComplex.Cochain.tensor_v]
  rfl

/-- Zero left factor in a tensor product of cochains.

For any degree-n cochain g and integer m, tensorCochain(0,g) is the zero degree-(m+n) cochain. -/
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

/-- Zero right factor in a tensor product of cochains.

For any degree-m cochain f and integer n, tensorCochain(f,0) is the zero degree-(m+n) cochain. -/
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

/-- Graded convolution of homogeneous cochains.

For a cochain comonoid C and monoid A, define f⋆g as the degree-zero coproduct Δ_C followed by
tensorCochain(f,g) and the degree-zero multiplication μ_A. Its degree is m+n for f of degree m
and g of degree n. -/
noncomputable def conv {m n : ℤ} (f : HomComplex.Cochain C A m)
    (g : HomComplex.Cochain C A n) : HomComplex.Cochain C A (m + n) :=
  ((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
    (tensorCochain f g) (zero_add (m + n))).comp
    (HomComplex.Cochain.ofHom (MonObj.mul (X := A))) (add_zero (m + n))

/-- Vanishing convolution with a zero left cochain.

For a cochain comonoid C, monoid A and any homogeneous g, 0⋆g=0 in the sum of the two degrees. -/
lemma conv_zero_left {m n : ℤ} (g : HomComplex.Cochain C A n) :
    conv (0 : HomComplex.Cochain C A m) g = 0 := by
  unfold conv
  rw [tensorCochain_zero_left, HomComplex.Cochain.comp_zero,
    HomComplex.Cochain.zero_comp]

/-- Vanishing convolution with a zero right cochain.

For a cochain comonoid C, monoid A and any homogeneous f, f⋆0=0 in the sum of the two degrees. -/
lemma conv_zero_right {m n : ℤ} (f : HomComplex.Cochain C A m) :
    conv f (0 : HomComplex.Cochain C A n) = 0 := by
  unfold conv
  rw [tensorCochain_zero_right, HomComplex.Cochain.comp_zero,
    HomComplex.Cochain.zero_comp]

/-- Monoid-morphism naturality of convolution.

For a monoid morphism φ : A → B and homogeneous f,g : C → A, postcomposing f⋆g with φ equals
the convolution of f followed by φ and g followed by φ. All cochain degrees m,n and m+n are
retained. -/
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

/-- Comonoid-morphism naturality of convolution.

For a comonoid morphism ψ : C' → C and homogeneous f,g : C → A, precomposing f⋆g with ψ equals
the convolution of ψ followed by f and ψ followed by g. -/
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

/-- Augmented twisting cochain in cohomological degree one.

For a cochain comonoid C and monoid A over R, specify a degree-one cochain τ, comonoid
coaugmentation η : I → C and monoid augmentation ε : A → I. Require τ∘η=0, ε∘τ=0 and δτ+τ⋆τ=0
in degree 1+1. -/
structure TwistingCochain where
  /-- Underlying degree-one homogeneous twisting cochain.

The underlying family has components τ_i : C_i → A_{i+1} for every integer i. Its differential
is constrained by the Maurer–Cartan field. -/
  tau : HomComplex.Cochain C A 1
  /-- Source coaugmentation of a twisting cochain.

The map η : I → C is a degree-zero chain morphism; the coaug_isComonHom field makes it a
comonoid map from the canonical unit comonoid. -/
  coaug : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C
  /-- Target augmentation of a twisting cochain.

The map ε : A → I is a degree-zero chain morphism; the aug_isMonHom field makes it a monoid
map to the tensor-unit monoid. -/
  aug : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ)
  /-- Comonoid compatibility of the twisting coaugmentation.

Require η : I → C to preserve counit and coproduct, with the canonical ComonObj.instTensorUnit
structure on I. -/
  coaug_isComonHom : letI := ComonObj.instTensorUnit (CochainComplex (ModuleCat R) ℤ)
    ; IsComonHom coaug
  /-- Monoid compatibility of the twisting augmentation.

Require ε : A → I to preserve the monoid unit and multiplication. -/
  aug_isMonHom : IsMonHom aug
  /-- Vanishing of the twisting cochain on the coaugmentation.

The composite of the degree-zero coaugmentation η with the degree-one cochain τ is zero, as a
cochain of degree 0+1. -/
  coaug_vanish : (HomComplex.Cochain.ofHom coaug).comp tau (zero_add 1) = 0
  /-- Vanishing of the augmented twisting cochain.

The degree-one cochain τ followed by the degree-zero augmentation ε is zero, as a cochain of
degree 1+0. -/
  aug_vanish : tau.comp (HomComplex.Cochain.ofHom aug) (add_zero 1) = 0
  /-- Maurer–Cartan identity in cohomological degree two.

The degree-one twisting cochain satisfies HomComplex.δ 1 (1+1) τ + conv τ τ = 0. Both terms
have degree 1+1 with the stated Hom and Koszul sign conventions. -/
  maurer_cartan : HomComplex.δ 1 (1 + 1) tau + conv tau tau = 0

/-- Bundled comonoid coaugmentation of a twisting cochain.

The map τ.coaug and its comonoid-preservation field define a morphism from the canonical
tensor-unit comonoid to the comonoid C. -/
def TwistingCochain.coaugHom (τ : TwistingCochain (R := R) (C := C) (A := A)) :
    Comon.trivial _ ⟶ Comon.mk C :=
  letI := ComonObj.instTensorUnit (CochainComplex (ModuleCat R) ℤ)
  { hom := τ.coaug, isComonHom_hom := τ.coaug_isComonHom }

/-- Bundled monoid augmentation of a twisting cochain.

The map τ.aug and its monoid-preservation field define a morphism from the monoid A to the
canonical tensor-unit monoid. -/
def TwistingCochain.augHom (τ : TwistingCochain (R := R) (C := C) (A := A)) :
    Mon.mk A ⟶ Mon.trivial _ :=
  { hom := τ.aug, isMonHom_hom := τ.aug_isMonHom }

/-- Underlying map of the bundled twisting coaugmentation.

The hom of τ.coaugHom is exactly τ.coaug : I → C. -/
@[simp]
lemma TwistingCochain.coaugHom_hom (τ : TwistingCochain (R := R) (C := C) (A := A)) :
    (τ.coaugHom).hom = τ.coaug := by
  unfold TwistingCochain.coaugHom
  rfl

/-- Underlying map of the bundled twisting augmentation.

The hom of τ.augHom is exactly τ.aug : A → I. -/
@[simp]
lemma TwistingCochain.augHom_hom (τ : TwistingCochain (R := R) (C := C) (A := A)) :
    (τ.augHom).hom = τ.aug := rfl

end CochainComplex
