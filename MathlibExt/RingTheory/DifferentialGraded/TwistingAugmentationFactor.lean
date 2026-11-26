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
# Reduced cochains and convolution vanishing

Let C be a cochain comonoid and A a cochain monoid over a commutative ring, with the stated
graded tensor structures. For maps η : I → C and ε : A → I, a degree-m cochain f is reduced
when η followed by f and f followed by ε are zero as degree-m cochains.

When I has a comonoid structure making η a comonoid morphism and ε is a monoid morphism,
convolution of degree-m and degree-n cochains is reduced if either factor is reduced. The
total degree is m+n. Each twisting cochain is reduced for its own maps, and convolution
against either of its zero outer composites vanishes.
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

/-- Two-sided reduction of a homogeneous cochain.

For η : I → C, ε : A → I and f of degree m, require (ofHom η).comp f = 0 in degree 0+m and
f.comp(ofHom ε) = 0 in degree m+0. These equations define IsReducedCochain η ε f. -/
def IsReducedCochain {m : ℤ} (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ))
    (f : HomComplex.Cochain C A m) : Prop :=
  (HomComplex.Cochain.ofHom η).comp f (zero_add m) = 0 ∧
    f.comp (HomComplex.Cochain.ofHom ε) (add_zero m) = 0

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [MonObj A] [ComonObj C] in
/-- Reduction of the zero homogeneous cochain.

For any η,ε and integer m, the zero degree-m cochain is reduced because both outer composites
with it vanish. -/
theorem IsReducedCochain.zero {m : ℤ}
    (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ)) :
    IsReducedCochain (m := m) η ε 0 :=
  ⟨HomComplex.Cochain.comp_zero _ _, HomComplex.Cochain.zero_comp _ _⟩

/-- Convolution vanishing from a twisting coaugmentation composite.

For a twisting cochain τ, its composite (ofHom τ.coaug).comp τ.tau is zero in degree one.
Convolving this on the left with any degree-n cochain I → A gives zero. A comonoid structure
on I is assumed to define this convolution source. -/
theorem conv_reduced_left (τ : TwistingCochain (R := R) (C := C) (A := A))
    [ComonObj (𝟙_ (CochainComplex (ModuleCat R) ℤ))]
    {n : ℤ} (g : HomComplex.Cochain (𝟙_ (CochainComplex (ModuleCat R) ℤ)) A n) :
    conv ((HomComplex.Cochain.ofHom τ.coaug).comp τ.tau (zero_add 1)) g = 0 := by
  rw [τ.coaug_vanish, conv_zero_left]

/-- Convolution vanishing from a twisting augmentation composite.

For τ, the degree-one composite τ.tau.comp(ofHom τ.aug) is zero. Convolution of any degree-n
cochain C → I with this zero right factor is zero, using the tensor-unit monoid. -/
theorem conv_reduced_right (τ : TwistingCochain (R := R) (C := C) (A := A))
    {n : ℤ} (g : HomComplex.Cochain C (𝟙_ (CochainComplex (ModuleCat R) ℤ)) n) :
    conv g (τ.tau.comp (HomComplex.Cochain.ofHom τ.aug) (add_zero 1)) = 0 := by
  rw [τ.aug_vanish, conv_zero_right]

/-- Reduction of a twisting cochain in its own maps.

For τ, the coaugmentation and augmentation vanishing fields give IsReducedCochain τ.coaug
τ.aug τ.tau. -/
theorem TwistingCochain.reduced (τ : TwistingCochain (R := R) (C := C) (A := A)) :
    IsReducedCochain τ.coaug τ.aug τ.tau :=
  ⟨τ.coaug_vanish, τ.aug_vanish⟩

/-- Reduction of convolution from a reduced left factor.

Assume a comonoid structure on I, η : I → C a comonoid morphism and ε : A → I a monoid
morphism. If f of degree m is reduced, then f⋆g of degree m+n is reduced for every degree-n
cochain g. The outer morphisms commute with convolution and the zero left factor annihilates
it. -/
theorem IsReducedCochain.conv_of_left {m n : ℤ}
    {η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C}
    {ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ)}
    [ComonObj (𝟙_ (CochainComplex (ModuleCat R) ℤ))]
    [IsComonHom η] [IsMonHom ε]
    {f : HomComplex.Cochain C A m} (g : HomComplex.Cochain C A n)
    (hf : IsReducedCochain η ε f) :
    IsReducedCochain η ε (conv f g) := by
  refine ⟨?_, ?_⟩
  · rw [conv_precomp f g η, hf.1, conv_zero_left]
  · rw [conv_postcomp f g ε, hf.2, conv_zero_left]

/-- Reduction of convolution from a reduced right factor.

Assume a comonoid structure on I, η a comonoid morphism and ε a monoid morphism. For any
degree-m cochain f, if g of degree n is reduced, then f⋆g is reduced in degree m+n. -/
theorem IsReducedCochain.conv_of_right {m n : ℤ}
    {η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C}
    {ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ)}
    [ComonObj (𝟙_ (CochainComplex (ModuleCat R) ℤ))]
    [IsComonHom η] [IsMonHom ε]
    (f : HomComplex.Cochain C A m) {g : HomComplex.Cochain C A n}
    (hg : IsReducedCochain η ε g) :
    IsReducedCochain η ε (conv f g) := by
  refine ⟨?_, ?_⟩
  · rw [conv_precomp f g η, hg.1, conv_zero_right]
  · rw [conv_postcomp f g ε, hg.2, conv_zero_right]

end CochainComplex
