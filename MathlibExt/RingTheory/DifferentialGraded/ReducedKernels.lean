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

public import MathlibExt.RingTheory.DifferentialGraded.TwistingAugmentationFactor
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Reduced kernels for twisting cochains

This file packages only kernel/cokernel objects and universal-property maps
for explicit augmentation/coaugmentation morphisms of cochain complexes. It is
the smallest generic-first C14 kernel/cokernel specialization.

For explicit `ε : A ⟶ 𝟙_` and `η : 𝟙_ ⟶ C`, `augIdeal ε := kernel ε` with its
inclusion, condition, lift, computation, and uniqueness, and dually
`coaugCoideal η := cokernel η` with its projection, condition, desc,
computation, and uniqueness. Degree-zero `ofHom` vanishing lemmas and thin
`TwistingCochain` wrappers reuse the public reducedness/vanishing fields.

## Declaration inventory

* `augIdeal`, `augIdealι`, `augIdeal_condition`, `augIdeal_lift`,
  `augIdeal_lift_ι`, `augIdeal_lift_unique`.
* `coaugCoideal`, `coaugCoidealπ`, `coaugCoideal_condition`, `coaugCoideal_desc`,
  `coaugCoideal_π_desc`, `coaugCoideal_desc_unique`.
* `coaugCoidealMap`, `coaugCoideal_π_map`, `coaugCoidealMap_id`,
  `coaugCoidealMap_comp`.
* `ofHom_augIdeal_vanish` at exactly `(add_zero 0)`, `ofHom_coaugCoideal_vanish`
  at exactly `(zero_add 0)`.
* `TwistingCochain.augIdeal_lift`, `TwistingCochain.augIdeal_lift_ι`,
  `TwistingCochain.coaugCoideal_desc`, `TwistingCochain.coaugCoideal_desc_π`.

## Nonclaims

These are only kernel/cokernel objects and universal-property maps: no `MonObj`
on the augmentation kernel, no `ComonObj` on the coaugmentation cokernel, no
reduced multiplication/comultiplication, no tensor-preservation claim, no
powers/filtrations/completeness/summability, no free/cofree universal property,
no representability/adjunction, and no C15/C16/KQ/operad result. No
unconditional non-factorization lemma is proved here; such a lemma would be
false over the trivial ring without extra nontriviality and morphism
hypotheses.

## Import justification

`TwistingAugmentationFactor` supplies the carrier/hypothesis block, `conv`,
and the `TwistingCochain` structure with its reducedness fields.
`HomologicalComplexAbelian` supplies `Abelian (HomologicalComplex …)`, hence
kernels/cokernels for `CochainComplex (ModuleCat R) ℤ`.
`ModuleCat.Abelian` supplies `Abelian (ModuleCat R)`. No other import is used.
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

/-- Augmentation ideal as a kernel object only; no ideal monoid structure. -/
noncomputable def augIdeal (ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ)) :
    CochainComplex (ModuleCat R) ℤ :=
  kernel ε

/-- Inclusion of the augmentation kernel. -/
noncomputable def augIdealι (ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ)) :
    augIdeal ε ⟶ A :=
  kernel.ι ε

/-- Coaugmentation coideal as a cokernel object only; no coideal comonoid
structure. -/
noncomputable def coaugCoideal (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C) :
    CochainComplex (ModuleCat R) ℤ :=
  cokernel η

/-- Projection onto the coaugmentation cokernel. -/
noncomputable def coaugCoidealπ (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C) :
    C ⟶ coaugCoideal η :=
  cokernel.π η

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [MonObj A] in
/-- Kernel condition: the inclusion followed by the augmentation is zero. -/
theorem augIdeal_condition (ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ)) :
    augIdealι ε ≫ ε = 0 :=
  kernel.condition ε

/-- Generic lift through the augmentation kernel. -/
noncomputable def augIdeal_lift (ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ))
    {X : CochainComplex (ModuleCat R) ℤ} (f : X ⟶ A) (h : f ≫ ε = 0) :
    X ⟶ augIdeal ε :=
  kernel.lift ε f h

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [MonObj A] in
/-- Computation for the augmentation-kernel lift. -/
theorem augIdeal_lift_ι (ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ))
    {X : CochainComplex (ModuleCat R) ℤ} (f : X ⟶ A) (h : f ≫ ε = 0) :
    augIdeal_lift ε f h ≫ augIdealι ε = f :=
  kernel.lift_ι ε f h

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [MonObj A] in
/-- Uniqueness for the augmentation-kernel lift via the pinned generic kernel
universal property. -/
theorem augIdeal_lift_unique (ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ))
    {X : CochainComplex (ModuleCat R) ℤ} (f : X ⟶ A) (h : f ≫ ε = 0)
    (g : X ⟶ augIdeal ε) (hg : g ≫ augIdealι ε = f) :
    g = augIdeal_lift ε f h := by
  unfold augIdeal augIdeal_lift augIdealι at *
  have h1 : g ≫ kernel.ι ε = kernel.lift ε f h ≫ kernel.ι ε := by
    rw [hg, kernel.lift_ι]
  exact Fork.IsLimit.hom_ext (kernelIsKernel ε) h1

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [ComonObj C] in
/-- Cokernel condition: the coaugmentation followed by the projection is zero. -/
theorem coaugCoideal_condition (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C) :
    η ≫ coaugCoidealπ η = 0 :=
  cokernel.condition η

/-- Generic desc through the coaugmentation cokernel. -/
noncomputable def coaugCoideal_desc (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    {W : CochainComplex (ModuleCat R) ℤ} (k : C ⟶ W) (h : η ≫ k = 0) :
    coaugCoideal η ⟶ W :=
  cokernel.desc η k h

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [ComonObj C] in
/-- Computation for the coaugmentation-cokernel desc. -/
theorem coaugCoideal_π_desc (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    {W : CochainComplex (ModuleCat R) ℤ} (k : C ⟶ W) (h : η ≫ k = 0) :
    coaugCoidealπ η ≫ coaugCoideal_desc η k h = k :=
  cokernel.π_desc η k h

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [ComonObj C] in
/-- Uniqueness for the coaugmentation-cokernel desc via the pinned generic
cokernel universal property. -/
theorem coaugCoideal_desc_unique (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    {W : CochainComplex (ModuleCat R) ℤ} (k : C ⟶ W) (h : η ≫ k = 0)
    (g : coaugCoideal η ⟶ W) (hg : coaugCoidealπ η ≫ g = k) :
    g = coaugCoideal_desc η k h := by
  unfold coaugCoideal coaugCoideal_desc coaugCoidealπ at *
  have h1 : cokernel.π η ≫ g = cokernel.π η ≫ cokernel.desc η k h := by
    rw [hg, cokernel.π_desc]
  exact Cofork.IsColimit.hom_ext (cokernelIsCokernel η) h1

variable {D E : CochainComplex (ModuleCat R) ℤ}

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [ComonObj C] in
/-- Canonical map between coaugmentation coideals induced by a
coaugmentation-preserving morphism, via the existing cokernel descendant. -/
noncomputable def coaugCoidealMap
    (ηC : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (ηD : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ D) (f : C ⟶ D)
    (hη : ηC ≫ f = ηD) : coaugCoideal ηC ⟶ coaugCoideal ηD :=
  coaugCoideal_desc ηC (f ≫ coaugCoidealπ ηD) (by
    rw [← Category.assoc, hη]
    exact coaugCoideal_condition ηD)

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [ComonObj C] in
/-- Projection square for the canonical coaugmentation-coideal map. -/
theorem coaugCoideal_π_map
    (ηC : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (ηD : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ D) (f : C ⟶ D)
    (hη : ηC ≫ f = ηD) :
    coaugCoidealπ ηC ≫ coaugCoidealMap ηC ηD f hη = f ≫ coaugCoidealπ ηD :=
  coaugCoideal_π_desc ηC _ _

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [ComonObj C] in
/-- Identity coherence for the canonical coaugmentation-coideal map. -/
theorem coaugCoidealMap_id
    (ηC : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C) :
    coaugCoidealMap ηC ηC (𝟙 C) (Category.comp_id ηC) = 𝟙 _ := by
  have hπ : coaugCoidealπ ηC ≫ (𝟙 (coaugCoideal ηC)) =
      (𝟙 C) ≫ coaugCoidealπ ηC := by simp
  have hv : ηC ≫ ((𝟙 C) ≫ coaugCoidealπ ηC) = 0 := by
    rw [Category.id_comp]
    exact coaugCoideal_condition ηC
  have h := coaugCoideal_desc_unique ηC ((𝟙 C) ≫ coaugCoidealπ ηC) hv
    (𝟙 _) hπ
  simpa [coaugCoidealMap] using h.symm

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [ComonObj C] in
/-- Composition coherence for the canonical coaugmentation-coideal maps. -/
theorem coaugCoidealMap_comp
    (ηC : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (ηD : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ D)
    (ηE : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ E)
    (f : C ⟶ D) (g : D ⟶ E)
    (h₁ : ηC ≫ f = ηD) (h₂ : ηD ≫ g = ηE) :
    coaugCoidealMap ηC ηE (f ≫ g) (by rw [← Category.assoc, h₁, h₂]) =
      coaugCoidealMap ηC ηD f h₁ ≫ coaugCoidealMap ηD ηE g h₂ := by
  have hπ : coaugCoidealπ ηC ≫
      (coaugCoidealMap ηC ηD f h₁ ≫ coaugCoidealMap ηD ηE g h₂) =
      (f ≫ g) ≫ coaugCoidealπ ηE := by
    rw [← Category.assoc, coaugCoideal_π_map, Category.assoc,
      coaugCoideal_π_map, ← Category.assoc]
  have hfg : ηC ≫ (f ≫ g) = ηE := by rw [← Category.assoc, h₁, h₂]
  have hv : ηC ≫ ((f ≫ g) ≫ coaugCoidealπ ηE) = 0 := by
    rw [← Category.assoc, hfg]
    exact coaugCoideal_condition ηE
  have h := coaugCoideal_desc_unique ηC ((f ≫ g) ≫ coaugCoidealπ ηE) hv
    (_ ≫ _) hπ
  simpa [coaugCoidealMap] using h.symm

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [MonObj A] in
/-- Degree-zero augmentation vanishing from the generic kernel condition and
the pinned `ofHom` composition API, at exactly `(add_zero 0)`. -/
theorem ofHom_augIdeal_vanish (ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ)) :
    (HomComplex.Cochain.ofHom (augIdealι ε)).comp
      (HomComplex.Cochain.ofHom ε) (add_zero 0) = 0 := by
  have h : augIdealι ε ≫ ε = 0 := augIdeal_condition ε
  have h2 : HomComplex.Cochain.ofHom (augIdealι ε ≫ ε) =
      (HomComplex.Cochain.ofHom (augIdealι ε)).comp
        (HomComplex.Cochain.ofHom ε) (zero_add 0) :=
    HomComplex.Cochain.ofHom_comp _ _
  rw [h, HomComplex.Cochain.ofHom_zero] at h2
  exact h2.symm

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [ComonObj C] in
/-- Degree-zero coaugmentation vanishing from the generic cokernel condition
and the pinned `ofHom` composition API, at exactly `(zero_add 0)`. -/
theorem ofHom_coaugCoideal_vanish (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C) :
    (HomComplex.Cochain.ofHom η).comp
      (HomComplex.Cochain.ofHom (coaugCoidealπ η)) (zero_add 0) = 0 := by
  have h : η ≫ coaugCoidealπ η = 0 := coaugCoideal_condition η
  have h2 : HomComplex.Cochain.ofHom (η ≫ coaugCoidealπ η) =
      (HomComplex.Cochain.ofHom η).comp
        (HomComplex.Cochain.ofHom (coaugCoidealπ η)) (zero_add 0) :=
    HomComplex.Cochain.ofHom_comp _ _
  rw [h, HomComplex.Cochain.ofHom_zero] at h2
  exact h2.symm

/-- Thin wrapper: lift through a twisting cochain's own augmentation kernel,
reusing the generic lift. -/
noncomputable def TwistingCochain.augIdeal_lift
    (τ : TwistingCochain (R := R) (C := C) (A := A))
    {X : CochainComplex (ModuleCat R) ℤ} (f : X ⟶ A) (h : f ≫ τ.aug = 0) :
    X ⟶ _root_.CochainComplex.augIdeal τ.aug :=
  _root_.CochainComplex.augIdeal_lift τ.aug f h

/-- Computation for the twisting-cochain augmentation lift. -/
theorem TwistingCochain.augIdeal_lift_ι
    (τ : TwistingCochain (R := R) (C := C) (A := A))
    {X : CochainComplex (ModuleCat R) ℤ} (f : X ⟶ A) (h : f ≫ τ.aug = 0) :
    τ.augIdeal_lift f h ≫ _root_.CochainComplex.augIdealι τ.aug = f :=
  _root_.CochainComplex.augIdeal_lift_ι τ.aug f h

/-- Thin wrapper: desc through a twisting cochain's own coaugmentation
cokernel, reusing the generic desc. -/
noncomputable def TwistingCochain.coaugCoideal_desc
    (τ : TwistingCochain (R := R) (C := C) (A := A))
    {W : CochainComplex (ModuleCat R) ℤ} (k : C ⟶ W) (h : τ.coaug ≫ k = 0) :
    _root_.CochainComplex.coaugCoideal τ.coaug ⟶ W :=
  _root_.CochainComplex.coaugCoideal_desc τ.coaug k h

/-- Computation for the twisting-cochain coaugmentation desc. -/
theorem TwistingCochain.coaugCoideal_desc_π
    (τ : TwistingCochain (R := R) (C := C) (A := A))
    {W : CochainComplex (ModuleCat R) ℤ} (k : C ⟶ W) (h : τ.coaug ≫ k = 0) :
    _root_.CochainComplex.coaugCoidealπ τ.coaug ≫ τ.coaugCoideal_desc k h = k :=
  _root_.CochainComplex.coaugCoideal_π_desc τ.coaug k h

end CochainComplex
