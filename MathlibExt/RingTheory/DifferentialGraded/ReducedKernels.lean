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
# Kernels, cokernels and reduced twisting maps

In the cochain tensor setting over a commutative ring R, let ε : A → I and η : I → C be chain
maps. The augmentation kernel K = Ker(ε) has inclusion i : K → A, and the coaugmentation
quotient Q = Coker(η) has projection π : C → Q.

Every map f : X → A with f ≫ ε = 0 lifts uniquely to K, with lift(f) ≫ i = f. Every map k : C
→ W with η ≫ k = 0 descends uniquely from Q, with π ≫ desc(k) = k. Point-compatible morphisms
induce quotient maps that preserve identities and composition.

The corresponding degree-zero Hom cochains have vanishing outer composites. For a twisting
cochain, these constructions use its specified augmentation and coaugmentation and give the
same universal factor maps. The kernel and cokernel are cochain-complex objects;
multiplication and coproduct structures are not part of these definitions.
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

/-- Augmentation kernel as a cochain complex.

For a chain map ε : A → I in the stated cochain tensor category, augIdeal ε is the kernel
complex Ker(ε). -/
noncomputable def augIdeal (ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ)) :
    CochainComplex (ModuleCat R) ℤ :=
  kernel ε

/-- Inclusion of the augmentation kernel.

For ε : A → I, augIdealι ε is the canonical kernel inclusion Ker(ε) → A. -/
noncomputable def augIdealι (ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ)) :
    augIdeal ε ⟶ A :=
  kernel.ι ε

/-- Coaugmentation quotient as a cochain complex.

For η : I → C, coaugCoideal η is the cokernel complex Coker(η). -/
noncomputable def coaugCoideal (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C) :
    CochainComplex (ModuleCat R) ℤ :=
  cokernel η

/-- Projection to the coaugmentation quotient.

For η : I → C, coaugCoidealπ η is the canonical cokernel projection C → Coker(η). -/
noncomputable def coaugCoidealπ (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C) :
    C ⟶ coaugCoideal η :=
  cokernel.π η

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [MonObj A] in
/-- Zero composite of the augmentation-kernel inclusion.

For i : Ker(ε) → A, the equation i ≫ ε = 0 is the kernel condition. -/
theorem augIdeal_condition (ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ)) :
    augIdealι ε ≫ ε = 0 :=
  kernel.condition ε

/-- Universal factor map through an augmentation kernel.

For f : X → A with f ≫ ε = 0, the kernel universal property defines augIdeal_lift ε f : X →
Ker(ε). -/
noncomputable def augIdeal_lift (ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ))
    {X : CochainComplex (ModuleCat R) ℤ} (f : X ⟶ A) (h : f ≫ ε = 0) :
    X ⟶ augIdeal ε :=
  kernel.lift ε f h

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [MonObj A] in
/-- Inclusion equation for an augmentation-kernel factor map.

For f : X → A annihilated by ε, augIdeal_lift ε f followed by augIdealι ε is f. -/
theorem augIdeal_lift_ι (ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ))
    {X : CochainComplex (ModuleCat R) ℤ} (f : X ⟶ A) (h : f ≫ ε = 0) :
    augIdeal_lift ε f h ≫ augIdealι ε = f :=
  kernel.lift_ι ε f h

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [MonObj A] in
/-- Uniqueness of an augmentation-kernel factor map.

If f ≫ ε = 0 and g : X → Ker(ε) satisfies g ≫ augIdealι ε = f, then g equals augIdeal_lift ε
f. -/
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
/-- Zero composite of a coaugmentation quotient projection.

For η : I → C and π : C → Coker(η), η ≫ π = 0. -/
theorem coaugCoideal_condition (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C) :
    η ≫ coaugCoidealπ η = 0 :=
  cokernel.condition η

/-- Universal descendant from a coaugmentation quotient.

For k : C → W with η ≫ k = 0, the cokernel universal property gives coaugCoideal_desc η k :
Coker(η) → W. -/
noncomputable def coaugCoideal_desc (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    {W : CochainComplex (ModuleCat R) ℤ} (k : C ⟶ W) (h : η ≫ k = 0) :
    coaugCoideal η ⟶ W :=
  cokernel.desc η k h

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [ComonObj C] in
/-- Projection equation for a coaugmentation quotient descendant.

For k annihilating η, coaugCoidealπ η followed by coaugCoideal_desc η k equals k. -/
theorem coaugCoideal_π_desc (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    {W : CochainComplex (ModuleCat R) ℤ} (k : C ⟶ W) (h : η ≫ k = 0) :
    coaugCoidealπ η ≫ coaugCoideal_desc η k h = k :=
  cokernel.π_desc η k h

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [ComonObj C] in
/-- Uniqueness of a coaugmentation quotient descendant.

If η ≫ k = 0 and g : Coker(η) → W satisfies coaugCoidealπ η ≫ g = k, then g equals
coaugCoideal_desc η k. -/
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
/-- Map of coaugmentation quotients from a point-compatible morphism.

For f : C → D with η_C ≫ f = η_D, the composite f ≫ π_D annihilates η_C and descends to a map
Coker(η_C) → Coker(η_D). No coproduct-preservation condition on f is required for this
cokernel map. -/
noncomputable def coaugCoidealMap
    (ηC : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (ηD : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ D) (f : C ⟶ D)
    (hη : ηC ≫ f = ηD) : coaugCoideal ηC ⟶ coaugCoideal ηD :=
  coaugCoideal_desc ηC (f ≫ coaugCoidealπ ηD) (by
    rw [← Category.assoc, hη]
    exact coaugCoideal_condition ηD)

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [ComonObj C] in
/-- Projection square for a coaugmentation quotient map.

For f : C → D with η_C ≫ f = η_D, the induced quotient map satisfies π_C ≫ coaugCoidealMap(f)
= f ≫ π_D. -/
theorem coaugCoideal_π_map
    (ηC : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (ηD : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ D) (f : C ⟶ D)
    (hη : ηC ≫ f = ηD) :
    coaugCoidealπ ηC ≫ coaugCoidealMap ηC ηD f hη = f ≫ coaugCoidealπ ηD :=
  coaugCoideal_π_desc ηC _ _

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [ComonObj C] in
/-- Identity law for coaugmentation quotient maps.

The quotient map induced by id_C with point η_C is the identity of Coker(η_C). -/
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
/-- Composition law for coaugmentation quotient maps.

For f : C → D and g : D → E satisfying η_C ≫ f = η_D and η_D ≫ g = η_E, the quotient map of f
≫ g equals the quotient map of f followed by that of g. -/
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
/-- Augmentation-kernel vanishing in degree-zero Hom cochains.

The degree-zero cochain of the kernel inclusion i : Ker(ε) → A followed by the degree-zero
cochain of ε is zero, with total degree 0+0=0. -/
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
/-- Coaugmentation-quotient vanishing in degree-zero Hom cochains.

The degree-zero cochain of η : I → C followed by the degree-zero cochain of π : C → Coker(η)
is zero, with total degree 0+0=0. -/
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

/-- Factor map through a twisting cochain's augmentation kernel.

For a twisting cochain τ and f : X → A with f ≫ τ.aug = 0, use the kernel universal property
to define X → Ker(τ.aug). -/
noncomputable def TwistingCochain.augIdeal_lift
    (τ : TwistingCochain (R := R) (C := C) (A := A))
    {X : CochainComplex (ModuleCat R) ℤ} (f : X ⟶ A) (h : f ≫ τ.aug = 0) :
    X ⟶ _root_.CochainComplex.augIdeal τ.aug :=
  _root_.CochainComplex.augIdeal_lift τ.aug f h

/-- Inclusion equation for a twisting augmentation factor map.

For f annihilated by τ.aug, τ.augIdeal_lift f followed by the inclusion Ker(τ.aug) → A is f. -/
theorem TwistingCochain.augIdeal_lift_ι
    (τ : TwistingCochain (R := R) (C := C) (A := A))
    {X : CochainComplex (ModuleCat R) ℤ} (f : X ⟶ A) (h : f ≫ τ.aug = 0) :
    τ.augIdeal_lift f h ≫ _root_.CochainComplex.augIdealι τ.aug = f :=
  _root_.CochainComplex.augIdeal_lift_ι τ.aug f h

/-- Descendant from a twisting cochain's coaugmentation quotient.

For τ and k : C → W with τ.coaug ≫ k = 0, use the cokernel universal property to define
Coker(τ.coaug) → W. -/
noncomputable def TwistingCochain.coaugCoideal_desc
    (τ : TwistingCochain (R := R) (C := C) (A := A))
    {W : CochainComplex (ModuleCat R) ℤ} (k : C ⟶ W) (h : τ.coaug ≫ k = 0) :
    _root_.CochainComplex.coaugCoideal τ.coaug ⟶ W :=
  _root_.CochainComplex.coaugCoideal_desc τ.coaug k h

/-- Projection equation for a twisting coaugmentation descendant.

For k annihilating τ.coaug, the projection C → Coker(τ.coaug) followed by τ.coaugCoideal_desc
k equals k. -/
theorem TwistingCochain.coaugCoideal_desc_π
    (τ : TwistingCochain (R := R) (C := C) (A := A))
    {W : CochainComplex (ModuleCat R) ℤ} (k : C ⟶ W) (h : τ.coaug ≫ k = 0) :
    _root_.CochainComplex.coaugCoidealπ τ.coaug ≫ τ.coaugCoideal_desc k h = k :=
  _root_.CochainComplex.coaugCoideal_π_desc τ.coaug k h

end CochainComplex
