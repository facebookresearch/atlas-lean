/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChainGradedPairingPositiveImages
public import MathlibExt.Algebra.Homology.TensorHomFunctoriality
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# The actual positive-image subcomplex and quotient of a chain pairing

The relation family is the existing sum of ranges in bidegrees p,q > 0.
Its differential is the restriction of the original target differential;
the quotient differential is the native Submodule.mapQ of that same map.
Closure is derived from the pairing's signed chain-map law and the two
original endpoint-zero laws. No closure or quotient certificate is an input.
The original degree-zero objects remain unrestricted.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory
open scoped MonoidalCategory

universe u v

namespace HomologicalComplex.ChainGradedPairing

variable {R : Type u} [Ring R]
  [MonoidalCategory (ModuleCat.{v} R)] [CategoryTheory.MonoidalPreadditive (ModuleCat.{v} R)]
  {K₁ K₂ K₃ : ChainComplex (ModuleCat.{v} R) ℕ}
  (P : ChainGradedPairing K₁ K₂ K₃)
  (h₁ : K₁.d 1 0 = 0) (h₂ : K₂.d 1 0 = 0)

/-- The original differential restricted to the actual positive image family. -/
def positiveImageDifferential (n : ℕ) :
    ModuleCat.of R (positiveImages P (n + 1)) ⟶ ModuleCat.of R (positiveImages P n) :=
  ModuleCat.ofHom
    (((K₃.d (n + 1) n).hom.comp (positiveImages P (n + 1)).subtype).codRestrict
      (positiveImages P n) (fun x => positiveImages_d P h₁ h₂ n x.property))

/-- The restricted maps square to zero because the original differential does. -/
theorem positiveImageDifferential_comp (n : ℕ) :
    positiveImageDifferential P h₁ h₂ (n + 1) ≫
      positiveImageDifferential P h₁ h₂ n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (K₃.d (n + 1) n).hom ((K₃.d (n + 2) (n + 1)).hom x.val) = 0
  have hd : (K₃.d (n + 1) n).hom.comp (K₃.d (n + 2) (n + 1)).hom = 0 :=
    congrArg ModuleCat.Hom.hom (K₃.d_comp_d (n + 2) (n + 1) n)
  exact congrArg (fun f : K₃.X (n + 2) →ₗ[R] K₃.X n => f x.val) hd

/-- The subcomplex on D_n = sum of positive component images. -/
def positiveImageSubcomplex : ChainComplex (ModuleCat.{v} R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (positiveImages P n))
    (positiveImageDifferential P h₁ h₂) (positiveImageDifferential_comp P h₁ h₂)

/-- The subcomplex inclusion is the native subtype map in every degree. -/
def positiveImageInclusion : positiveImageSubcomplex P h₁ h₂ ⟶ K₃ :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (positiveImages P n).subtype) (by
    intro n
    apply ModuleCat.hom_ext
    ext x
    simp only [positiveImageSubcomplex, ChainComplex.of_d]
    rfl)

/-- The quotient boundary is the native induced map of the original differential. -/
def positiveQuotientDifferential (n : ℕ) :
    ModuleCat.of R ((K₃.X (n + 1)) ⧸ positiveImages P (n + 1)) ⟶
      ModuleCat.of R ((K₃.X n) ⧸ positiveImages P n) :=
  ModuleCat.ofHom ((positiveImages P (n + 1)).mapQ (positiveImages P n)
    (K₃.d (n + 1) n).hom (positiveImages_d P h₁ h₂ n))

/-- The quotient maps inherit d squared equals zero from the original complex. -/
theorem positiveQuotientDifferential_comp (n : ℕ) :
    positiveQuotientDifferential P h₁ h₂ (n + 1) ≫
      positiveQuotientDifferential P h₁ h₂ n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  refine Quotient.inductionOn' z ?_
  intro x
  change (positiveImages P n).mkQ
    ((K₃.d (n + 1) n).hom ((K₃.d (n + 2) (n + 1)).hom x)) = 0
  have hd : (K₃.d (n + 1) n).hom.comp (K₃.d (n + 2) (n + 1)).hom = 0 :=
    congrArg ModuleCat.Hom.hom (K₃.d_comp_d (n + 2) (n + 1) n)
  have hx : (K₃.d (n + 1) n).hom ((K₃.d (n + 2) (n + 1)).hom x) = 0 :=
    congrArg (fun f : K₃.X (n + 2) →ₗ[R] K₃.X n => f x) hd
  rw [hx, map_zero]

/-- The actual pointwise quotient K_3,n / D_n, retaining the full original target complex. -/
def positiveImageQuotient : ChainComplex (ModuleCat.{v} R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R ((K₃.X n) ⧸ positiveImages P n))
    (positiveQuotientDifferential P h₁ h₂) (positiveQuotientDifferential_comp P h₁ h₂)

/-- The original target maps to its quotient through its actual quotient maps. -/
def positiveImageProjection : K₃ ⟶ positiveImageQuotient P h₁ h₂ :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (positiveImages P n).mkQ) (by
    intro n
    apply ModuleCat.hom_ext
    simp only [positiveImageQuotient, ChainComplex.of_d]
    exact Submodule.mapQ_mkQ (positiveImages P (n + 1)) (positiveImages P n)
      (K₃.d (n + 1) n).hom (h := positiveImages_d P h₁ h₂ n))

/-- Its actual component kernel is exactly the stated positive relation family. -/
theorem ker_positiveImageProjection (n : ℕ) :
    LinearMap.ker ((positiveImageProjection P h₁ h₂).f n).hom = positiveImages P n :=
  Submodule.ker_mkQ _

/-- Every original positive pairing component is killed by the actual quotient projection. -/
theorem pairAt_comp_positiveImageProjection (p q n : ℕ) (h : p + q = n)
    (hp : 0 < p) (hq : 0 < q) :
    pairAt P p q n h ≫ (positiveImageProjection P h₁ h₂).f n = 0 := by
  apply ModuleCat.hom_ext
  ext x
  change (positiveImages P n).mkQ ((pairAt P p q n h).hom x) = 0
  have hm := pairAt_mem_positiveImages P p q n h hp hq x
  have hk : (pairAt P p q n h).hom x ∈ LinearMap.ker (positiveImages P n).mkQ := by
    simpa only [Submodule.ker_mkQ] using hm
  exact hk

/-- D_0 is zero, so the quotient never destroys the original degree-zero object. -/
theorem positiveImageProjection_injective_zero :
    Function.Injective ((positiveImageProjection P h₁ h₂).f 0).hom := by
  apply LinearMap.ker_eq_bot.mp
  rw [ker_positiveImageProjection, positiveImages_zero]

/-- D_1 is also zero; the original degree-one coordinate is retained. -/
theorem positiveImageProjection_injective_one :
    Function.Injective ((positiveImageProjection P h₁ h₂).f 1).hom := by
  apply LinearMap.ker_eq_bot.mp
  rw [ker_positiveImageProjection, positiveImages_one]

section Naturality

variable {L₁ L₂ L₃ : ChainComplex (ModuleCat.{v} R) ℕ}
  (Q : ChainGradedPairing L₁ L₂ L₃)
  (g₁ : L₁.d 1 0 = 0) (g₂ : L₂.d 1 0 = 0)
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃)
  (hf : tensorHom f₁ f₂ ≫ Q = P ≫ f₃)

/-- A morphism of pairings induces the native quotient map componentwise. -/
def positiveImageQuotientMap :
    positiveImageQuotient P h₁ h₂ ⟶ positiveImageQuotient Q g₁ g₂ :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom
    ((positiveImages P n).mapQ (positiveImages Q n) (f₃.f n).hom
      (positiveImages_naturality P Q f₁ f₂ f₃ hf n))) (by
    intro n
    apply ModuleCat.hom_ext
    ext z
    refine Quotient.inductionOn' z ?_
    intro x
    simp only [positiveImageQuotient, ChainComplex.of_d]
    change (positiveImages Q n).mkQ
      ((L₃.d (n + 1) n).hom ((f₃.f (n + 1)).hom x)) =
        (positiveImages Q n).mkQ ((f₃.f n).hom ((K₃.d (n + 1) n).hom x))
    exact congrArg (positiveImages Q n).mkQ
      (ConcreteCategory.congr_hom (f₃.comm (n + 1) n) x))

/-- The actual induced map commutes with the original target maps and projections. -/
@[reassoc]
theorem positiveImageProjection_map :
    positiveImageProjection P h₁ h₂ ≫
        positiveImageQuotientMap P h₁ h₂ Q g₁ g₂ f₁ f₂ f₃ hf =
      f₃ ≫ positiveImageProjection Q g₁ g₂ := by
  ext n x
  rfl

end Naturality

/-- The identity morphism of a pairing induces the identity on the actual quotient. -/
@[simp]
theorem positiveImageQuotientMap_id :
    positiveImageQuotientMap P h₁ h₂ P h₁ h₂ (𝟙 K₁) (𝟙 K₂) (𝟙 K₃)
      (by simp only [tensorHom_id_id, Category.id_comp, Category.comp_id]) =
        𝟙 (positiveImageQuotient P h₁ h₂) := by
  ext n z
  refine Quotient.inductionOn' z ?_
  intro x
  rfl

/-- Actual compatible composition of pairings gives composition of the native quotient maps. -/
@[reassoc]
theorem positiveImageQuotientMap_comp
    {L₁ L₂ L₃ M₁ M₂ M₃ : ChainComplex (ModuleCat.{v} R) ℕ}
    (Q : ChainGradedPairing L₁ L₂ L₃) (S : ChainGradedPairing M₁ M₂ M₃)
    (g₁ : L₁.d 1 0 = 0) (g₂ : L₂.d 1 0 = 0)
    (s₁ : M₁.d 1 0 = 0) (s₂ : M₂.d 1 0 = 0)
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃)
    (k₁ : L₁ ⟶ M₁) (k₂ : L₂ ⟶ M₂) (k₃ : L₃ ⟶ M₃)
    (hf : tensorHom f₁ f₂ ≫ Q = P ≫ f₃)
    (hk : tensorHom k₁ k₂ ≫ S = Q ≫ k₃) :
    positiveImageQuotientMap P h₁ h₂ Q g₁ g₂ f₁ f₂ f₃ hf ≫
        positiveImageQuotientMap Q g₁ g₂ S s₁ s₂ k₁ k₂ k₃ hk =
      positiveImageQuotientMap P h₁ h₂ S s₁ s₂ (f₁ ≫ k₁) (f₂ ≫ k₂) (f₃ ≫ k₃)
        (by rw [← tensorHom_comp_tensorHom, Category.assoc, hk,
          ← Category.assoc, hf, Category.assoc]) := by
  ext n z
  refine Quotient.inductionOn' z ?_
  intro x
  rfl

end HomologicalComplex.ChainGradedPairing
