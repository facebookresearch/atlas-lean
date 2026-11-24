/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChainGradedPairingPositiveQuotient
public import MathlibExt.Algebra.Homology.LinearHomCochainComplex

/-!
# Cochains on the actual positive pairing quotient

The cochains are the existing contravariant linear Hom complex of the actual
quotient. Their differential precomposes with its actual differential. The
degreewise universal property says exactly which original cochains occur:
they annihilate every pairing component with both degrees positive.

This is a ground-linear dual construction with an explicit target module.
An identification with algebra-linear Harrison cohomology requires a separate
algebra-action construction and comparison.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped MonoidalCategory

universe u v

namespace HomologicalComplex.ChainGradedPairing

variable {R : Type u} [CommRing R]
  [MonoidalCategory (ModuleCat.{v} R)]
  [MonoidalPreadditive (ModuleCat.{v} R)]
  {K₁ K₂ K₃ : ChainComplex (ModuleCat.{v} R) ℕ}
  (P : ChainGradedPairing K₁ K₂ K₃)

/-- An original cochain kills the relation sum precisely when it kills every positive component. -/
theorem positiveImages_le_ker_iff (n : ℕ) {G : ModuleCat.{v} R}
    (φ : K₃.X n ⟶ G) :
    positiveImages P n ≤ LinearMap.ker φ.hom ↔
      ∀ (p q : ℕ) (h : p + q = n), 0 < p → 0 < q →
        pairAt P p q n h ≫ φ = 0 := by
  constructor
  · intro hφ p q h hp hq
    apply ModuleCat.hom_ext
    ext x
    change φ.hom ((pairAt P p q n h).hom x) = 0
    exact hφ (pairAt_mem_positiveImages P p q n h hp hq x)
  · intro hφ
    apply iSup_le
    intro z
    rintro y ⟨x, rfl⟩
    change φ.hom ((pairAt P z.1.1 z.1.2 n z.2.2.2).hom x) = 0
    exact ConcreteCategory.congr_hom
      (hφ z.1.1 z.1.2 z.2.2.2 z.2.1 z.2.2.1) x

variable (h₁ : K₁.d 1 0 = 0) (h₂ : K₂.d 1 0 = 0)

/-- The actual quotient cochains are the existing linear Hom complex. -/
def positiveImageCochainComplex (G : ModuleCat.{v} R) :
    CochainComplex (ModuleCat.{v} R) ℕ :=
  (linearHomCochainComplexFunctor R (ModuleCat.{v} R) G).obj
    (Opposite.op (positiveImageQuotient P h₁ h₂))

/-- Their complete coboundary is precomposition with the original quotient boundary. -/
theorem positiveImageCochainComplex_d_apply (G : ModuleCat.{v} R) (n : ℕ)
    (φ : (positiveImageQuotient P h₁ h₂).X n ⟶ G)
    (x : (positiveImageQuotient P h₁ h₂).X (n + 1)) :
    (((positiveImageCochainComplex P h₁ h₂ G).d n (n + 1)).hom φ).hom x =
      φ.hom (((positiveImageQuotient P h₁ h₂).d (n + 1) n).hom x) := rfl

/-- Pullback along the actual quotient projection is a cochain map. -/
def positiveImageCochainInclusion (G : ModuleCat.{v} R) :
    positiveImageCochainComplex P h₁ h₂ G ⟶
      (linearHomCochainComplexFunctor R (ModuleCat.{v} R) G).obj (Opposite.op K₃) :=
  (linearHomCochainComplexFunctor R (ModuleCat.{v} R) G).map
    (positiveImageProjection P h₁ h₂).op

/-- Its degree value is the actual projection followed by the quotient cochain. -/
theorem positiveImageCochainInclusion_f_apply (G : ModuleCat.{v} R) (n : ℕ)
    (φ : (positiveImageQuotient P h₁ h₂).X n ⟶ G) :
    ((positiveImageCochainInclusion P h₁ h₂ G).f n).hom φ =
      (positiveImageProjection P h₁ h₂).f n ≫ φ := rfl

/-- A quotient cochain is uniquely determined by its pullback to original chains. -/
theorem positiveImageCochainInclusion_f_injective (G : ModuleCat.{v} R) (n : ℕ) :
    Function.Injective ((positiveImageCochainInclusion P h₁ h₂ G).f n).hom := by
  intro φ ψ h
  apply ModuleCat.hom_ext
  ext z
  refine Quotient.inductionOn' z ?_
  intro x
  exact congrArg (fun τ : K₃.X n ⟶ G => τ.hom x) h

/-- The degreewise universal property is precisely the positive-component annihilation condition. -/
theorem existsUnique_positiveImageQuotient_cochain (n : ℕ) {G : ModuleCat.{v} R}
    (φ : K₃.X n ⟶ G) :
    (∃! ψ : (positiveImageQuotient P h₁ h₂).X n ⟶ G,
      (positiveImageProjection P h₁ h₂).f n ≫ ψ = φ) ↔
      ∀ (p q : ℕ) (h : p + q = n), 0 < p → 0 < q →
        pairAt P p q n h ≫ φ = 0 := by
  constructor
  · rintro ⟨ψ, hψ, _⟩ p q h hp hq
    rw [← hψ, ← Category.assoc, pairAt_comp_positiveImageProjection P h₁ h₂ p q n h hp hq,
      Limits.zero_comp]
  · intro hφ
    have hk : positiveImages P n ≤ LinearMap.ker φ.hom :=
      (positiveImages_le_ker_iff P n φ).2 hφ
    let ψ : (positiveImageQuotient P h₁ h₂).X n ⟶ G :=
      ModuleCat.ofHom ((positiveImages P n).liftQ φ.hom hk)
    refine ⟨ψ, ?_, ?_⟩
    · apply ModuleCat.hom_ext
      exact Submodule.liftQ_mkQ _ _ _
    · intro χ hχ
      apply ModuleCat.hom_ext
      ext z
      refine Quotient.inductionOn' z ?_
      intro x
      exact congrArg (fun τ : K₃.X n ⟶ G => τ.hom x) hχ

/-- All nonnegative cohomology degrees use the actual coboundary and homology quotient. -/
def positiveImageCohomology (G : ModuleCat.{v} R) (n : ℕ) : ModuleCat.{v} R :=
  (positiveImageCochainComplex P h₁ h₂ G).homology n

/-- Covariance in the explicit target module is the existing Hom-cohomology functor. -/
def positiveImageCohomologyFunctor (n : ℕ) : ModuleCat.{v} R ⥤ ModuleCat.{v} R :=
  linearHomCochainComplexHomologyFunctor R (ModuleCat.{v} R)
    (positiveImageQuotient P h₁ h₂) n

section Naturality

variable {L₁ L₂ L₃ : ChainComplex (ModuleCat.{v} R) ℕ}
  (Q : ChainGradedPairing L₁ L₂ L₃)
  (g₁ : L₁.d 1 0 = 0) (g₂ : L₂.d 1 0 = 0)
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃)
  (hf : tensorHom f₁ f₂ ≫ Q = P ≫ f₃)

/-- Pullback of quotient cochains uses the actual induced quotient map. -/
def positiveImageCochainMap (G : ModuleCat.{v} R) :
    positiveImageCochainComplex Q g₁ g₂ G ⟶ positiveImageCochainComplex P h₁ h₂ G :=
  (linearHomCochainComplexFunctor R (ModuleCat.{v} R) G).map
    (positiveImageQuotientMap P h₁ h₂ Q g₁ g₂ f₁ f₂ f₃ hf).op

/-- Pullback commutes with the original cochain inclusions. -/
@[reassoc]
theorem positiveImageCochainMap_inclusion (G : ModuleCat.{v} R) :
    positiveImageCochainMap P h₁ h₂ Q g₁ g₂ f₁ f₂ f₃ hf G ≫
        positiveImageCochainInclusion P h₁ h₂ G =
      positiveImageCochainInclusion Q g₁ g₂ G ≫
        (linearHomCochainComplexFunctor R (ModuleCat.{v} R) G).map f₃.op := by
  let F := linearHomCochainComplexFunctor R (ModuleCat.{v} R) G
  change F.map (positiveImageQuotientMap P h₁ h₂ Q g₁ g₂ f₁ f₂ f₃ hf).op ≫
      F.map (positiveImageProjection P h₁ h₂).op =
    F.map (positiveImageProjection Q g₁ g₂).op ≫ F.map f₃.op
  rw [← F.map_comp, ← F.map_comp]
  apply congrArg F.map
  exact congrArg Quiver.Hom.op
    (positiveImageProjection_map P h₁ h₂ Q g₁ g₂ f₁ f₂ f₃ hf)

/-- The contravariant all-degree cohomology map is induced by that actual cochain map. -/
def positiveImageCohomologyMap (G : ModuleCat.{v} R) (n : ℕ) :
    positiveImageCohomology Q g₁ g₂ G n ⟶ positiveImageCohomology P h₁ h₂ G n :=
  HomologicalComplex.homologyMap
    (positiveImageCochainMap P h₁ h₂ Q g₁ g₂ f₁ f₂ f₃ hf G) n

end Naturality

end HomologicalComplex.ChainGradedPairing
