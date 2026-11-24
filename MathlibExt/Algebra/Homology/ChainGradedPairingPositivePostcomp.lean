/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChainGradedPairingPositiveQuotient

/-!
# Positive pairing relations after a target map

Postcomposing an actual chain pairing takes its positive relation module to
the image of the original relation module. The induced quotient map and its
kernel are computed here. A quasi-isomorphism of targets does not by itself
give a quasi-isomorphism of these quotients.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped MonoidalCategory

universe u v

namespace HomologicalComplex.ChainGradedPairing

variable {R : Type u} [Ring R]
  [MonoidalCategory (ModuleCat.{v} R)]
  [MonoidalPreadditive (ModuleCat.{v} R)]
  {K₁ K₂ K₃ L : ChainComplex (ModuleCat.{v} R) ℕ}
  (P : ChainGradedPairing K₁ K₂ K₃) (f : K₃ ⟶ L)

/-- A component of the actual postcomposition is postcomposition of the component. -/
theorem pairAt_postcomp (p q n : ℕ) (h : p + q = n) :
    pairAt (P.postcomp f) p q n h = pairAt P p q n h ≫ f.f n := by
  subst n
  simp only [pairAt_rfl, pair_postcomp]

/-- The positive relation family of the actual postcomposition is the direct image. -/
theorem positiveImages_postcomp (n : ℕ) :
    positiveImages (P.postcomp f) n = (positiveImages P n).map (f.f n).hom := by
  unfold positiveImages
  rw [Submodule.map_iSup]
  apply iSup_congr
  intro z
  rw [pairAt_postcomp]
  change LinearMap.range ((f.f n).hom.comp
      (pairAt P z.1.1 z.1.2 n z.2.2.2).hom) = _
  exact LinearMap.range_comp _ _

/-- Pulling those relations back adds exactly the kernel of the target map. -/
theorem comap_positiveImages_postcomp (n : ℕ) :
    (positiveImages (P.postcomp f) n).comap (f.f n).hom =
      positiveImages P n ⊔ LinearMap.ker (f.f n).hom := by
  rw [positiveImages_postcomp, Submodule.comap_map_eq]

variable (h₁ : K₁.d 1 0 = 0) (h₂ : K₂.d 1 0 = 0)

/-- The target map descends through the two actual positive relation quotients. -/
def positiveImageQuotientPostcompMap :
    positiveImageQuotient P h₁ h₂ ⟶ positiveImageQuotient (P.postcomp f) h₁ h₂ :=
  positiveImageQuotientMap P h₁ h₂ (P.postcomp f) h₁ h₂ (𝟙 K₁) (𝟙 K₂) f
    (by simp only [tensorHom_id_id, Category.id_comp, postcomp])

/-- The descended map sends an original class to the class of its actual image. -/
theorem positiveImageQuotientPostcompMap_mk (n : ℕ) (x : K₃.X n) :
    ((positiveImageQuotientPostcompMap P f h₁ h₂).f n).hom
        ((positiveImages P n).mkQ x) =
      (positiveImages (P.postcomp f) n).mkQ ((f.f n).hom x) := rfl

/-- The induced map retains the original quotient projection square. -/
@[reassoc]
theorem positiveImageQuotientPostcompMap_projection :
    positiveImageProjection P h₁ h₂ ≫ positiveImageQuotientPostcompMap P f h₁ h₂ =
      f ≫ positiveImageProjection (P.postcomp f) h₁ h₂ :=
  positiveImageProjection_map P h₁ h₂ (P.postcomp f) h₁ h₂ (𝟙 K₁) (𝟙 K₂) f
    (by simp only [tensorHom_id_id, Category.id_comp, postcomp])

/-- Its component kernel is the original target kernel modulo the original relations. -/
theorem ker_positiveImageQuotientPostcompMap (n : ℕ) :
    LinearMap.ker ((positiveImageQuotientPostcompMap P f h₁ h₂).f n).hom =
      (LinearMap.ker (f.f n).hom).map (positiveImages P n).mkQ := by
  have h : positiveImages P n ≤
      (positiveImages (P.postcomp f) n).comap (f.f n).hom := by
    rw [comap_positiveImages_postcomp]
    exact le_sup_left
  change LinearMap.ker ((positiveImages P n).mapQ
      (positiveImages (P.postcomp f) n) (f.f n).hom h) = _
  rw [Submodule.ker_mapQ, comap_positiveImages_postcomp, Submodule.map_sup,
    Submodule.mkQ_map_self, bot_sup_eq]

/-- Surjectivity of each original component gives surjectivity of the actual quotient component. -/
theorem positiveImageQuotientPostcompMap_surjective (n : ℕ)
    (hf : Function.Surjective (f.f n).hom) :
    Function.Surjective ((positiveImageQuotientPostcompMap P f h₁ h₂).f n).hom := by
  intro z
  refine Quotient.inductionOn' z ?_
  intro y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨(positiveImages P n).mkQ x, rfl⟩

end HomologicalComplex.ChainGradedPairing
