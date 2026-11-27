/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChainGradedPairingPositiveQuotient

/-!
# Positive pairing images under a target map

For a chain pairing P and a target chain map f, the positive relation submodule of P followed
by f is the image f_n(S_n) of the relation submodule S_n of P. Pulling it back along f_n gives
S_n + ker f_n.

When the two source degree-one boundaries vanish, f induces a map between the positive-image
quotient complexes, sending [x] to [f_n(x)]. Its degree-n kernel is the image of ker f_n under
K₃.X n → K₃.X n/S_n. Surjectivity of f_n implies surjectivity of this degree quotient map.
These statements use the supplied additive monoidal structure over an arbitrary ring.
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

/-- Let R be a ring and equip ModuleCat.{v} R with a monoidal structure additive in both
variables. Let P : K₁ ⊗ K₂ ⟶ K₃ be a chain pairing of ℕ-indexed chain complexes. Let f : K₃ ⟶
L be a chain map and write S_n for positiveImages P n. For p + q = n with equality h, pairAt
(P.postcomp f) p q n h = pairAt P p q n h ≫ f.f n. -/
theorem pairAt_postcomp (p q n : ℕ) (h : p + q = n) :
    pairAt (P.postcomp f) p q n h = pairAt P p q n h ≫ f.f n := by
  subst n
  simp only [pairAt_rfl, pair_postcomp]

/-- Let R be a ring and equip ModuleCat.{v} R with a monoidal structure additive in both
variables. Let P : K₁ ⊗ K₂ ⟶ K₃ be a chain pairing of ℕ-indexed chain complexes. Let f : K₃ ⟶
L be a chain map and write S_n for positiveImages P n. For every n : ℕ, positiveImages
(P.postcomp f) n = S_n.map (f.f n).hom. -/
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

/-- Let R be a ring and equip ModuleCat.{v} R with a monoidal structure additive in both
variables. Let P : K₁ ⊗ K₂ ⟶ K₃ be a chain pairing of ℕ-indexed chain complexes. Let f : K₃ ⟶
L be a chain map and write S_n for positiveImages P n. For every n : ℕ, (positiveImages
(P.postcomp f) n).comap (f.f n).hom = S_n ⊔ LinearMap.ker (f.f n).hom. This is the submodule
sum of the relations and the kernel. -/
theorem comap_positiveImages_postcomp (n : ℕ) :
    (positiveImages (P.postcomp f) n).comap (f.f n).hom =
      positiveImages P n ⊔ LinearMap.ker (f.f n).hom := by
  rw [positiveImages_postcomp, Submodule.comap_map_eq]

variable (h₁ : K₁.d 1 0 = 0) (h₂ : K₂.d 1 0 = 0)

/-- Let R be a ring and equip ModuleCat.{v} R with a monoidal structure additive in both
variables. Let P : K₁ ⊗ K₂ ⟶ K₃ be a chain pairing of ℕ-indexed chain complexes. Let f : K₃ ⟶
L be a chain map and write S_n for positiveImages P n. Assume K₁.d 1 0 = 0 and K₂.d 1 0 = 0,
so these image families define quotient complexes. The map positiveImageQuotientPostcompMap
goes from K₃/S to L/f(S), with the boundaries induced from K₃ and L. In degree n it sends the
class of x to the class of f_n(x). -/
def positiveImageQuotientPostcompMap :
    positiveImageQuotient P h₁ h₂ ⟶ positiveImageQuotient (P.postcomp f) h₁ h₂ :=
  positiveImageQuotientMap P h₁ h₂ (P.postcomp f) h₁ h₂ (𝟙 K₁) (𝟙 K₂) f
    (by simp only [tensorHom_id_id, Category.id_comp, postcomp])

/-- Let R be a ring and equip ModuleCat.{v} R with a monoidal structure additive in both
variables. Let P : K₁ ⊗ K₂ ⟶ K₃ be a chain pairing of ℕ-indexed chain complexes. Let f : K₃ ⟶
L be a chain map and write S_n for positiveImages P n. Assume K₁.d 1 0 = 0 and K₂.d 1 0 = 0,
so these image families define quotient complexes. For every n : ℕ and x : K₃.X n, the
degree-n quotient map sends S_n.mkQ x to (positiveImages (P.postcomp f) n).mkQ ((f.f n).hom
x). -/
theorem positiveImageQuotientPostcompMap_mk (n : ℕ) (x : K₃.X n) :
    ((positiveImageQuotientPostcompMap P f h₁ h₂).f n).hom
        ((positiveImages P n).mkQ x) =
      (positiveImages (P.postcomp f) n).mkQ ((f.f n).hom x) := rfl

/-- Let R be a ring and equip ModuleCat.{v} R with a monoidal structure additive in both
variables. Let P : K₁ ⊗ K₂ ⟶ K₃ be a chain pairing of ℕ-indexed chain complexes. Let f : K₃ ⟶
L be a chain map and write S_n for positiveImages P n. Assume K₁.d 1 0 = 0 and K₂.d 1 0 = 0,
so these image families define quotient complexes. Writing π_P and π_(P.f) for the two
quotient projections, one has π_P ≫ positiveImageQuotientPostcompMap P f h₁ h₂ = f ≫ π_(P.f)
as chain maps. -/
@[reassoc]
theorem positiveImageQuotientPostcompMap_projection :
    positiveImageProjection P h₁ h₂ ≫ positiveImageQuotientPostcompMap P f h₁ h₂ =
      f ≫ positiveImageProjection (P.postcomp f) h₁ h₂ :=
  positiveImageProjection_map P h₁ h₂ (P.postcomp f) h₁ h₂ (𝟙 K₁) (𝟙 K₂) f
    (by simp only [tensorHom_id_id, Category.id_comp, postcomp])

/-- Let R be a ring and equip ModuleCat.{v} R with a monoidal structure additive in both
variables. Let P : K₁ ⊗ K₂ ⟶ K₃ be a chain pairing of ℕ-indexed chain complexes. Let f : K₃ ⟶
L be a chain map and write S_n for positiveImages P n. Assume K₁.d 1 0 = 0 and K₂.d 1 0 = 0,
so these image families define quotient complexes. For n : ℕ, the kernel of the induced degree
quotient map equals (LinearMap.ker (f.f n).hom).map S_n.mkQ. As a submodule of K₃.X n/S_n, it
is (ker f_n + S_n)/S_n. -/
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

/-- Let R be a ring and equip ModuleCat.{v} R with a monoidal structure additive in both
variables. Let P : K₁ ⊗ K₂ ⟶ K₃ be a chain pairing of ℕ-indexed chain complexes. Let f : K₃ ⟶
L be a chain map and write S_n for positiveImages P n. Assume K₁.d 1 0 = 0 and K₂.d 1 0 = 0,
so these image families define quotient complexes. If (f.f n).hom is surjective for a
particular n : ℕ, then the degree-n component of positiveImageQuotientPostcompMap P f h₁ h₂ is
surjective. -/
theorem positiveImageQuotientPostcompMap_surjective (n : ℕ)
    (hf : Function.Surjective (f.f n).hom) :
    Function.Surjective ((positiveImageQuotientPostcompMap P f h₁ h₂).f n).hom := by
  intro z
  refine Quotient.inductionOn' z ?_
  intro y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨(positiveImages P n).mkQ x, rfl⟩

end HomologicalComplex.ChainGradedPairing
