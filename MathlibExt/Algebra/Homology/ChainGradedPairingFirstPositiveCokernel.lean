/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.ChainGradedPairingFirstPositiveImages
public import MathlibExt.Algebra.Homology.HomologicalComplexCokernelHomology
public import MathlibExt.Algebra.Homology.HomologicalComplexImageCokernel
public import MathlibExt.Algebra.Homology.HomologicalComplexModuleCokernel

/-!
# The actual first-positive image quotient and its universal maps

The first factor is positive and the second factor is unrestricted. The
quotient is the native cokernel of the actual image inclusion of the accepted
first-positive pairing. Its universal comparison with the original pairing
cokernel uses the general image/coimage API, and its degree coordinates reuse
the accepted exact first-positive range theorem and cokernel degree iso.

Every original pairing square induces the actual quotient map. The coordinate
map is the native Submodule.mapQ of the original target component; its
preservation proof is earned from that square. In degree zero the defining
range vanishes, so the actual quotient projection earns the native H0 iso.
No degree-one vanishing or higher Harrison/AQ identification is asserted.

Candidate source; Native and adoption gates remain pending.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory

universe u v

namespace HomologicalComplex.ChainGradedPairing

variable {R : Type u} [Ring R]
  [MonoidalCategory (ModuleCat.{v} R)] [MonoidalPreadditive (ModuleCat.{v} R)]
  {K₁ K₂ K₃ : ChainComplex (ModuleCat.{v} R) ℕ}
  (P : ChainGradedPairing K₁ K₂ K₃) (h₁ : K₁.d 1 0 = 0)

/-- Quotient the original target by the actual native image subcomplex. -/
def firstPositiveImageQuotient : ChainComplex (ModuleCat.{v} R) ℕ :=
  cokernel (Abelian.image.ι (firstPositivePairing P h₁))

/-- The actual quotient projection from the original target. -/
def firstPositiveImageProjection : K₃ ⟶ firstPositiveImageQuotient P h₁ :=
  cokernel.π (Abelian.image.ι (firstPositivePairing P h₁))

/-- The actual image quotient represents the original first-positive action cokernel. -/
def firstPositiveImageQuotientIsoCokernel :
    firstPositiveImageQuotient P h₁ ≅ firstPositiveCokernel P h₁ :=
  Abelian.imageCokernelIso (firstPositivePairing P h₁)

/-- The comparison preserves the original target projection. -/
@[reassoc (attr := simp)]
theorem firstPositiveImageProjection_comp_iso :
    firstPositiveImageProjection P h₁ ≫ (firstPositiveImageQuotientIsoCokernel P h₁).hom =
      firstPositiveProjection P h₁ :=
  Abelian.imageCokernelIso_projection (firstPositivePairing P h₁)

/-- The inverse comparison preserves that same projection. -/
@[reassoc (attr := simp)]
theorem firstPositiveProjection_comp_imageIso_inv :
    firstPositiveProjection P h₁ ≫ (firstPositiveImageQuotientIsoCokernel P h₁).inv =
      firstPositiveImageProjection P h₁ :=
  Abelian.imageCokernelIso_projection_inv (firstPositivePairing P h₁)

/-- The native image quotient has exactly the accepted original first-positive quotient levels. -/
def firstPositiveImageQuotientDegreeIso (n : ℕ) :
    (firstPositiveImageQuotient P h₁).X n ≅ firstPositiveDegreeQuotient P n :=
  moduleImageCokernelDegreeIso (firstPositivePairing P h₁) n ≪≫
    (Submodule.quotEquivOfEq _ _ (range_firstPositivePairing P h₁ n)).toModuleIso

/-- Degree coordinates are characterized by the original module quotient map. -/
@[reassoc]
theorem firstPositiveImageProjection_degreeIso (n : ℕ) :
    (firstPositiveImageProjection P h₁).f n ≫
        (firstPositiveImageQuotientDegreeIso P h₁ n).hom =
      ModuleCat.ofHom (firstPositiveImages P n).mkQ := by
  let π : K₃.X n ⟶ (cokernel (Abelian.image.ι (firstPositivePairing P h₁))).X n :=
    (cokernel.π (Abelian.image.ι (firstPositivePairing P h₁))).f n
  let e := moduleImageCokernelDegreeIso (firstPositivePairing P h₁) n
  let q := (Submodule.quotEquivOfEq _ _ (range_firstPositivePairing P h₁ n)).toModuleIso
  have hπ : π ≫ e.hom = ModuleCat.ofHom (LinearMap.range ((firstPositivePairing P h₁).f n).hom).mkQ :=
    moduleImageCokernelDegreeIso_projection (firstPositivePairing P h₁) n
  change π ≫ (e.hom ≫ q.hom) = _
  rw [← Category.assoc, hπ]
  apply ModuleCat.hom_ext
  ext x
  exact Submodule.quotEquivOfEq_mk _ _ (range_firstPositivePairing P h₁ n) x

/-- Annihilating the native pairing is exactly annihilating its original range family. -/
theorem firstPositivePairing_comp_eq_zero_iff {L : ChainComplex (ModuleCat.{v} R) ℕ}
    (f : K₃ ⟶ L) :
    firstPositivePairing P h₁ ≫ f = 0 ↔
      ∀ n x, x ∈ firstPositiveImages P n → (f.f n).hom x = 0 := by
  constructor
  · intro hf n x hx
    rw [← range_firstPositivePairing P h₁ n] at hx
    obtain ⟨z, hz⟩ := hx
    have hc : (firstPositivePairing P h₁).f n ≫ f.f n = 0 := by
      simpa only [comp_f, zero_f] using congrArg (fun g => g.f n) hf
    rw [← hz]
    exact ConcreteCategory.congr_hom hc z
  · intro hf
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    ext x
    have hx : ((firstPositivePairing P h₁).f n).hom x ∈ firstPositiveImages P n := by
      rw [← range_firstPositivePairing P h₁ n]
      exact LinearMap.mem_range_self _ x
    exact hf n _ hx

/-- Universal descent uses the original pairing-zero equation and the native image cokernel. -/
def firstPositiveImageQuotientDesc {L : ChainComplex (ModuleCat.{v} R) ℕ}
    (f : K₃ ⟶ L) (hf : firstPositivePairing P h₁ ≫ f = 0) :
    firstPositiveImageQuotient P h₁ ⟶ L :=
  Abelian.imageCokernelDesc (firstPositivePairing P h₁) f hf

/-- The universal descent retains the original projection square. -/
@[reassoc (attr := simp)]
theorem firstPositiveImageProjection_desc {L : ChainComplex (ModuleCat.{v} R) ℕ}
    (f : K₃ ⟶ L) (hf : firstPositivePairing P h₁ ≫ f = 0) :
    firstPositiveImageProjection P h₁ ≫ firstPositiveImageQuotientDesc P h₁ f hf = f :=
  Abelian.imageCokernelDesc_projection (firstPositivePairing P h₁) f hf

/-- Original quotient values determine a universal descent. -/
theorem firstPositiveImageQuotientDesc_unique {L : ChainComplex (ModuleCat.{v} R) ℕ}
    (f : K₃ ⟶ L) (hf : firstPositivePairing P h₁ ≫ f = 0)
    (l : firstPositiveImageQuotient P h₁ ⟶ L)
    (hl : firstPositiveImageProjection P h₁ ≫ l = f) :
    l = firstPositiveImageQuotientDesc P h₁ f hf :=
  Abelian.imageCokernelDesc_unique (firstPositivePairing P h₁) f hf l hl

section Maps

variable {L₁ L₂ L₃ : ChainComplex (ModuleCat.{v} R) ℕ}
  (Q : ChainGradedPairing L₁ L₂ L₃) (g₁ : L₁.d 1 0 = 0)
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃)
  (hf : tensorHom f₁ f₂ ≫ Q = P ≫ f₃)

include h₁ g₁ f₁ f₂ hf in
/-- The original pairing square preserves every actual first-positive image. -/
theorem firstPositiveImages_map (n : ℕ) :
    firstPositiveImages P n ≤ (firstPositiveImages Q n).comap (f₃.f n).hom := by
  intro x hx
  rw [← range_firstPositivePairing P h₁ n] at hx
  obtain ⟨z, hz⟩ := hx
  rw [← hz]
  rw [← range_firstPositivePairing Q g₁ n]
  have hc := congrArg (fun f => f.f n)
    (firstPositivePairing_naturality P h₁ Q g₁ f₁ f₂ f₃ hf)
  refine ⟨((tensorHom (stupidTruncMap f₁ ComplexShape.positiveNatEmbedding) f₂).f n).hom z, ?_⟩
  exact ConcreteCategory.congr_hom hc z

/-- The degree quotient map is the native quotient of the original target component. -/
def firstPositiveDegreeQuotientMap (n : ℕ) :
    firstPositiveDegreeQuotient P n ⟶ firstPositiveDegreeQuotient Q n :=
  ModuleCat.ofHom ((firstPositiveImages P n).mapQ (firstPositiveImages Q n)
    (f₃.f n).hom (firstPositiveImages_map P h₁ Q g₁ f₁ f₂ f₃ hf n))

/-- The concrete degree map retains the actual target component on quotient classes. -/
@[reassoc]
theorem firstPositiveDegreeQuotientMap_projection (n : ℕ) :
    ModuleCat.ofHom (firstPositiveImages P n).mkQ ≫
        firstPositiveDegreeQuotientMap P h₁ Q g₁ f₁ f₂ f₃ hf n =
      f₃.f n ≫ ModuleCat.ofHom (firstPositiveImages Q n).mkQ := by
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- The accepted native degree isomorphisms are natural in the original pairing maps. -/
@[reassoc]
theorem firstPositiveCokernelDegreeIso_naturality (n : ℕ) :
    (firstPositiveCokernelMap P h₁ Q g₁ f₁ f₂ f₃ hf).f n ≫
        (firstPositiveCokernelDegreeIso Q g₁ n).hom =
      (firstPositiveCokernelDegreeIso P h₁ n).hom ≫
        firstPositiveDegreeQuotientMap P h₁ Q g₁ f₁ f₂ f₃ hf n := by
  have hπ := congrArg (fun g => g.f n)
    (firstPositiveProjection_map P h₁ Q g₁ f₁ f₂ f₃ hf)
  have hcomponent : (firstPositiveProjection P h₁).f n ≫
      (firstPositiveCokernelMap P h₁ Q g₁ f₁ f₂ f₃ hf).f n =
      f₃.f n ≫ (firstPositiveProjection Q g₁).f n := by
    simpa only [HomologicalComplex.comp_f] using hπ
  letI : Epi ((firstPositiveProjection P h₁).f n) := by
    change Epi ((cokernel.π (firstPositivePairing P h₁)).f n)
    infer_instance
  apply (cancel_epi ((firstPositiveProjection P h₁).f n)).1
  rw [← Category.assoc, hcomponent, Category.assoc, firstPositiveProjection_degreeIso,
    ← Category.assoc, firstPositiveProjection_degreeIso]
  exact (firstPositiveDegreeQuotientMap_projection P h₁ Q g₁ f₁ f₂ f₃ hf n).symm

/-- The actual image quotient map is induced by the original first-positive pairing square. -/
def firstPositiveImageQuotientMap :
    firstPositiveImageQuotient P h₁ ⟶ firstPositiveImageQuotient Q g₁ :=
  Abelian.imageCokernelMap (firstPositivePairing P h₁)
    (Arrow.homMk (tensorHom (stupidTruncMap f₁ ComplexShape.positiveNatEmbedding) f₂) f₃
      (firstPositivePairing_naturality P h₁ Q g₁ f₁ f₂ f₃ hf))

/-- The image quotient map retains the original target chain map. -/
@[reassoc (attr := simp)]
theorem firstPositiveImageProjection_map :
    firstPositiveImageProjection P h₁ ≫
        firstPositiveImageQuotientMap P h₁ Q g₁ f₁ f₂ f₃ hf =
      f₃ ≫ firstPositiveImageProjection Q g₁ :=
  Abelian.imageCokernelMap_projection (firstPositivePairing P h₁)
    (Arrow.homMk (tensorHom (stupidTruncMap f₁ ComplexShape.positiveNatEmbedding) f₂) f₃
      (firstPositivePairing_naturality P h₁ Q g₁ f₁ f₂ f₃ hf))

/-- The native image/cokernel comparison preserves original pairing-map naturality. -/
@[reassoc]
theorem firstPositiveImageQuotientIsoCokernel_naturality :
    firstPositiveImageQuotientMap P h₁ Q g₁ f₁ f₂ f₃ hf ≫
        (firstPositiveImageQuotientIsoCokernel Q g₁).hom =
      (firstPositiveImageQuotientIsoCokernel P h₁).hom ≫
        firstPositiveCokernelMap P h₁ Q g₁ f₁ f₂ f₃ hf :=
  Abelian.imageCokernelIso_naturality (firstPositivePairing P h₁)
    (Arrow.homMk (tensorHom (stupidTruncMap f₁ ComplexShape.positiveNatEmbedding) f₂) f₃
      (firstPositivePairing_naturality P h₁ Q g₁ f₁ f₂ f₃ hf))

/-- The image quotient's exact original range coordinates preserve the concrete degree map. -/
@[reassoc]
theorem firstPositiveImageQuotientDegreeIso_naturality (n : ℕ) :
    (firstPositiveImageQuotientMap P h₁ Q g₁ f₁ f₂ f₃ hf).f n ≫
        (firstPositiveImageQuotientDegreeIso Q g₁ n).hom =
      (firstPositiveImageQuotientDegreeIso P h₁ n).hom ≫
        firstPositiveDegreeQuotientMap P h₁ Q g₁ f₁ f₂ f₃ hf n := by
  have hπ := congrArg (fun g => g.f n)
    (firstPositiveImageProjection_map P h₁ Q g₁ f₁ f₂ f₃ hf)
  have hcomponent : (firstPositiveImageProjection P h₁).f n ≫
      (firstPositiveImageQuotientMap P h₁ Q g₁ f₁ f₂ f₃ hf).f n =
      f₃.f n ≫ (firstPositiveImageProjection Q g₁).f n := by
    simpa only [HomologicalComplex.comp_f] using hπ
  letI : Epi ((firstPositiveImageProjection P h₁).f n) := by
    change Epi ((cokernel.π (Abelian.image.ι (firstPositivePairing P h₁))).f n)
    infer_instance
  apply (cancel_epi ((firstPositiveImageProjection P h₁).f n)).1
  rw [← Category.assoc, hcomponent, Category.assoc, firstPositiveImageProjection_degreeIso,
    ← Category.assoc, firstPositiveImageProjection_degreeIso]
  exact (firstPositiveDegreeQuotientMap_projection P h₁ Q g₁ f₁ f₂ f₃ hf n).symm

end Maps

/-- The defining first-positive action has no degree-zero image. -/
theorem firstPositivePairing_f_zero : (firstPositivePairing P h₁).f 0 = 0 := by
  apply ModuleCat.hom_ext
  ext x
  have hx : ((firstPositivePairing P h₁).f 0).hom x ∈ firstPositiveImages P 0 := by
    rw [← range_firstPositivePairing P h₁ 0]
    exact LinearMap.mem_range_self _ x
  simpa only [firstPositiveImages_zero, Submodule.mem_bot, ModuleCat.hom_zero, LinearMap.zero_apply] using hx

/-- The actual first-image projection retains every original degree-zero coefficient. -/
theorem firstPositiveImageProjection_f_zero_isIso :
    IsIso ((firstPositiveImageProjection P h₁).f 0) := by
  letI : IsIso ((firstPositiveProjection P h₁).f 0) :=
    isIso_cokernelProjection_f_of_zero (firstPositivePairing P h₁) 0
      (firstPositivePairing_f_zero P h₁)
  have h := congrArg (fun g => g.f 0) (firstPositiveProjection_comp_imageIso_inv P h₁)
  rw [← h]
  change IsIso ((firstPositiveProjection P h₁).f 0 ≫
    (firstPositiveImageQuotientIsoCokernel P h₁).inv.f 0)
  infer_instance

/-- Only the earned degree-zero vanishing is used to compare actual target and quotient H0. -/
def firstPositiveImageHomologyZeroIso [K₃.HasHomology 0]
    [(firstPositiveImageQuotient P h₁).HasHomology 0] :
    K₃.homology 0 ≅ (firstPositiveImageQuotient P h₁).homology 0 :=
  cokernelHomologyZeroIso (firstPositivePairing P h₁) (firstPositivePairing_f_zero P h₁) ≪≫
    (imageCokernelHomologyIso (firstPositivePairing P h₁) 0).symm

/-- The H0 isomorphism's actual forward map is induced by the original image projection. -/
theorem firstPositiveImageHomologyZeroIso_hom [K₃.HasHomology 0]
    [(firstPositiveImageQuotient P h₁).HasHomology 0] :
    (firstPositiveImageHomologyZeroIso P h₁).hom =
      homologyMap (firstPositiveImageProjection P h₁) 0 := by
  apply (cancel_mono (imageCokernelHomologyIso (firstPositivePairing P h₁) 0).hom).1
  change (_ ≫ (imageCokernelHomologyIso (firstPositivePairing P h₁) 0).inv) ≫
      (imageCokernelHomologyIso (firstPositivePairing P h₁) 0).hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (imageCokernelHomologyIso_projection (firstPositivePairing P h₁) 0).symm

end HomologicalComplex.ChainGradedPairing

end
