/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.SpectralSequencePairing
public import MathlibExt.AlgebraicTopology.AtiyahHirzebruch.EndpointStabilization
public import MathlibExt.AlgebraicTopology.AtiyahHirzebruch.AbutmentFiltration

/-!
# Relative representatives of spectral-object intervals

For i₀≤i₁≤i₂≤i₃, the map H_n(i₀,i₂) to cycles and then the boundary quotient gives the
relative representative in the E object. It is natural in four-cut diagrams and in equality
presentations of the middle cut.

With bottom and top indices, step classes map to these finite representatives. Vanishing of
the two outer endpoint groups identifies them with stable intervals and the kernel-filtration
graded quotient, with all neighboring cohomological degrees explicit.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits ComposableArrows

universe u v w

namespace CategoryTheory.Abelian.SpectralObject

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} [Preorder ι] (Y : SpectralObject C ι)

/-- The relative interval representative of a four-cut quotient.

Map H_n(i₀,i₂) to cycles for i₀→i₁→i₂ and then project to E(i₀,i₁,i₂,i₃;n). -/
def relativeRepresentative {i₀ i₁ i₂ i₃ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃) (n : ℤ) :
    (Y.H n).obj (mk₁ (f₁ ≫ f₂)) ⟶ Y.E f₁ f₂ f₃ (n - 1) n (n + 1) (by omega) rfl :=
  Y.toCycles f₁ f₂ (f₁ ≫ f₂) rfl n ≫ Y.πE f₁ f₂ f₃ (n - 1) n (n + 1) (by omega) rfl

/-- Relative representatives commute with four-cut maps.

A morphism of four-cut diagrams carries the representative by its endpoint maps at i₀ and i₂. -/
lemma relativeRepresentative_map {i₀ i₁ i₂ i₃ j₀ j₁ j₂ j₃ : ι}
    (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (g₁ : j₀ ⟶ j₁) (g₂ : j₁ ⟶ j₂) (g₃ : j₂ ⟶ j₃)
    (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ g₁ g₂ g₃) (n : ℤ) :
    Y.relativeRepresentative f₁ f₂ f₃ n ≫ Y.map f₁ f₂ f₃ g₁ g₂ g₃ α
      (n - 1) n (n + 1) (by omega) rfl =
    (Y.H n).map (homMk₁ (α.app 0) (α.app 2) (by subsingleton)) ≫
      Y.relativeRepresentative g₁ g₂ g₃ n := by
  let β : mk₂ f₁ f₂ ⟶ mk₂ g₁ g₂ :=
    homMk₂ (α.app 0) (α.app 1) (α.app 2) (naturality' α 0 1) (naturality' α 1 2)
  let γ : mk₁ (f₁ ≫ f₂) ⟶ mk₁ (g₁ ≫ g₂) := homMk₁ (α.app 0) (α.app 2) (by subsingleton)
  have hπ := Y.πE_map f₁ f₂ f₃ g₁ g₂ g₃ α β (n - 1) n (n + 1) rfl (by omega) rfl
  have hcy := Y.toCycles_cyclesMap f₁ f₂ g₁ g₂ (f₁ ≫ f₂) rfl (g₁ ≫ g₂) rfl β γ n rfl rfl
  dsimp only [relativeRepresentative]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => Y.toCycles f₁ f₂ (f₁ ≫ f₂) rfl n ≫ z) hπ).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ Y.πE g₁ g₂ g₃ (n - 1) n (n + 1) (by omega) rfl) hcy).trans
          (Category.assoc _ _ _))))

/-- Equality transport of a relative middle cut.

An equality i₁=i₁′ gives the canonical isomorphism between the two presentations of the
relative E object. -/
def relativeMiddleIndexIso (n : ℤ) {i₀ i₁ i₁' i₂ i₃ : ι}
    (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂) (h₂₃ : i₂ ≤ i₃)
    (h₀₁' : i₀ ≤ i₁') (h₁₂' : i₁' ≤ i₂) (h : i₁ = i₁') :
    Y.E (homOfLE h₀₁) (homOfLE h₁₂) (homOfLE h₂₃) (n - 1) n (n + 1) (by omega) rfl ≅
      Y.E (homOfLE h₀₁') (homOfLE h₁₂') (homOfLE h₂₃) (n - 1) n (n + 1) (by omega) rfl := by
  subst i₁'
  exact Iso.refl _

/-- The map of the equal-middle-cut comparison.

The forward relative comparison is the equality transport morphism. -/
lemma relativeMiddleIndexIso_hom (n : ℤ) {i₀ i₁ i₁' i₂ i₃ : ι}
    (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂) (h₂₃ : i₂ ≤ i₃)
    (h₀₁' : i₀ ≤ i₁') (h₁₂' : i₁' ≤ i₂) (h : i₁ = i₁') :
    (Y.relativeMiddleIndexIso n h₀₁ h₁₂ h₂₃ h₀₁' h₁₂' h).hom =
      eqToHom (by subst i₁'; rfl) := by
  subst i₁'
  rfl

variable [OrderBot ι] [OrderTop ι]

/-- The map from a bottom-to-cut step to a finite representative.

Map H_n(⊥,i₂) to the four-cut E object using its canonical relative representative and the
left-cut change. -/
def stepToFiniteRepresentative (n : ℤ) {i₀ i₁ i₂ i₃ : ι}
    (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂) (h₂₃ : i₂ ≤ i₃) :
    Y.stableIntervalStep n i₂ ⟶
      Y.E (homOfLE h₀₁) (homOfLE h₁₂) (homOfLE h₂₃) (n - 1) n (n + 1) (by omega) rfl := by
  let β : mk₁ (stableIntervalLeftMiddle i₂) ⟶ mk₁ (homOfLE h₀₁ ≫ homOfLE h₁₂) :=
    homMk₁ (homOfLE (bot_le : (⊥ : ι) ≤ i₀)) (𝟙 i₂) (by subsingleton)
  exact (Y.H n).map β ≫ Y.relativeRepresentative (homOfLE h₀₁) (homOfLE h₁₂) (homOfLE h₂₃) n

omit [OrderTop ι] in
/-- Step representatives respect equal middle cuts.

The equality comparison of the middle index carries the step representative to its equal-index
presentation. -/
lemma stepToFiniteRepresentative_middleIso (n : ℤ) {i₀ i₁ i₁' i₂ i₃ : ι}
    (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂) (h₂₃ : i₂ ≤ i₃)
    (h₀₁' : i₀ ≤ i₁') (h₁₂' : i₁' ≤ i₂) (h : i₁ = i₁') :
    Y.stepToFiniteRepresentative n h₀₁ h₁₂ h₂₃ ≫
      (Y.relativeMiddleIndexIso n h₀₁ h₁₂ h₂₃ h₀₁' h₁₂' h).hom =
    Y.stepToFiniteRepresentative n h₀₁' h₁₂' h₂₃ := by
  subst i₁'
  exact Category.comp_id _

/-- The finite step representative agrees with its padded stable class.

Under H_{n+1}(⊥,i₀)=0 and H_{n−1}(i₃,⊤)=0, endpoint padding carries the finite representative
to the stable step class. -/
lemma stepToFiniteRepresentative_padding (n : ℤ) {i₀ i₁ i₂ i₃ : ι}
    (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂) (h₂₃ : i₂ ≤ i₃)
    (hleft : IsZero ((Y.H (n + 1)).obj (mk₁ (homOfLE (bot_le : (⊥ : ι) ≤ i₀)))))
    (hright : IsZero ((Y.H (n - 1)).obj (mk₁ (homOfLE (le_top : i₃ ≤ (⊤ : ι)))))) :
    Y.stepToFiniteRepresentative n h₀₁ h₁₂ h₂₃ ≫
      (Y.finiteIntervalPaddingIso n h₀₁ h₁₂ h₂₃ hleft hright).hom =
      Y.stableIntervalStepToStable n h₁₂ := by
  let L := Y.isoMapFourδ₁Toδ₀' (⊥ : ι) i₀ i₁ i₂ i₃ bot_le h₀₁ h₁₂ h₂₃
    (n - 1) n (n + 1) hleft (by omega) rfl
  let R := Y.isoMapFourδ₄Toδ₃' (⊥ : ι) i₁ i₂ i₃ (⊤ : ι) bot_le h₁₂ h₂₃ le_top
    (n - 1) n (n + 1) hright (by omega) rfl
  let ρ := Y.relativeRepresentative (homOfLE (bot_le : (⊥ : ι) ≤ i₁))
    (homOfLE h₁₂) (homOfLE h₂₃) n
  let f := Y.stepToFiniteRepresentative n h₀₁ h₁₂ h₂₃
  have hL : ρ ≫ L.hom = f :=
    Y.relativeRepresentative_map (homOfLE (bot_le : (⊥ : ι) ≤ i₁)) (homOfLE h₁₂) (homOfLE h₂₃)
      (homOfLE h₀₁) (homOfLE h₁₂) (homOfLE h₂₃)
      (fourδ₁Toδ₀' (⊥ : ι) i₀ i₁ i₂ i₃ bot_le h₀₁ h₁₂ h₂₃) n
  have hR : ρ ≫ R.hom = Y.stableIntervalStepToStable n h₁₂ := by
    have hs := Y.relativeRepresentative_map (homOfLE (bot_le : (⊥ : ι) ≤ i₁))
      (homOfLE h₁₂) (homOfLE h₂₃)
      (homOfLE (bot_le : (⊥ : ι) ≤ i₁)) (homOfLE h₁₂) (homOfLE (le_top : i₂ ≤ (⊤ : ι)))
      (fourδ₄Toδ₃' (⊥ : ι) i₁ i₂ i₃ (⊤ : ι) bot_le h₁₂ h₂₃ le_top) n
    change ρ ≫ R.hom = (Y.H n).map (𝟙 _) ≫ Y.stableIntervalStepToStable n h₁₂ at hs
    rw [Functor.map_id] at hs
    exact hs.trans (Category.id_comp _)
  have hf : f ≫ L.inv = ρ :=
    (congrArg (fun z => z ≫ L.inv) hL.symm).trans
      ((Category.assoc ρ L.hom L.inv).trans
        ((congrArg (fun z => ρ ≫ z) L.hom_inv_id).trans (Category.comp_id ρ)))
  change f ≫ (L.inv ≫ R.hom) = Y.stableIntervalStepToStable n h₁₂
  exact (Category.assoc f L.inv R.hom).symm.trans ((congrArg (fun z => z ≫ R.hom) hf).trans hR)

omit [Abelian C] in
private lemma quotient_comparison {S I T Q R K : C} (s : S ⟶ T) (t : S ⟶ I) (j : I ⟶ T)
    (e : T ≅ Q) (k : Q ≅ R) (b : I ≅ K) (qI : I ⟶ Q) (qK : K ⟶ R)
    (hS : t ≫ j = s) (hJ : j ≫ e.hom = qI) (hK : qI ≫ k.hom = b.hom ≫ qK) :
    s ≫ (e ≪≫ k).hom = t ≫ b.hom ≫ qK := by
  rw [← hS, Iso.trans_hom, Category.assoc, ← Category.assoc j e.hom k.hom, hJ, hK]

/-- The stable step class in a kernel-filtration graded quotient.

The stable-to-graded comparison is the step-to-image map, the image-to-kernel identification
and the canonical graded quotient projection. -/
lemma stableIntervalStepToStable_graded (n : ℤ) {i₁ i₂ : ι} (h₁₂ : i₁ ≤ i₂) :
    Y.stableIntervalStepToStable n h₁₂ ≫ (Y.stableIntervalKernelGradedIso n h₁₂).hom =
    Y.stableIntervalStepToImage n i₂ ≫ (Y.stableIntervalImageKernelIso n i₂).hom ≫
      cokernel.π (Subobject.ofLE _ _ (Y.stableIntervalKernelFiltration_monotone n h₁₂)) :=
  quotient_comparison (Y.stableIntervalStepToStable n h₁₂) (Y.stableIntervalStepToImage n i₂)
    (Y.stableIntervalImageToStable n h₁₂) (Y.stableIntervalImageCokernelIso n h₁₂)
    (Y.stableIntervalImageKernelGradedIso n h₁₂) (Y.stableIntervalImageKernelIso n i₂)
    (cokernel.π (Y.stableIntervalImageMap n h₁₂))
    (cokernel.π (Subobject.ofLE _ _ (Y.stableIntervalKernelFiltration_monotone n h₁₂)))
    (Y.stableIntervalStepToImage_comp_imageToStable n h₁₂)
    (Y.stableIntervalImageToStable_comp_iso_hom n h₁₂)
    (Y.stableIntervalImageKernelGradedIso_π n h₁₂)

/-- The finite step representative in a kernel-graded coordinate.

Under endpoint vanishing, the finite-window graded comparison gives the same image and graded
quotient representative as the stable step. -/
lemma stepToFiniteRepresentative_graded (n : ℤ) {i₀ i₁ i₂ i₃ : ι}
    (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂) (h₂₃ : i₂ ≤ i₃)
    (hleft : IsZero ((Y.H (n + 1)).obj (mk₁ (homOfLE (bot_le : (⊥ : ι) ≤ i₀)))))
    (hright : IsZero ((Y.H (n - 1)).obj (mk₁ (homOfLE (le_top : i₃ ≤ (⊤ : ι)))))) :
    Y.stepToFiniteRepresentative n h₀₁ h₁₂ h₂₃ ≫
      (Y.finiteIntervalKernelGradedIso n h₀₁ h₁₂ h₂₃ hleft hright).hom =
    Y.stableIntervalStepToImage n i₂ ≫ (Y.stableIntervalImageKernelIso n i₂).hom ≫
      cokernel.π (Subobject.ofLE _ _ (Y.stableIntervalKernelFiltration_monotone n h₁₂)) := by
  let f := Y.stepToFiniteRepresentative n h₀₁ h₁₂ h₂₃
  let p := Y.finiteIntervalPaddingIso n h₀₁ h₁₂ h₂₃ hleft hright
  let e := Y.stableIntervalKernelGradedIso n h₁₂
  have hp : f ≫ p.hom = Y.stableIntervalStepToStable n h₁₂ :=
    Y.stepToFiniteRepresentative_padding n h₀₁ h₁₂ h₂₃ hleft hright
  have he : (Y.finiteIntervalKernelGradedIso n h₀₁ h₁₂ h₂₃ hleft hright).hom = p.hom ≫ e.hom :=
    Category.assoc p.hom (Y.stableIntervalImageCokernelIso n h₁₂).hom
      (Y.stableIntervalImageKernelGradedIso n h₁₂).hom
  exact (congrArg (fun z => f ≫ z) he).trans
    ((Category.assoc f p.hom e.hom).symm.trans
      ((congrArg (fun z => z ≫ e.hom) hp).trans (Y.stableIntervalStepToStable_graded n h₁₂)))

/-- Skeletal page charts respect equal normalized middle cuts.

Replacing two middle-cut presentations equal to the skeletal core index gives the same page
chart after equality transport. -/
lemma skeletalPageXIso_middleNormalization (S : SpectralObject C EInt)
    (r : ℤ) (hr : 1 ≤ r) (pq : ℤ × ℤ) (i₀ i₁ i₁' i₂ i₃ : EInt)
    (h₀ : i₀ = skeletalPageCore.i₀ r pq) (h₁ : i₁ = skeletalPageCore.i₁ pq)
    (h₁' : i₁' = skeletalPageCore.i₁ pq) (h₂ : i₂ = skeletalPageCore.i₂ pq)
    (h₃ : i₃ = skeletalPageCore.i₃ r pq) (n : ℤ) (hn : n = skeletalPageCore.deg pq) :
    (S.spectralSequencePageXIso skeletalPageCore r hr pq i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃
      (n - 1) n (n + 1) hn (by omega) rfl).hom ≫
      (S.relativeMiddleIndexIso n (skeletalPageCore.le₀₁' r hr pq h₀ h₁)
        (skeletalPageCore.le₁₂' pq h₁ h₂) (skeletalPageCore.le₂₃' r hr pq h₂ h₃)
        (skeletalPageCore.le₀₁' r hr pq h₀ h₁') (skeletalPageCore.le₁₂' pq h₁' h₂)
        (h₁.trans h₁'.symm)).hom =
    (S.spectralSequencePageXIso skeletalPageCore r hr pq i₀ i₁' i₂ i₃ h₀ h₁' h₂ h₃
      (n - 1) n (n + 1) hn (by omega) rfl).hom := by
  have heq : i₁' = i₁ := h₁'.trans h₁.symm
  cases heq
  exact Category.comp_id (S.spectralSequencePageXIso skeletalPageCore r hr pq i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃
    (n - 1) n (n + 1) hn (by omega) rfl).hom

end CategoryTheory.Abelian.SpectralObject
