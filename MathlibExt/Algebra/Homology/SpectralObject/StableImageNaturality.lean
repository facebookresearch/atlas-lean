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

public import MathlibExt.Algebra.Homology.SpectralObject.StableImageConvergence
public import MathlibExt.Algebra.Homology.SpectralObject.PageCore
public import MathlibExt.Algebra.Homology.SpectralObjectMapNaturality
/-!
# Naturality of stable-image graded comparisons

For abelian-group spectral objects on a preorder with endpoints, the
stable-to-finite window map induced by a change of the left cut is natural.
For an antitone cut sequence a_k and fixed c≥a₀, the right-interval tower
G_k=Hⁿ(a_k,⊤) restricts to Hⁿ(c,⊤), with kernel tower K.

When the full-endpoint cone is limiting and K is Mittag–Leffler, the
comparison at an attained image stage R identifies Eⁿ(a_R,a₀,c,⊤)
with F_c/F_{a₀}, where F_i is the full-abutment restriction kernel.
These comparisons are natural in spectral-object maps. Right padding uses
the stated H^{n−1}(d,⊤)=0 hypotheses, and changing equal cuts or growing
the left and right window bounds preserves the comparisons.

For EInt skeletal cuts a_k=−p−1−k, the page-to-graded comparisons commute
with spectral-object maps at a common attained image stage and with
equal page-index identifications.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows Opposite
open CategoryTheory.Abelian.SpectralObject

universe u v

namespace CategoryTheory.Abelian.SpectralObject

variable {ι : Type v} [Preorder ι] [OrderBot ι] [OrderTop ι]
variable {S T : SpectralObject AddCommGrpCat.{u} ι}

/-- Let ι be a preorder with endpoints, φ:S → T a morphism of
abelian-group spectral objects, n∈ℤ, a:ℕ → ι antitone and a₀≤c.

For every R, the stable-to-finite maps E_Wⁿ(⊥,a₀,c,⊤) → E_Wⁿ(a_R,a₀,c,⊤) commute with the E-window maps induced by φ. -/
@[reassoc]
theorem Hom.stableImagePageComparison_naturality (φ : S ⟶ T)
    (n : ℤ) (a : ℕ → ι) (ha : Antitone a) (c : ι) (hc : a 0 ≤ c) (R : ℕ) :
    stableImagePageComparison S n a ha c hc R ≫
        φ.EMap (homOfLE (ha (Nat.zero_le R))) (homOfLE hc) (stableIntervalRight c)
          (n - 1) n (n + 1) =
      φ.stableIntervalMap n hc ≫ stableImagePageComparison T n a ha c hc R :=
  φ.map_EMap (homOfLE (bot_le : (⊥ : ι) ≤ a 0)) (homOfLE hc) (stableIntervalRight c)
    (homOfLE (ha (Nat.zero_le R))) (homOfLE hc) (stableIntervalRight c)
    (homMk₃ (homOfLE (bot_le : (⊥ : ι) ≤ a R)) (𝟙 (a 0)) (𝟙 c) (𝟙 (⊤ : ι))
      (by subsingleton) (by subsingleton) (by subsingleton))
    (n - 1) n (n + 1) (by omega) (by omega)

/-- Let ι be a preorder with endpoints, φ:S → T a morphism of
abelian-group spectral objects, n∈ℤ, a:ℕ → ι antitone and a₀≤c. For W=S,T set A_W=H_Wⁿ(⊥,⊤), G_k(W)=H_Wⁿ(a_k,⊤),
K_k(W)=Ker(G_k(W) → H_Wⁿ(c,⊤)), and F_i(W)=Ker(A_W → H_Wⁿ(i,⊤)).
Assume the full-endpoint cone A_W → G(W) is limiting and K(W) is
Mittag–Leffler. Let R attain the eventual image in both K₀(S) and K₀(T).

The comparisons E_Wⁿ(a_R,a₀,c,⊤) ≅ F_c(W)/F_{a₀}(W) commute with φ on the E-windows and the kernel-filtration graded quotients. -/
@[reassoc]
theorem Hom.stableImageKernelGradedIso_naturality (φ : S ⟶ T)
    (n : ℤ) (a : ℕ → ι) (ha : Antitone a) (c : ι) (hc : a 0 ≤ c)
    (hTotalS : IsLimit (stableImageTotalCone S n a ha))
    (hMLS : (stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)).IsSequentialMittagLeffler)
    (hTotalT : IsLimit (stableImageTotalCone T n a ha))
    (hMLT : (stableImageKernelTower (stableImageTowerRestriction T n a ha c hc)).IsSequentialMittagLeffler)
    (R : ℕ)
    (hRS : ((stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)) ⋙
        forget AddCommGrpCat.{u}).eventualRange (op 0) =
      Set.range ((stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)).map
        (homOfLE (Nat.zero_le R)).op))
    (hRT : ((stableImageKernelTower (stableImageTowerRestriction T n a ha c hc)) ⋙
        forget AddCommGrpCat.{u}).eventualRange (op 0) =
      Set.range ((stableImageKernelTower (stableImageTowerRestriction T n a ha c hc)).map
        (homOfLE (Nat.zero_le R)).op)) :
    φ.EMap (homOfLE (ha (Nat.zero_le R))) (homOfLE hc) (stableIntervalRight c)
        (n - 1) n (n + 1) ≫
        (stableImageKernelGradedIso T n a ha c hc hTotalT hMLT R hRT).hom =
      (stableImageKernelGradedIso S n a ha c hc hTotalS hMLS R hRS).hom ≫
        φ.stableIntervalKernelGradedMap n hc := by
  letI := stableImagePageComparison_isIso S n a ha c hc hTotalS hMLS R hRS
  apply (cancel_epi (stableImagePageComparison S n a ha c hc R)).1
  rw [← Category.assoc, φ.stableImagePageComparison_naturality,
    Category.assoc, stableImageKernelGradedIso_comparison,
    φ.stableIntervalKernelGradedIso_naturality,
    ← Category.assoc, stableImageKernelGradedIso_comparison]

/-- Let ι be a preorder with endpoints, φ:S → T a morphism of
abelian-group spectral objects, n∈ℤ, a:ℕ → ι antitone and a₀≤c. For W=S,T set A_W=H_Wⁿ(⊥,⊤), G_k(W)=H_Wⁿ(a_k,⊤),
K_k(W)=Ker(G_k(W) → H_Wⁿ(c,⊤)), and F_i(W)=Ker(A_W → H_Wⁿ(i,⊤)).
Assume the full-endpoint cone A_W → G(W) is limiting and K(W) is
Mittag–Leffler. Let R attain the eventual image in both K₀(S) and K₀(T).

Let d≥c and assume H_W^{n−1}(d,⊤)=0 for W=S,T. The padded comparisons E_Wⁿ(a_R,a₀,c,d) ≅ F_c(W)/F_{a₀}(W) commute with φ on windows and graded quotients. -/
@[reassoc]
theorem Hom.stableImageFiniteWindowKernelGradedIso_naturality (φ : S ⟶ T)
    (n : ℤ) (a : ℕ → ι) (ha : Antitone a) (c : ι) (hc : a 0 ≤ c)
    (hTotalS : IsLimit (stableImageTotalCone S n a ha))
    (hMLS : (stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)).IsSequentialMittagLeffler)
    (hTotalT : IsLimit (stableImageTotalCone T n a ha))
    (hMLT : (stableImageKernelTower (stableImageTowerRestriction T n a ha c hc)).IsSequentialMittagLeffler)
    (R : ℕ)
    (hRS : ((stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)) ⋙
        forget AddCommGrpCat.{u}).eventualRange (op 0) =
      Set.range ((stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)).map
        (homOfLE (Nat.zero_le R)).op))
    (hRT : ((stableImageKernelTower (stableImageTowerRestriction T n a ha c hc)) ⋙
        forget AddCommGrpCat.{u}).eventualRange (op 0) =
      Set.range ((stableImageKernelTower (stableImageTowerRestriction T n a ha c hc)).map
        (homOfLE (Nat.zero_le R)).op))
    (d : ι) (hcd : c ≤ d)
    (hRightS : IsZero ((S.H (n - 1)).obj (mk₁ (stableIntervalRight d))))
    (hRightT : IsZero ((T.H (n - 1)).obj (mk₁ (stableIntervalRight d)))) :
    φ.EMap (homOfLE (ha (Nat.zero_le R))) (homOfLE hc) (homOfLE hcd)
        (n - 1) n (n + 1) ≫
        (stableImageFiniteWindowKernelGradedIso T n a ha c hc hTotalT hMLT R hRT d hcd hRightT).hom =
      (stableImageFiniteWindowKernelGradedIso S n a ha c hc hTotalS hMLS R hRS d hcd hRightS).hom ≫
        φ.stableIntervalKernelGradedMap n hc := by
  let PS := S.isoMapFourδ₄Toδ₃' (a R) (a 0) c d (⊤ : ι)
    (ha (Nat.zero_le R)) hc hcd le_top (n - 1) n (n + 1) hRightS
  let PT := T.isoMapFourδ₄Toδ₃' (a R) (a 0) c d (⊤ : ι)
    (ha (Nat.zero_le R)) hc hcd le_top (n - 1) n (n + 1) hRightT
  have hPad : PS.hom ≫ φ.EMap (homOfLE (ha (Nat.zero_le R))) (homOfLE hc) (stableIntervalRight c)
      (n - 1) n (n + 1) =
      φ.EMap (homOfLE (ha (Nat.zero_le R))) (homOfLE hc) (homOfLE hcd)
        (n - 1) n (n + 1) ≫ PT.hom :=
    φ.map_EMap (homOfLE (ha (Nat.zero_le R))) (homOfLE hc) (homOfLE hcd)
      (homOfLE (ha (Nat.zero_le R))) (homOfLE hc) (stableIntervalRight c)
      (fourδ₄Toδ₃' (a R) (a 0) c d (⊤ : ι) (ha (Nat.zero_le R)) hc hcd le_top)
      (n - 1) n (n + 1) (by omega) (by omega)
  dsimp only [stableImageFiniteWindowKernelGradedIso, Iso.trans_hom]
  change φ.EMap _ _ _ _ _ _ ≫ (PT.hom ≫ _) = (PS.hom ≫ _) ≫ _
  rw [← Category.assoc, ← hPad, Category.assoc,
    φ.stableImageKernelGradedIso_naturality, ← Category.assoc]

-- Keep the original hypothesis parameters and their order in this compatibility declaration.
/-- Let φ:S → T be a morphism of abelian-group spectral objects indexed
by a preorder with endpoints. For two ordered four-cut chains with
iₐ=jₐ for all four cuts, the canonical identifications of their
degree-n E-windows commute with the E-window maps of φ. -/

@[reassoc, nolint unusedArguments]
theorem Hom.stableImageWindowEqIso_naturality (φ : S ⟶ T) (n : ℤ)
    {i₀ i₁ i₂ i₃ j₀ j₁ j₂ j₃ : ι}
    (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂) (h₂₃ : i₂ ≤ i₃)
    (h₀₁' : j₀ ≤ j₁) (h₁₂' : j₁ ≤ j₂) (h₂₃' : j₂ ≤ j₃)
    (e₀ : i₀ = j₀) (e₁ : i₁ = j₁) (e₂ : i₂ = j₂) (e₃ : i₃ = j₃) :
    φ.EMap (homOfLE h₀₁) (homOfLE h₁₂) (homOfLE h₂₃) (n - 1) n (n + 1) ≫
        (stableImageWindowEqIso T n h₀₁ h₁₂ h₂₃ h₀₁' h₁₂' h₂₃' e₀ e₁ e₂ e₃).hom =
      (stableImageWindowEqIso S n h₀₁ h₁₂ h₂₃ h₀₁' h₁₂' h₂₃' e₀ e₁ e₂ e₃).hom ≫
        φ.EMap (homOfLE h₀₁') (homOfLE h₁₂') (homOfLE h₂₃') (n - 1) n (n + 1) := by
  subst j₀ j₁ j₂ j₃
  simp only [stableImageWindowEqIso, Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- Let φ:S → T be a morphism of abelian-group spectral objects on a
preorder with endpoints. For i₁≤i₂ and j₁≤j₂ with i₁=j₁,i₂=j₂,
the identifications F_{i₂}(W)/F_{i₁}(W) ≅ F_{j₂}(W)/F_{j₁}(W)
commute with the kernel-graded maps of φ, where
F_i(W)=Ker(H_Wⁿ(⊥,⊤) → H_Wⁿ(i,⊤)). -/
@[reassoc]
theorem Hom.stableImageKernelGradedEqIso_naturality (φ : S ⟶ T) (n : ℤ)
    {i₁ i₂ j₁ j₂ : ι} (h : i₁ ≤ i₂) (h' : j₁ ≤ j₂) (e₁ : i₁ = j₁) (e₂ : i₂ = j₂) :
    φ.stableIntervalKernelGradedMap n h ≫ (stableImageKernelGradedEqIso T n h h' e₁ e₂).hom =
      (stableImageKernelGradedEqIso S n h h' e₁ e₂).hom ≫ φ.stableIntervalKernelGradedMap n h' := by
  subst j₁ j₂
  simp only [stableImageKernelGradedEqIso, Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- Let U be an EInt-indexed abelian-group spectral object, p,q∈ℤ and n=p+q.
Put a_k=−p−1−k, G_k=H_Uⁿ(a_k,+∞), K_k=Ker(G_k → H_Uⁿ(−p,+∞)),
and assume the full-endpoint cone is limiting and K is Mittag–Leffler.

Suppose M=R, both indices attain the eventual image in K₀, and H_U^{n−1}(−p+M,+∞)=H_U^{n−1}(−p+R,+∞)=0. The comparisons from pages M+1 and R+1 agree after the canonical identification of these equal page indices. -/
theorem stableImageSkeletalPageGradedIso_transport
    (U : SpectralObject AddCommGrpCat.{u} EInt) (p q : ℤ)
    (hTotal : IsLimit (stableImageTotalCone U (p + q) (stableImageSkeletalLeftCuts p)
      (stableImageSkeletalLeftCuts_antitone p)))
    (hML : (stableImageKernelTower (stableImageTowerRestriction U (p + q)
      (stableImageSkeletalLeftCuts p) (stableImageSkeletalLeftCuts_antitone p)
      ((-p : ℤ) : EInt) (stableImageSkeletal_middle p))).IsSequentialMittagLeffler)
    (M R : ℕ) (hMR : M = R)
    (hM : ((stableImageKernelTower (stableImageTowerRestriction U (p + q)
        (stableImageSkeletalLeftCuts p) (stableImageSkeletalLeftCuts_antitone p)
        ((-p : ℤ) : EInt) (stableImageSkeletal_middle p))) ⋙ forget AddCommGrpCat.{u}).eventualRange (op 0) =
      Set.range ((stableImageKernelTower (stableImageTowerRestriction U (p + q)
        (stableImageSkeletalLeftCuts p) (stableImageSkeletalLeftCuts_antitone p)
        ((-p : ℤ) : EInt) (stableImageSkeletal_middle p))).map (homOfLE (Nat.zero_le M)).op))
    (hR : ((stableImageKernelTower (stableImageTowerRestriction U (p + q)
        (stableImageSkeletalLeftCuts p) (stableImageSkeletalLeftCuts_antitone p)
        ((-p : ℤ) : EInt) (stableImageSkeletal_middle p))) ⋙ forget AddCommGrpCat.{u}).eventualRange (op 0) =
      Set.range ((stableImageKernelTower (stableImageTowerRestriction U (p + q)
        (stableImageSkeletalLeftCuts p) (stableImageSkeletalLeftCuts_antitone p)
        ((-p : ℤ) : EInt) (stableImageSkeletal_middle p))).map (homOfLE (Nat.zero_le R)).op))
    (zM : IsZero ((U.H (p + q - 1)).obj (mk₁ (stableIntervalRight (((-p + (M : ℤ) : ℤ) : EInt))))))
    (zR : IsZero ((U.H (p + q - 1)).obj (mk₁ (stableIntervalRight (((-p + (R : ℤ) : ℤ) : EInt)))))) :
    (U.skeletalSpectralSequence.pageXIsoOfEq (p, q) ((R : ℤ) + 1) ((M : ℤ) + 1)
      (by omega) (by omega)).hom ≫ (stableImageSkeletalPageGradedIso U p q hTotal hML M hM zM).hom =
      (stableImageSkeletalPageGradedIso U p q hTotal hML R hR zR).hom := by
  subst M
  simp only [SpectralSequence.pageXIsoOfEq, eqToIso_refl, Iso.refl_hom, Category.id_comp]

end CategoryTheory.Abelian.SpectralObject

namespace CategoryTheory.Abelian.SpectralObject

variable {ι : Type v} [Preorder ι] [OrderBot ι] [OrderTop ι]
variable (S : SpectralObject AddCommGrpCat.{u} ι)

/-- Let S be an abelian-group spectral object on a preorder with endpoints.
Fix n∈ℤ, antitone a:ℕ → ι and a₀≤c. Suppose its full-endpoint
cone over H_Sⁿ(a_k,⊤) is limiting and the kernels of restriction to
H_Sⁿ(c,⊤) form a Mittag–Leffler tower. Let R≤M both attain the
eventual kernel image, c≤d≤d′, and
H_S^{n−1}(d,⊤)=H_S^{n−1}(d′,⊤)=0.
From E_Sⁿ(a_M,a₀,c,d), the left-index map to the R-window followed by
its graded comparison equals the right-index map to the d′-window
followed by the M-comparison; both target F_c/F_{a₀}. -/
theorem stableImageFiniteWindowKernelGradedIso_indexing
    (n : ℤ) (a : ℕ → ι) (ha : Antitone a) (c : ι) (hc : a 0 ≤ c)
    (hTotal : IsLimit (stableImageTotalCone S n a ha))
    (hML : (stableImageKernelTower
      (stableImageTowerRestriction S n a ha c hc)).IsSequentialMittagLeffler)
    (R M : ℕ) (hRM : R ≤ M)
    (hR : ((stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)) ⋙
        forget AddCommGrpCat.{u}).eventualRange (op 0) =
      Set.range ((stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)).map
        (homOfLE (Nat.zero_le R)).op))
    (hM : ((stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)) ⋙
        forget AddCommGrpCat.{u}).eventualRange (op 0) =
      Set.range ((stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)).map
        (homOfLE (Nat.zero_le M)).op))
    {d d' : ι} (hcd : c ≤ d) (hdd : d ≤ d')
    (hRight : IsZero ((S.H (n - 1)).obj (mk₁ (stableIntervalRight d))))
    (hRight' : IsZero ((S.H (n - 1)).obj (mk₁ (stableIntervalRight d')))) :
    S.mapFourδ₁Toδ₀' (a M) (a R) (a 0) c d (ha hRM) (ha (Nat.zero_le R))
        hc hcd (n - 1) n (n + 1) ≫
      (stableImageFiniteWindowKernelGradedIso S n a ha c hc hTotal hML R hR d hcd hRight).hom =
    S.mapFourδ₄Toδ₃' (a M) (a 0) c d d' (ha (Nat.zero_le M)) hc hcd hdd
        (n - 1) n (n + 1) ≫
      (stableImageFiniteWindowKernelGradedIso S n a ha c hc hTotal hML M hM d'
        (hcd.trans hdd) hRight').hom := by
  letI := stableImagePageComparison_isIso S n a ha c hc hTotal hML M hM
  let PR := S.isoMapFourδ₄Toδ₃' (a R) (a 0) c d (⊤ : ι)
    (ha (Nat.zero_le R)) hc hcd le_top (n - 1) n (n + 1) hRight
  let PM := S.isoMapFourδ₄Toδ₃' (a M) (a 0) c d (⊤ : ι)
    (ha (Nat.zero_le M)) hc hcd le_top (n - 1) n (n + 1) hRight
  let PM' := S.isoMapFourδ₄Toδ₃' (a M) (a 0) c d' (⊤ : ι)
    (ha (Nat.zero_le M)) hc (hcd.trans hdd) le_top (n - 1) n (n + 1) hRight'
  let L := S.mapFourδ₁Toδ₀' (a M) (a R) (a 0) c (⊤ : ι)
    (ha hRM) (ha (Nat.zero_le R)) hc le_top (n - 1) n (n + 1)
  have hSquare :
      S.mapFourδ₁Toδ₀' (a M) (a R) (a 0) c d (ha hRM) (ha (Nat.zero_le R))
          hc hcd (n - 1) n (n + 1) ≫ PR.hom = PM.hom ≫ L :=
    S.mapFourδ₁Toδ₀'_mapFourδ₃Toδ₃' (a M) (a R) (a 0) c d (⊤ : ι)
      (ha hRM) (ha (Nat.zero_le R)) hc hcd le_top (n - 1) n (n + 1)
  have hRightIndex :
      S.mapFourδ₄Toδ₃' (a M) (a 0) c d d' (ha (Nat.zero_le M)) hc hcd hdd
          (n - 1) n (n + 1) ≫ PM'.hom = PM.hom :=
    S.mapFourδ₄Toδ₃'_comp (a M) (a 0) c d d' (⊤ : ι)
      (ha (Nat.zero_le M)) hc hcd hdd le_top (n - 1) n (n + 1)
  have hComparison : stableImagePageComparison S n a ha c hc M ≫ L =
      stableImagePageComparison S n a ha c hc R :=
    S.mapFourδ₁Toδ₀'_comp (⊥ : ι) (a M) (a R) (a 0) c (⊤ : ι)
      bot_le (ha hRM) (ha (Nat.zero_le R)) hc le_top (n - 1) n (n + 1)
  have hGraded : L ≫ (stableImageKernelGradedIso S n a ha c hc hTotal hML R hR).hom =
      (stableImageKernelGradedIso S n a ha c hc hTotal hML M hM).hom := by
    apply (cancel_epi (stableImagePageComparison S n a ha c hc M)).1
    rw [← Category.assoc, hComparison, stableImageKernelGradedIso_comparison,
      stableImageKernelGradedIso_comparison]
  change _ ≫ (PR.hom ≫ _) = _ ≫ (PM'.hom ≫ _)
  rw [← Category.assoc, hSquare, Category.assoc, hGraded,
    ← Category.assoc, hRightIndex]

end CategoryTheory.Abelian.SpectralObject
namespace CategoryTheory.Abelian.SpectralObject

variable {S T : SpectralObject AddCommGrpCat.{u} EInt}

/-- Let φ:S → T be a map of EInt-indexed abelian-group spectral objects.
Fix p,q∈ℤ, n=p+q and a_k=−p−1−k. For W=S,T assume the cone
H_Wⁿ(−∞,+∞) over H_Wⁿ(a_k,+∞) is limiting and the kernel tower
of restriction to H_Wⁿ(−p,+∞) is Mittag–Leffler.
Let R attain both eventual kernel images, and suppose
H_W^{n−1}(−p+R,+∞)=0 for both objects.
The comparisons E_{R+1}^{p,q}(W) ≅ GrᵖA_n(W) commute with the
page map and associated-graded map induced by φ. -/
@[reassoc]
theorem Hom.stableImageSkeletalPageGradedIso_naturality (φ : S ⟶ T) (p q : ℤ)
    (hTotalS : IsLimit (stableImageTotalCone S (p + q) (stableImageSkeletalLeftCuts p)
      (stableImageSkeletalLeftCuts_antitone p)))
    (hMLS : (stableImageKernelTower (stableImageTowerRestriction S (p + q)
      (stableImageSkeletalLeftCuts p) (stableImageSkeletalLeftCuts_antitone p)
      ((-p : ℤ) : EInt) (stableImageSkeletal_middle p))).IsSequentialMittagLeffler)
    (hTotalT : IsLimit (stableImageTotalCone T (p + q) (stableImageSkeletalLeftCuts p)
      (stableImageSkeletalLeftCuts_antitone p)))
    (hMLT : (stableImageKernelTower (stableImageTowerRestriction T (p + q)
      (stableImageSkeletalLeftCuts p) (stableImageSkeletalLeftCuts_antitone p)
      ((-p : ℤ) : EInt) (stableImageSkeletal_middle p))).IsSequentialMittagLeffler)
    (R : ℕ)
    (hRS : ((stableImageKernelTower (stableImageTowerRestriction S (p + q)
        (stableImageSkeletalLeftCuts p) (stableImageSkeletalLeftCuts_antitone p)
        ((-p : ℤ) : EInt) (stableImageSkeletal_middle p))) ⋙ forget AddCommGrpCat.{u}).eventualRange (op 0) =
      Set.range ((stableImageKernelTower (stableImageTowerRestriction S (p + q)
        (stableImageSkeletalLeftCuts p) (stableImageSkeletalLeftCuts_antitone p)
        ((-p : ℤ) : EInt) (stableImageSkeletal_middle p))).map (homOfLE (Nat.zero_le R)).op))
    (hRT : ((stableImageKernelTower (stableImageTowerRestriction T (p + q)
        (stableImageSkeletalLeftCuts p) (stableImageSkeletalLeftCuts_antitone p)
        ((-p : ℤ) : EInt) (stableImageSkeletal_middle p))) ⋙ forget AddCommGrpCat.{u}).eventualRange (op 0) =
      Set.range ((stableImageKernelTower (stableImageTowerRestriction T (p + q)
        (stableImageSkeletalLeftCuts p) (stableImageSkeletalLeftCuts_antitone p)
        ((-p : ℤ) : EInt) (stableImageSkeletal_middle p))).map (homOfLE (Nat.zero_le R)).op))
    (hRightS : IsZero ((S.H (p + q - 1)).obj
      (mk₁ (stableIntervalRight (((-p + (R : ℤ) : ℤ) : EInt))))))
    (hRightT : IsZero ((T.H (p + q - 1)).obj
      (mk₁ (stableIntervalRight (((-p + (R : ℤ) : ℤ) : EInt)))))) :
    (φ.spectralSequencePageMap skeletalPageCore ((R : ℤ) + 1) (by omega)).f (p, q) ≫
        (stableImageSkeletalPageGradedIso T p q hTotalT hMLT R hRT hRightT).hom =
      (stableImageSkeletalPageGradedIso S p q hTotalS hMLS R hRS hRightS).hom ≫
        φ.skeletalAbutmentGradedMap (p + q) p := by
  let r : ℤ := (R : ℤ) + 1
  have hr : 1 ≤ r := by dsimp [r]; omega
  let a := stableImageSkeletalLeftCuts p
  let ha := stableImageSkeletalLeftCuts_antitone p
  let c : EInt := ((-p : ℤ) : EInt)
  let hc := stableImageSkeletal_middle p
  let d : EInt := ((-p + (R : ℤ) : ℤ) : EInt)
  have hcd : c ≤ d := by simp [c, d]
  have h₀₁ : ((-p - r : ℤ) : EInt) ≤ ((-(p + 1) : ℤ) : EInt) := by simp; dsimp [r]; omega
  have h₁₂ : ((-(p + 1) : ℤ) : EInt) ≤ c := by simp [c]
  have h₂₃ : c ≤ ((-p + r - 1 : ℤ) : EInt) := by simp [c]; dsimp [r]; omega
  have e₀ : ((-p - r : ℤ) : EInt) = a R := by
    apply congrArg (fun i : ℤ => (i : EInt))
    dsimp [a, stableImageSkeletalLeftCuts, r]
    omega
  have e₁ : ((-(p + 1) : ℤ) : EInt) = a 0 := by simp [a, stableImageSkeletalLeftCuts]
  have e₃ : ((-p + r - 1 : ℤ) : EInt) = d := by
    apply congrArg (fun i : ℤ => (i : EInt))
    dsimp [d, r]
    omega
  let eS := stableImageWindowEqIso S (p + q) h₀₁ h₁₂ h₂₃
    (ha (Nat.zero_le R)) hc hcd e₀ e₁ rfl e₃
  let eT := stableImageWindowEqIso T (p + q) h₀₁ h₁₂ h₂₃
    (ha (Nat.zero_le R)) hc hcd e₀ e₁ rfl e₃
  let gS := stableImageKernelGradedEqIso S (p + q) hc h₁₂ e₁.symm rfl
  let gT := stableImageKernelGradedEqIso T (p + q) hc h₁₂ e₁.symm rfl
  let FS := stableImageFiniteWindowKernelGradedIso S (p + q) a ha c hc hTotalS hMLS R hRS d hcd hRightS
  let FT := stableImageFiniteWindowKernelGradedIso T (p + q) a ha c hc hTotalT hMLT R hRT d hcd hRightT
  have hW := φ.skeletalPageWindowIso_naturality r (by dsimp [r]; omega) p q
  have hE := φ.stableImageWindowEqIso_naturality (p + q) h₀₁ h₁₂ h₂₃
    (ha (Nat.zero_le R)) hc hcd e₀ e₁ rfl e₃
  have hF := φ.stableImageFiniteWindowKernelGradedIso_naturality
    (p + q) a ha c hc hTotalS hMLS hTotalT hMLT R hRS hRT d hcd hRightS hRightT
  have hG := φ.stableImageKernelGradedEqIso_naturality (p + q) hc h₁₂ e₁.symm rfl
  change (φ.spectralSequencePageMap skeletalPageCore r hr).f (p, q) ≫
      ((T.skeletalPageWindowIso r hr p q).hom ≫ eT.hom ≫ FT.hom ≫ gT.hom) =
    ((S.skeletalPageWindowIso r hr p q).hom ≫ eS.hom ≫ FS.hom ≫ gS.hom) ≫
      φ.skeletalAbutmentGradedMap (p + q) p
  have h₁ := congrArg (fun f => f ≫ eT.hom ≫ FT.hom ≫ gT.hom) hW
  have h₂ := congrArg (fun f => (S.skeletalPageWindowIso r hr p q).hom ≫ f ≫ FT.hom ≫ gT.hom) hE
  have h₃ := congrArg (fun f => (S.skeletalPageWindowIso r hr p q).hom ≫ eS.hom ≫ f ≫ gT.hom) hF
  have h₄ := congrArg (fun f => (S.skeletalPageWindowIso r hr p q).hom ≫ eS.hom ≫ FS.hom ≫ f) hG
  simp only [Category.assoc] at h₁ h₂ h₃ h₄ ⊢
  exact h₁.trans (h₂.trans (h₃.trans h₄))

end CategoryTheory.Abelian.SpectralObject


end
