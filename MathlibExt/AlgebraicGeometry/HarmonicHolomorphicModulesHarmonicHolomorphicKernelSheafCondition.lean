/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModuleModels
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Geometry.Manifold.ContMDiff.Defs

/-!
# Sheaf gluing for the harmonic holomorphic kernel

Compatible families of sections of the holomorphic kernel presheaf over a
covering sieve glue uniquely: the pointwise-glued section is smooth by
locality of `ContMDiffOn` and lies in the kernel by locality of the bar
equation, with no integrability hypothesis. This proves
`harmonic_holomorphic_kernel_sheaf_condition`. Simpson, alg-geom/9604005v1,
section 2, printed pages 9--11.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open MathlibExt.AlgebraicGeometry.KahlerClassGeometry
open MathlibExt.AlgebraicGeometry.SmoothHarmonicBundleGeometry
open MathlibExt.AlgebraicGeometry.HarmonicHorizontalSheaves
open MathlibExt.AlgebraicGeometry.HarmonicHolomorphicSectionKernels
open MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModuleModels
open scoped Manifold ContDiff

private theorem holomorphicKernel_isSheafFor
    {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
    [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
    {r : ℕ} (B : SmoothComplexBundle n M r)
    (h : HermitianMetric B) (A : SmoothConnection B)
    [SectionCalculus B (unitaryPart B h A)] [BarMultiplicationCalculus B h A]
    (X : Opens M) (S : Sieve X) (hS : S ∈ Opens.grothendieckTopology M X)
    (x : Presieve.FamilyOfElements
      ((holomorphicModulePresheaf B h A).presheaf ⋙ forget Ab) (↑S : Presieve X))
    (hx : x.Compatible) :
    ∃! t, x.IsAmalgamation t := by
  rw [Opens.mem_grothendieckTopology] at hS
  choose Y f hf hmem using fun (p : X) => hS p.val p.property
  have hf' : ∀ p : X, (↑S : Presieve X) (f p) := hf
  have compat : ∀ (Y₁ Y₂ : Opens M) (f₁ : Y₁ ⟶ X) (f₂ : Y₂ ⟶ X)
      (h₁ : (↑S : Presieve X) f₁) (h₂ : (↑S : Presieve X) f₂)
      (z : M) (hz₁ : z ∈ Y₁) (hz₂ : z ∈ Y₂),
      (x f₁ h₁).val ⟨z, hz₁⟩ = (x f₂ h₂).val ⟨z, hz₂⟩ := by
    intro Y₁ Y₂ f₁ f₂ h₁ h₂ z hz₁ hz₂
    have heq := hx (homOfLE inf_le_left) (homOfLE inf_le_right) h₁ h₂
      (Subsingleton.elim _ _)
    have hpt := congrArg (fun v => v.val ⟨z, hz₁, hz₂⟩) heq
    exact hpt
  set s : RoughSection B X :=
    fun p => (x (f p) (hf' p)).val ⟨p.val, hmem p⟩ with hs_def
  have sag : ∀ (Y₁ : Opens M) (f₁ : Y₁ ⟶ X) (h₁ : (↑S : Presieve X) f₁)
      (z : M) (hzX : z ∈ X) (hz₁ : z ∈ Y₁),
      s ⟨z, hzX⟩ = (x f₁ h₁).val ⟨z, hz₁⟩ := by
    intro Y₁ f₁ h₁ z hzX hz₁
    simp only [hs_def]
    exact compat (Y ⟨z, hzX⟩) Y₁ (f ⟨z, hzX⟩) f₁ (hf' ⟨z, hzX⟩) h₁ z
      (hmem ⟨z, hzX⟩) hz₁
  have hsmooth : IsSmoothSection B X s := by
    intro i
    apply contMDiffOn_of_locally_contMDiffOn
    intro y hy
    obtain ⟨hyX, hyB⟩ := hy
    refine ⟨↑(Y ⟨y, hyX⟩), (Y ⟨y, hyX⟩).isOpen, hmem ⟨y, hyX⟩, ?_⟩
    have hloc := (x (f ⟨y, hyX⟩) (hf' ⟨y, hyX⟩)).property.1 i
    have hsub : (↑X ∩ B.core.baseSet i) ∩ ↑(Y ⟨y, hyX⟩) ⊆
        ↑(Y ⟨y, hyX⟩) ∩ B.core.baseSet i := by
      intro z hz
      obtain ⟨hab, hzY⟩ := hz
      obtain ⟨hzX, hzB⟩ := hab
      exact ⟨hzY, hzB⟩
    have hmono := hloc.mono hsub
    refine hmono.congr (fun z hz => ?_)
    obtain ⟨hab, hzY⟩ := hz
    obtain ⟨hzX, hzB⟩ := hab
    have hzX' : z ∈ X := hzX
    have hzY' : z ∈ Y ⟨y, hyX⟩ := hzY
    simp only [coordinateSection, dite_eq_left hzX', dite_eq_left hzY']
    rw [sag (Y ⟨y, hyX⟩) (f ⟨y, hyX⟩) (hf' ⟨y, hyX⟩) z hzX' hzY']
  have hbar : ∀ i (p : X), p.val ∈ B.core.baseSet i → ∀ u,
      barConnectionValue B h A i X s p u = 0 := by
    intro i p hp u
    have hconn : ∀ w, connectionValue B (unitaryPart B h A) i X s p w =
        connectionValue B (unitaryPart B h A) i (Y p)
          (x (f p) (hf' p)).val ⟨p.val, hmem p⟩ w := by
      intro w
      have hrestr := SectionCalculus.restriction (B := B) (A := unitaryPart B h A)
        i X (Y p) (f p).le s hsmooth ⟨p.val, hmem p⟩ hp w
      have hreq : restrictSection B (f p).le s = (x (f p) (hf' p)).val := by
        funext q
        exact sag (Y p) (f p) (hf' p) q.val ((f p).le q.property) q.property
      rw [hreq] at hrestr
      exact hrestr.symm
    calc barConnectionValue B h A i X s p u
        = barConnectionValue B h A i (Y p) (x (f p) (hf' p)).val
          ⟨p.val, hmem p⟩ u := by simp only [barConnectionValue, hconn]
      _ = 0 := (x (f p) (hf' p)).property.2 i ⟨p.val, hmem p⟩ hp u
  refine ⟨⟨s, hsmooth, hbar⟩, ?_, ?_⟩
  · intro Y₁ f₁ h₁
    apply Subtype.ext
    funext q
    exact sag Y₁ f₁ h₁ q.val ((f₁).le q.property) q.property
  · intro t ht
    apply Subtype.ext
    funext p
    have htp := ht (f p) (hf' p)
    have hpt := congrArg (fun v => v.val ⟨p.val, hmem p⟩) htp
    exact hpt

/-- The kernel of this same local PDE glues, without an integrability assumption. -/
theorem harmonic_holomorphic_kernel_sheaf_condition
    {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
    {r : ℕ}
    [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
    (B : SmoothComplexBundle n M r)
    (h : HermitianMetric B) (A : SmoothConnection B)
    [SectionCalculus B (unitaryPart B h A)] [BarMultiplicationCalculus B h A] :
    KernelSheafCondition B h A := by
  refine ⟨?_⟩
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget Ab),
    isSheaf_iff_isSheaf_of_type]
  intro X S hS x hx
  exact holomorphicKernel_isSheafFor B h A X S hS x hx
