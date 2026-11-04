/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.GradedAlgebra.MultigradedFreeResolution
public import Mathlib.LinearAlgebra.Dimension.Finite

import MathlibExt.RingTheory.GradedAlgebra.FiniteHomogeneousGenerators
import MathlibExt.RingTheory.Polynomial.HilbertSyzygy
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Finiteness.Nakayama

/-!
# Finite multigraded free resolutions over polynomial rings

Existence of a finite multigraded free resolution with finite homogeneous
basis types for every finitely generated module carrying the campaign
multigrading over `MvPolynomial (Fin n) K`.

Direct source for the existence claim: Hoffman–Wang,
*Regularity and Resolutions for Multigraded Modules*,
https://export.arxiv.org/e-print/math/0601101v1 lines 592-612, which states
that any finitely generated multigraded module has a finite free graded
resolution by finite direct sums of shifted copies of the polynomial algebra.

Motivation and multigraded Betti / Poincaré-series context: Braun–Davis,
*Antichain Simplices*, Journal of Integer Sequences 23 (2020),
https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex lines 856-876,
which records the Hilbert Syzygy consequence that the Poincaré series is a
polynomial over a polynomial ring. That JIS passage motivates this edge but
is not its proof source.

This edge claims finite termination only: no numerical bound `≤ n`, no
minimality or uniqueness, no base change, and no Poincaré-series conclusion.
-/

@[expose] public section

namespace MetaMathlibExt

universe u

open CategoryTheory MvPolynomial

noncomputable section

private theorem mgsyz_natDegreeToInt_add {n : ℕ} (a b : Fin n →₀ ℕ) :
    natDegreeToInt (a + b) = natDegreeToInt a + natDegreeToInt b := by
  apply Finsupp.mapRange_add
  exact Nat.cast_add

private theorem mgsyz_natDegreeToInt_zero {n : ℕ} :
    natDegreeToInt (0 : Fin n →₀ ℕ) = 0 := by
  exact Finsupp.mapRange_zero

private theorem mgsyz_natDegreeToInt_eq_zero_iff {n : ℕ} (a : Fin n →₀ ℕ) :
    natDegreeToInt a = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply Finsupp.mapRange_injective (fun x : ℕ => (x : ℤ)) (by simp)
        Nat.cast_injective
    simpa [natDegreeToInt] using h
  · rintro rfl
    exact mgsyz_natDegreeToInt_zero

private def mgsyz_freeComponent (K : Type u) [Field K] {n : ℕ} {ι : Type u}
    (δ : ι → Fin n →₀ ℤ) (α : Fin n →₀ ℤ) :
    letI : Module K (ι →₀ MvPolynomial (Fin n) K) :=
      Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)
    Submodule K (ι →₀ MvPolynomial (Fin n) K) := by
  letI : Module K (ι →₀ MvPolynomial (Fin n) K) :=
    Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)
  exact
    { carrier := fun f => ∀ j a, a ∈ (f j).support →
        natDegreeToInt a + δ j = α
      zero_mem' := by
        intro j a ha
        simp at ha
      add_mem' := by
        intro f g hf hg j a ha
        have ha' := MvPolynomial.support_add ha
        simp only [Finset.mem_union] at ha'
        rcases ha' with ha' | ha'
        · exact hf j a ha'
        · exact hg j a ha'
      smul_mem' := by
        intro k f hf j a ha
        change a ∈ (MvPolynomial.C k * f j).support at ha
        rw [MvPolynomial.C_mul'] at ha
        exact hf j a (MvPolynomial.support_smul ha) }

private noncomputable def mgsyz_freeProj (K : Type u) [Field K] {n : ℕ} {ι : Type u}
    (δ : ι → Fin n →₀ ℤ) (β : Fin n →₀ ℤ)
    (f : ι →₀ MvPolynomial (Fin n) K) : ι →₀ MvPolynomial (Fin n) K := by
  classical
  exact ∑ j ∈ f.support, Finsupp.single j
    (∑ a ∈ (f j).support with natDegreeToInt a + δ j = β,
      MvPolynomial.monomial a ((f j).coeff a))

private theorem mgsyz_freeProj_apply (K : Type u) [Field K] {n : ℕ} {ι : Type u}
    (δ : ι → Fin n →₀ ℤ) (β : Fin n →₀ ℤ)
    (f : ι →₀ MvPolynomial (Fin n) K) (j : ι) :
    mgsyz_freeProj K δ β f j =
      ∑ a ∈ (f j).support with natDegreeToInt a + δ j = β,
        MvPolynomial.monomial a ((f j).coeff a) := by
  classical
  rw [mgsyz_freeProj, Finsupp.finsetSum_apply]
  by_cases hj : j ∈ f.support
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b hb hbj
      simp [hbj]
    · intro h
      exact (h hj).elim
  · rw [Finset.sum_eq_zero]
    · have hfj : f j = 0 := by
        simpa [Finsupp.mem_support_iff] using hj
      rw [hfj]
      simp
    · intro b hb
      simp [show b ≠ j by
        intro h
        exact hj (h ▸ hb)]

private theorem mgsyz_freeProj_mem (K : Type u) [Field K] {n : ℕ} {ι : Type u}
    (δ : ι → Fin n →₀ ℤ) (β : Fin n →₀ ℤ)
    (f : ι →₀ MvPolynomial (Fin n) K) :
    letI : Module K (ι →₀ MvPolynomial (Fin n) K) :=
      Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)
    mgsyz_freeProj K δ β f ∈ mgsyz_freeComponent K δ β := by
  intro j a ha
  rw [mgsyz_freeProj_apply] at ha
  by_contra hdeg
  simp [MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial, hdeg] at ha

private noncomputable def mgsyz_freeDegrees (K : Type u) [Field K] {n : ℕ}
    {ι : Type u} (δ : ι → Fin n →₀ ℤ) (f : ι →₀ MvPolynomial (Fin n) K) :
    Finset (Fin n →₀ ℤ) :=
  f.support.biUnion fun j =>
    (f j).support.image fun a => natDegreeToInt a + δ j

private theorem mgsyz_sum_freeProj (K : Type u) [Field K] {n : ℕ} {ι : Type u}
    (δ : ι → Fin n →₀ ℤ) (f : ι →₀ MvPolynomial (Fin n) K) :
    f = ∑ β ∈ mgsyz_freeDegrees K δ f, mgsyz_freeProj K δ β f := by
  classical
  ext j a
  by_cases ha : (f j).coeff a = 0
  · simp [mgsyz_freeProj_apply, MvPolynomial.coeff_monomial, ha]
  · have haj : a ∈ (f j).support := MvPolynomial.mem_support_iff.mpr ha
    have hj : j ∈ f.support := by
      rw [Finsupp.mem_support_iff]
      intro hfj
      rw [hfj] at ha
      simp at ha
    have hdeg : natDegreeToInt a + δ j ∈ mgsyz_freeDegrees K δ f := by
      rw [mgsyz_freeDegrees, Finset.mem_biUnion]
      exact ⟨j, hj, Finset.mem_image.mpr ⟨a, haj, rfl⟩⟩
    simp [mgsyz_freeProj_apply, MvPolynomial.coeff_monomial, ha, hdeg]

private def mgsyz_freeComplement (K : Type u) [Field K] {n : ℕ} {ι : Type u}
    (δ : ι → Fin n →₀ ℤ) (α : Fin n →₀ ℤ) :
    letI : Module K (ι →₀ MvPolynomial (Fin n) K) :=
      Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)
    Submodule K (ι →₀ MvPolynomial (Fin n) K) := by
  letI : Module K (ι →₀ MvPolynomial (Fin n) K) :=
    Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)
  exact
    { carrier := fun f => ∀ j a, a ∈ (f j).support →
        natDegreeToInt a + δ j ≠ α
      zero_mem' := by
        intro j a ha
        simp at ha
      add_mem' := by
        intro f g hf hg j a ha
        have ha' := MvPolynomial.support_add ha
        simp only [Finset.mem_union] at ha'
        rcases ha' with ha' | ha'
        · exact hf j a ha'
        · exact hg j a ha'
      smul_mem' := by
        intro k f hf j a ha
        change a ∈ (MvPolynomial.C k * f j).support at ha
        rw [MvPolynomial.C_mul'] at ha
        exact hf j a (MvPolynomial.support_smul ha) }

section mgsyz_FreeDecomposition

variable (K : Type u) [Field K] {n : ℕ} {ι : Type u}

local instance : Module K (ι →₀ MvPolynomial (Fin n) K) :=
  Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)

private theorem mgsyz_freeComponent_iSupIndep (δ : ι → Fin n →₀ ℤ) :
    iSupIndep (mgsyz_freeComponent K δ) := by
  rw [iSupIndep_def]
  intro α
  have hle : (⨆ β, ⨆ (_ : β ≠ α), mgsyz_freeComponent K δ β) ≤
      mgsyz_freeComplement K δ α := by
    apply iSup_le
    intro β
    apply iSup_le
    intro hβα f hf j a ha
    exact fun hα => hβα ((hf j a ha).symm.trans hα)
  refine Disjoint.mono_right hle ?_
  rw [Submodule.disjoint_def]
  intro f hf hfc
  apply Finsupp.ext
  intro j
  apply MvPolynomial.ext
  intro a
  by_contra ha
  have has : a ∈ (f j).support := MvPolynomial.mem_support_iff.mpr ha
  exact (hfc j a has) (hf j a has)

private theorem mgsyz_freeComponent_iSup_eq_top (δ : ι → Fin n →₀ ℤ) :
    (⨆ β, mgsyz_freeComponent K δ β) = ⊤ := by
  apply eq_top_iff.mpr
  intro f hf
  rw [mgsyz_sum_freeProj K δ f]
  apply Submodule.sum_mem
  intro β hβ
  exact Submodule.mem_iSup_of_mem β (mgsyz_freeProj_mem K δ β f)

@[instance_reducible]
private noncomputable def mgsyz_freeDecomposition (δ : ι → Fin n →₀ ℤ) :
    DirectSum.Decomposition (mgsyz_freeComponent K δ) := by
  classical
  exact DirectSum.IsInternal.chooseDecomposition _
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (mgsyz_freeComponent_iSupIndep K δ) (mgsyz_freeComponent_iSup_eq_top K δ))

variable (δ : ι → Fin n →₀ ℤ)

@[instance_reducible]
private instance mgsyz_freeDecompositionInstance :
    DirectSum.Decomposition (mgsyz_freeComponent K δ) :=
  mgsyz_freeDecomposition K δ

private theorem mgsyz_decompose_free_apply (β : Fin n →₀ ℤ)
    (f : ι →₀ MvPolynomial (Fin n) K) :
    (((DirectSum.decompose (mgsyz_freeComponent K δ) f) β :
      mgsyz_freeComponent K δ β) : ι →₀ MvPolynomial (Fin n) K) =
      mgsyz_freeProj K δ β f := by
  conv_lhs => rw [mgsyz_sum_freeProj K δ f]
  rw [DirectSum.decompose_sum, DFinsupp.finsetSum_apply]
  by_cases hβ : β ∈ mgsyz_freeDegrees K δ f
  · rw [Finset.sum_eq_single β]
    · exact DirectSum.decompose_of_mem_same _ (mgsyz_freeProj_mem K δ β f)
    · intro γ hγ hγβ
      apply Subtype.ext
      exact DirectSum.decompose_of_mem_ne _ (mgsyz_freeProj_mem K δ γ f) hγβ
    · intro h
      exact (h hβ).elim
  · rw [Finset.sum_eq_zero]
    · ext j a
      by_cases ha : (f j).coeff a = 0
      · simp [mgsyz_freeProj_apply, MvPolynomial.coeff_monomial, ha]
      · have haj : a ∈ (f j).support := MvPolynomial.mem_support_iff.mpr ha
        have hj : j ∈ f.support := by
          rw [Finsupp.mem_support_iff]
          intro hfj
          rw [hfj] at ha
          simp at ha
        have hdeg : natDegreeToInt a + δ j ≠ β := by
          intro h
          apply hβ
          rw [mgsyz_freeDegrees, Finset.mem_biUnion]
          exact ⟨j, hj, Finset.mem_image.mpr ⟨a, haj, h⟩⟩
        simp [mgsyz_freeProj_apply, MvPolynomial.coeff_monomial, hdeg]
    · intro γ hγ
      apply Subtype.ext
      apply DirectSum.decompose_of_mem_ne _ (mgsyz_freeProj_mem K δ γ f)
      intro hγβ
      subst γ
      exact hβ hγ

private noncomputable def mgsyz_freeGraded :
    MultigradedPolynomialModule K n (ι →₀ MvPolynomial (Fin n) K) where
  component := mgsyz_freeComponent K δ
  decomposition := mgsyz_freeDecomposition K δ
  smul_via_C := by
    intro k f
    rfl
  monomial_mem := by
    intro s c α f hf j m hm
    change m ∈ (MvPolynomial.monomial s c * f j).support at hm
    have hmcoeff := MvPolynomial.mem_support_iff.mp hm
    rw [MvPolynomial.coeff_monomial_mul'] at hmcoeff
    split at hmcoeff
    next hs =>
      have hrest : m - s ∈ (f j).support := by
        rw [MvPolynomial.mem_support_iff]
        intro hzero
        simp [hzero] at hmcoeff
      have hdeg := hf j (m - s) hrest
      have hms : m - s + s = m := tsub_add_cancel_of_le hs
      have hnat : natDegreeToInt m =
          natDegreeToInt (m - s) + natDegreeToInt s := by
        conv_lhs => rw [← hms, mgsyz_natDegreeToInt_add]
      calc
        natDegreeToInt m + δ j =
            (natDegreeToInt (m - s) + δ j) + natDegreeToInt s := by
          rw [hnat]
          abel
        _ = α + natDegreeToInt s := by rw [hdeg]
    next hs =>
      simp at hmcoeff

private theorem mgsyz_single_mem (j : ι) :
    Finsupp.single j 1 ∈ mgsyz_freeComponent K δ (δ j) := by
  classical
  intro k a ha
  by_cases hkj : k = j
  · subst k
    rw [Finsupp.single_eq_same] at ha
    have ha0 : a = 0 := by simpa using ha
    subst a
    simp [mgsyz_natDegreeToInt_zero]
  · simp [Finsupp.single_eq_of_ne hkj] at ha

private noncomputable def mgsyz_freeModule :
    MultigradedFreeModule K n (ι →₀ MvPolynomial (Fin n) K) ι where
  graded := mgsyz_freeGraded K δ
  basis := Finsupp.basisSingleOne
  degree := δ
  basis_mem := by
    intro j
    change Finsupp.single j 1 ∈ mgsyz_freeComponent K δ (δ j)
    exact mgsyz_single_mem K δ j

private theorem mgsyz_linearCombination_isDegreeZero
    {W : Type u} [AddCommGroup W] [Module (MvPolynomial (Fin n) K) W] [Module K W]
    (gW : MultigradedPolynomialModule K n W) (g : ι → W)
    (hg : ∀ j, g j ∈ gW.component (δ j)) :
    IsDegreeZero (mgsyz_freeGraded K δ) gW
      (Finsupp.linearCombination (MvPolynomial (Fin n) K) g) := by
  classical
  intro α f hf
  change f ∈ mgsyz_freeComponent K δ α at hf
  rw [Finsupp.linearCombination_apply]
  change (∑ j ∈ f.support, f j • g j) ∈ gW.component α
  apply Submodule.sum_mem
  intro j hj
  rw [MvPolynomial.as_sum (f j), Finset.sum_smul]
  apply Submodule.sum_mem
  intro a ha
  have hmon := gW.monomial_mem a ((f j).coeff a) (δ j) (g j) (hg j)
  rw [add_comm, hf j a ha] at hmon
  exact hmon

end mgsyz_FreeDecomposition

section mgsyz_KernelGrading

variable {K : Type u} [Field K] {n : ℕ}
variable {F W : Type u} [AddCommGroup F] [Module (MvPolynomial (Fin n) K) F]
  [Module K F] [AddCommGroup W] [Module (MvPolynomial (Fin n) K) W] [Module K W]
variable (gF : MultigradedPolynomialModule K n F)
  (gW : MultigradedPolynomialModule K n W)

@[instance_reducible]
private instance mgsyz_sourceDecomposition : DirectSum.Decomposition gF.component :=
  gF.decomposition

@[instance_reducible]
private instance mgsyz_targetDecomposition : DirectSum.Decomposition gW.component :=
  gW.decomposition

private theorem mgsyz_ker_graded
    (φ : F →ₗ[MvPolynomial (Fin n) K] W) (hφ : IsDegreeZero gF gW φ)
    (q : F) (hq : q ∈ LinearMap.ker φ) (β : Fin n →₀ ℤ) :
    (((DirectSum.decompose gF.component q) β : gF.component β) : F) ∈
      LinearMap.ker φ := by
  classical
  rw [LinearMap.mem_ker]
  let qβ : F := ((DirectSum.decompose gF.component q) β : gF.component β)
  have hqβmem : qβ ∈ gF.component β :=
    ((DirectSum.decompose gF.component q) β).property
  have hφβmem : φ qβ ∈ gW.component β := hφ β qβ hqβmem
  let s := (DirectSum.decompose gF.component q).support
  have hsumF : (∑ γ ∈ s,
      (((DirectSum.decompose gF.component q) γ : gF.component γ) : F)) = q :=
    DirectSum.sum_support_decompose gF.component q
  have hsumW : (∑ γ ∈ s, φ
      (((DirectSum.decompose gF.component q) γ : gF.component γ) : F)) = 0 := by
    rw [← map_sum, hsumF]
    exact LinearMap.mem_ker.mp hq
  have hdec := congrArg (DirectSum.decompose gW.component) hsumW
  rw [DirectSum.decompose_sum, DirectSum.decompose_zero] at hdec
  have hβeq := congrArg (fun z => ((z β : gW.component β) : W)) hdec
  rw [DFinsupp.finsetSum_apply] at hβeq
  by_cases hβs : β ∈ s
  · have hoff : ∀ γ ∈ s, γ ≠ β →
        (DirectSum.decompose gW.component (φ
          (((DirectSum.decompose gF.component q) γ : gF.component γ) : F))) β = 0 := by
      intro γ hγ hγβ
      apply Subtype.ext
      apply DirectSum.decompose_of_mem_ne gW.component
      · exact hφ γ _ ((DirectSum.decompose gF.component q) γ).property
      · exact hγβ
    have hsingle := Finset.sum_eq_single β hoff (fun h => (h hβs).elim)
    rw [hsingle] at hβeq
    exact (DirectSum.decompose_of_mem_same gW.component hφβmem).symm.trans hβeq
  · have hzero : (DirectSum.decompose gF.component q) β = 0 := by
      by_contra h
      apply hβs
      simpa [s] using DFinsupp.mem_support_iff.mpr h
    change φ qβ = 0
    simp [qβ, hzero]

end mgsyz_KernelGrading

private structure mgsyz_Stage (K : Type u) [Field K] (n : ℕ) where
  W : Type u
  [addCommGroup : AddCommGroup W]
  [moduleR : Module (MvPolynomial (Fin n) K) W]
  [moduleK : Module K W]
  gW : MultigradedPolynomialModule K n W
  N : Submodule (MvPolynomial (Fin n) K) W
  graded :
    letI : DirectSum.Decomposition gW.component := gW.decomposition
    ∀ x ∈ N, ∀ β,
      (((DirectSum.decompose gW.component x) β : gW.component β) : W) ∈ N
  fg : N.FG

attribute [local instance] mgsyz_Stage.addCommGroup mgsyz_Stage.moduleR
  mgsyz_Stage.moduleK

section mgsyz_HomogeneousSpan

variable (K : Type u) [Field K] (n : ℕ) {W : Type u}
  [AddCommGroup W] [Module (MvPolynomial (Fin n) K) W] [Module K W]
variable (gW : MultigradedPolynomialModule K n W)

@[instance_reducible]
private instance mgsyz_homogeneousSpanDecomposition :
    DirectSum.Decomposition gW.component := gW.decomposition

private theorem mgsyz_exists_homogeneous_span
    (N : Submodule (MvPolynomial (Fin n) K) W)
    (graded : ∀ x ∈ N, ∀ β,
      (((DirectSum.decompose gW.component x) β : gW.component β) : W) ∈ N)
    (fg : N.FG) :
    ∃ s : Finset W,
      (∀ m ∈ s, ∃ α : Fin n →₀ ℤ, m ∈ gW.component α) ∧
      Submodule.span (MvPolynomial (Fin n) K) (s : Set W) = N := by
  classical
  obtain ⟨genCount, genFun, genSpan⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp fg
  let s : Finset W := Finset.univ.biUnion fun genIdx =>
    (DirectSum.decompose gW.component (genFun genIdx)).support.image
      (fun deg => (((DirectSum.decompose gW.component (genFun genIdx)) deg) : W))
  refine ⟨s, ?_, le_antisymm ?_ ?_⟩
  · intro homElem homMem
    rw [Finset.mem_biUnion] at homMem
    obtain ⟨genIdx, _, imageMem⟩ := homMem
    rw [Finset.mem_image] at imageMem
    obtain ⟨deg, _, rfl⟩ := imageMem
    exact ⟨deg, ((DirectSum.decompose gW.component (genFun genIdx)) deg).property⟩
  · apply Submodule.span_le.mpr
    intro homElem homMem
    rw [Finset.mem_coe, Finset.mem_biUnion] at homMem
    obtain ⟨genIdx, _, imageMem⟩ := homMem
    rw [Finset.mem_image] at imageMem
    obtain ⟨deg, _, rfl⟩ := imageMem
    apply graded (genFun genIdx)
    rw [← genSpan]
    exact Submodule.subset_span (Set.mem_range_self genIdx)
  · rw [← genSpan]
    apply Submodule.span_le.mpr
    intro genElem genRangeMem
    obtain ⟨genIdx, rfl⟩ := genRangeMem
    have recon : genFun genIdx =
        ∑ deg ∈ (DirectSum.decompose gW.component (genFun genIdx)).support,
          (((DirectSum.decompose gW.component (genFun genIdx)) deg) : W) :=
      (DirectSum.sum_support_decompose gW.component (genFun genIdx)).symm
    rw [recon]
    apply Submodule.sum_mem
    intro deg degMem
    apply Submodule.subset_span
    rw [Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨genIdx, Finset.mem_univ genIdx,
      Finset.mem_image.mpr ⟨deg, degMem, rfl⟩⟩

end mgsyz_HomogeneousSpan

section mgsyz_MinimalCover

private noncomputable def mgsyz_CoverProperty (K : Type u) [Field K] (n : ℕ)
    (S : mgsyz_Stage K n) (r : ℕ) : Prop := by
  classical
  exact ∃ s : Finset S.W,
    s.card = r ∧
        (∀ m ∈ s, ∃ α : Fin n →₀ ℤ, m ∈ S.gW.component α) ∧
      Submodule.span (MvPolynomial (Fin n) K) (s : Set S.W) = S.N

private theorem mgsyz_coverProperty_exists (K : Type u) [Field K] (n : ℕ)
    (S : mgsyz_Stage K n) :
    ∃ r, mgsyz_CoverProperty (K := K) n S r := by
  obtain ⟨s, hhom, hspan⟩ :=
    mgsyz_exists_homogeneous_span K n S.gW S.N S.graded S.fg
  exact ⟨s.card, s, rfl, hhom, hspan⟩

private noncomputable def mgsyz_minCard (K : Type u) [Field K] (n : ℕ)
    (S : mgsyz_Stage K n) : ℕ := by
  classical
  exact Nat.find (mgsyz_coverProperty_exists (K := K) n S)

private theorem mgsyz_minCard_spec (K : Type u) [Field K] (n : ℕ)
    (S : mgsyz_Stage K n) :
    mgsyz_CoverProperty (K := K) n S (mgsyz_minCard (K := K) n S) := by
  classical
  exact Nat.find_spec (mgsyz_coverProperty_exists (K := K) n S)

private noncomputable def mgsyz_cover (K : Type u) [Field K] (n : ℕ)
    (S : mgsyz_Stage K n) : Finset S.W := by
  classical
  exact Classical.choose (mgsyz_minCard_spec (K := K) n S)

private theorem mgsyz_cover_spec (K : Type u) [Field K] (n : ℕ)
    (S : mgsyz_Stage K n) :
    (mgsyz_cover (K := K) n S).card = mgsyz_minCard (K := K) n S ∧
      (∀ m ∈ mgsyz_cover (K := K) n S,
        ∃ α : Fin n →₀ ℤ, m ∈ S.gW.component α) ∧
      Submodule.span (MvPolynomial (Fin n) K)
        (mgsyz_cover (K := K) n S : Set S.W) = S.N := by
  classical
  exact Classical.choose_spec (mgsyz_minCard_spec (K := K) n S)

private theorem mgsyz_cover_card (K : Type u) [Field K] (n : ℕ)
    (S : mgsyz_Stage K n) :
    (mgsyz_cover (K := K) n S).card = mgsyz_minCard (K := K) n S :=
  (mgsyz_cover_spec (K := K) n S).1

private theorem mgsyz_cover_homogeneous (K : Type u) [Field K] (n : ℕ)
    (S : mgsyz_Stage K n) (m : S.W)
    (hm : m ∈ mgsyz_cover (K := K) n S) :
    ∃ α : Fin n →₀ ℤ, m ∈ S.gW.component α :=
  (mgsyz_cover_spec (K := K) n S).2.1 m hm

private theorem mgsyz_cover_span (K : Type u) [Field K] (n : ℕ)
    (S : mgsyz_Stage K n) :
    Submodule.span (MvPolynomial (Fin n) K)
      (mgsyz_cover (K := K) n S : Set S.W) = S.N :=
  (mgsyz_cover_spec (K := K) n S).2.2

private abbrev mgsyz_ι (K : Type u) [Field K] (n : ℕ)
    (S : mgsyz_Stage K n) : Type u := ↥(mgsyz_cover (K := K) n S)

private noncomputable def mgsyz_delta (K : Type u) [Field K] (n : ℕ)
    (S : mgsyz_Stage K n) (j : mgsyz_ι (K := K) n S) : Fin n →₀ ℤ :=
  Classical.choose (mgsyz_cover_homogeneous (K := K) n S j.1 j.2)

private theorem mgsyz_delta_mem (K : Type u) [Field K] (n : ℕ)
    (S : mgsyz_Stage K n) (j : mgsyz_ι (K := K) n S) :
    j.1 ∈ S.gW.component (mgsyz_delta (K := K) n S j) :=
  Classical.choose_spec (mgsyz_cover_homogeneous (K := K) n S j.1 j.2)

private noncomputable def mgsyz_phi (K : Type u) [Field K] (n : ℕ)
    (S : mgsyz_Stage K n) :
    (mgsyz_ι (K := K) n S →₀ MvPolynomial (Fin n) K) →ₗ[MvPolynomial (Fin n) K]
      S.W :=
  Finsupp.linearCombination (MvPolynomial (Fin n) K) fun j => j.1

private theorem mgsyz_phi_range (K : Type u) [Field K] (n : ℕ)
    (S : mgsyz_Stage K n) : LinearMap.range (mgsyz_phi (K := K) n S) = S.N := by
  rw [mgsyz_phi, Finsupp.range_linearCombination]
  change Submodule.span (MvPolynomial (Fin n) K)
    (Set.range (Subtype.val : mgsyz_ι (K := K) n S → S.W)) = S.N
  rw [Subtype.range_coe]
  exact mgsyz_cover_span (K := K) n S

private theorem mgsyz_phi_degreeZero (K : Type u) [Field K] (n : ℕ)
    (S : mgsyz_Stage K n) :
    letI : Module K (mgsyz_ι (K := K) n S →₀ MvPolynomial (Fin n) K) :=
      Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K);
    IsDegreeZero (mgsyz_freeGraded K (mgsyz_delta (K := K) n S)) S.gW
      (mgsyz_phi (K := K) n S) := by
  apply mgsyz_linearCombination_isDegreeZero
  intro j
  exact mgsyz_delta_mem (K := K) n S j

end mgsyz_MinimalCover

section mgsyz_KernelConstantCoeff

private theorem mgsyz_ker_constantCoeff (K : Type u) [Field K] (n : ℕ)
    (S : mgsyz_Stage K n)
    (q : mgsyz_ι (K := K) n S →₀ MvPolynomial (Fin n) K)
    (hq : q ∈ LinearMap.ker (mgsyz_phi (K := K) n S))
    (j : mgsyz_ι (K := K) n S) :
    letI : Module K (mgsyz_ι (K := K) n S →₀ MvPolynomial (Fin n) K) :=
      Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K);
    letI : DirectSum.Decomposition
        (mgsyz_freeComponent K (mgsyz_delta (K := K) n S)) :=
      mgsyz_freeDecomposition K (mgsyz_delta (K := K) n S);
    MvPolynomial.constantCoeff (q j) = 0 := by
  classical
  by_contra hconstant
  let β := mgsyz_delta (K := K) n S j
  let q' : mgsyz_ι (K := K) n S →₀ MvPolynomial (Fin n) K :=
    ((DirectSum.decompose
      (mgsyz_freeComponent K (mgsyz_delta (K := K) n S)) q) β :
      mgsyz_freeComponent K (mgsyz_delta (K := K) n S) β)
  have hq'ker : q' ∈ LinearMap.ker (mgsyz_phi (K := K) n S) :=
    @mgsyz_ker_graded K _ n _ _ _ _
      (Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)) _ _ _
      (mgsyz_freeGraded K (mgsyz_delta (K := K) n S)) S.gW
      (mgsyz_phi (K := K) n S) (mgsyz_phi_degreeZero K n S) q hq β
  have hq'component :
      q' ∈ mgsyz_freeComponent K (mgsyz_delta (K := K) n S) β :=
    ((DirectSum.decompose
      (mgsyz_freeComponent K (mgsyz_delta (K := K) n S)) q) β).property
  have hq'proj : q' = mgsyz_freeProj K (mgsyz_delta (K := K) n S) β q :=
    mgsyz_decompose_free_apply K (mgsyz_delta (K := K) n S) β q
  have hcoeff : (q' j).coeff 0 = (q j).coeff 0 := by
    rw [hq'proj, mgsyz_freeProj_apply]
    simp [β, mgsyz_natDegreeToInt_zero, MvPolynomial.coeff_monomial, eq_comm]
  have hcoeff_ne : (q' j).coeff 0 ≠ 0 := by
    rw [hcoeff]
    simpa [MvPolynomial.constantCoeff_eq] using hconstant
  let c := (q' j).coeff 0
  have hc : c ≠ 0 := hcoeff_ne
  have hsupport : (q' j).support = {0} := by
    ext a
    constructor
    · intro ha
      have hdeg := hq'component j a ha
      have hnat : natDegreeToInt a = 0 := by
        apply add_right_cancel (b := mgsyz_delta (K := K) n S j)
        simpa [β] using hdeg
      have ha0 := (mgsyz_natDegreeToInt_eq_zero_iff a).mp hnat
      simp [ha0]
    · intro ha
      have ha0 : a = 0 := by simpa using ha
      subst a
      exact MvPolynomial.mem_support_iff.mpr hc
  have hpolynomial : q' j = MvPolynomial.C c := by
    calc
      q' j = ∑ a ∈ (q' j).support,
          MvPolynomial.monomial a ((q' j).coeff a) := MvPolynomial.as_sum (q' j)
      _ = MvPolynomial.C c := by
        rw [hsupport]
        simp [c, MvPolynomial.monomial_zero']
  have hjSupport : j ∈ q'.support := by
    rw [Finsupp.mem_support_iff, hpolynomial]
    simp [hc]
  have hkernelEq : mgsyz_phi (K := K) n S q' = 0 := LinearMap.mem_ker.mp hq'ker
  rw [mgsyz_phi, Finsupp.linearCombination_apply] at hkernelEq
  change (∑ k ∈ q'.support, q' k • k.1) = 0 at hkernelEq
  have hsplit := Finset.add_sum_erase q'.support (fun k => q' k • k.1) hjSupport
  have hadd : q' j • j.1 + ∑ k ∈ q'.support.erase j, q' k • k.1 = 0 :=
    hsplit.trans hkernelEq
  rw [hpolynomial] at hadd
  have hsolve : MvPolynomial.C c • j.1 =
      -(∑ k ∈ q'.support.erase j, q' k • k.1) :=
    eq_neg_of_add_eq_zero_left hadd
  let t := (mgsyz_cover (K := K) n S).erase j.1
  have hsumSpan : (∑ k ∈ q'.support.erase j, q' k • k.1) ∈
      Submodule.span (MvPolynomial (Fin n) K) (t : Set S.W) := by
    apply Submodule.sum_mem
    intro k hk
    apply Submodule.smul_mem
    apply Submodule.subset_span
    rw [Finset.mem_coe, Finset.mem_erase]
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    exact ⟨fun h => hkj (Subtype.ext h), k.2⟩
  have hCcj : (MvPolynomial.C c : MvPolynomial (Fin n) K) • j.1 ∈
      Submodule.span (MvPolynomial (Fin n) K) (t : Set S.W) := by
    rw [hsolve]
    exact Submodule.neg_mem _ hsumSpan
  have hjSpan : j.1 ∈ Submodule.span (MvPolynomial (Fin n) K) (t : Set S.W) := by
    have hscaled := (Submodule.span (MvPolynomial (Fin n) K) (t : Set S.W)).smul_mem
      (MvPolynomial.C c⁻¹ : MvPolynomial (Fin n) K) hCcj
    have hC : (MvPolynomial.C c⁻¹ : MvPolynomial (Fin n) K) * MvPolynomial.C c = 1 := by
      rw [← MvPolynomial.C_mul]
      simp [hc]
    simpa only [smul_smul, hC, one_smul] using hscaled
  have htSpan :
      Submodule.span (MvPolynomial (Fin n) K) (t : Set S.W) = S.N := by
    calc
      Submodule.span (MvPolynomial (Fin n) K) (t : Set S.W) =
          Submodule.span (MvPolynomial (Fin n) K) (insert j.1 (t : Set S.W)) :=
        (Submodule.span_insert_eq_span hjSpan).symm
      _ = Submodule.span (MvPolynomial (Fin n) K)
          (mgsyz_cover (K := K) n S : Set S.W) := by
        rw [← Finset.coe_insert, show insert j.1 t = mgsyz_cover (K := K) n S by
          exact Finset.insert_erase j.2]
      _ = S.N := mgsyz_cover_span (K := K) n S
  have htProperty : mgsyz_CoverProperty (K := K) n S t.card := by
    refine ⟨t, rfl, ?_, htSpan⟩
    intro m hm
    exact mgsyz_cover_homogeneous (K := K) n S m (Finset.erase_subset _ _ hm)
  have hle : mgsyz_minCard (K := K) n S ≤ t.card := by
    change Nat.find (mgsyz_coverProperty_exists (K := K) n S) ≤ t.card
    exact Nat.find_min' (mgsyz_coverProperty_exists (K := K) n S) htProperty
  have hlt : t.card < mgsyz_minCard (K := K) n S := by
    rw [← mgsyz_cover_card (K := K) n S]
    exact Finset.card_erase_lt_of_mem j.2
  exact (not_lt_of_ge hle hlt).elim

end mgsyz_KernelConstantCoeff

section mgsyz_ProjectiveKernel

private def mgsyz_phiToN (K : Type u) [Field K] (n : ℕ) (S : mgsyz_Stage K n) :
    (mgsyz_ι (K := K) n S →₀ MvPolynomial (Fin n) K) →ₗ[MvPolynomial (Fin n) K]
      ↥S.N :=
  (mgsyz_phi (K := K) n S).codRestrict S.N fun x => by
    rw [← mgsyz_phi_range K n S]
    exact (mgsyz_phi (K := K) n S).mem_range_self x

private theorem mgsyz_phiToN_surjective (K : Type u) [Field K] (n : ℕ)
    (S : mgsyz_Stage K n) : Function.Surjective (mgsyz_phiToN K n S) := by
  intro y
  have hy : y.1 ∈ LinearMap.range (mgsyz_phi (K := K) n S) := by
    rw [mgsyz_phi_range K n S]
    exact y.2
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

private theorem mgsyz_phiToN_ker (K : Type u) [Field K] (n : ℕ)
    (S : mgsyz_Stage K n) :
    LinearMap.ker (mgsyz_phiToN K n S) = LinearMap.ker (mgsyz_phi (K := K) n S) := by
  exact LinearMap.ker_codRestrict _ _ _

private theorem mgsyz_ker_eq_bot_of_projective (K : Type u) [Field K] (n : ℕ)
    (S : mgsyz_Stage K n)
    [Module.Projective (MvPolynomial (Fin n) K) ↥S.N] :
    LinearMap.ker (mgsyz_phi (K := K) n S) = ⊥ := by
  classical
  let φ' := mgsyz_phiToN K n S
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property φ' LinearMap.id
    (mgsyz_phiToN_surjective K n S)
  let p : (mgsyz_ι (K := K) n S →₀ MvPolynomial (Fin n) K) →ₗ[
      MvPolynomial (Fin n) K] (mgsyz_ι (K := K) n S →₀ MvPolynomial (Fin n) K) :=
    LinearMap.id - σ.comp φ'
  have hσ_apply (y : ↥S.N) : φ' (σ y) = y := by
    have h := congrArg (fun f => f y) hσ
    simpa using h
  have hpker (x : mgsyz_ι (K := K) n S →₀ MvPolynomial (Fin n) K) :
      p x ∈ LinearMap.ker (mgsyz_phi (K := K) n S) := by
    rw [← mgsyz_phiToN_ker K n S, LinearMap.mem_ker]
    change φ' (x - σ (φ' x)) = 0
    rw [map_sub, hσ_apply]
    exact sub_self _
  have hpfix (x : mgsyz_ι (K := K) n S →₀ MvPolynomial (Fin n) K)
      (hx : x ∈ LinearMap.ker (mgsyz_phi (K := K) n S)) : p x = x := by
    have hx' : x ∈ LinearMap.ker φ' := by
      rw [mgsyz_phiToN_ker K n S]
      exact hx
    have hx0 := LinearMap.mem_ker.mp hx'
    change x - σ (φ' x) = x
    rw [hx0]
    simp
  let I : Ideal (MvPolynomial (Fin n) K) :=
    RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin n) K →+* K)
  have hle : LinearMap.ker (mgsyz_phi (K := K) n S) ≤
      I • LinearMap.ker (mgsyz_phi (K := K) n S) := by
    intro x hx
    have hrepr : (∑ j ∈ x.support,
        x j • Finsupp.single j (1 : MvPolynomial (Fin n) K)) = x := by
      calc
        (∑ j ∈ x.support, x j • Finsupp.single j (1 : MvPolynomial (Fin n) K)) =
            ∑ j ∈ x.support, Finsupp.single j (x j) := by
          apply Finset.sum_congr rfl
          intro j _
          exact Finsupp.smul_single_one j (x j)
        _ = x := Finsupp.sum_single x
    rw [← hpfix x hx, ← hrepr, map_sum]
    simp only [map_smul]
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem_smul
    · rw [RingHom.mem_ker]
      exact mgsyz_ker_constantCoeff K n S x hx j
    · exact hpker (Finsupp.single j 1)
  have hfg : (LinearMap.ker (mgsyz_phi (K := K) n S)).FG :=
    IsNoetherian.noetherian _
  obtain ⟨r, hrI, hrann⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I
      (LinearMap.ker (mgsyz_phi (K := K) n S)) hfg hle
  have hrcc : MvPolynomial.constantCoeff r = 1 := by
    have hrzero := RingHom.mem_ker.mp hrI
    apply sub_eq_zero.mp
    simpa only [map_sub, map_one] using hrzero
  have hrne : r ≠ 0 := by
    intro hr
    rw [hr] at hrcc
    simp at hrcc
  apply le_antisymm ?_ bot_le
  intro x hx
  change x = 0
  apply Finsupp.ext
  intro j
  have hcoord := congrArg (fun y => y j) (hrann x hx)
  change r * x j = 0 at hcoord
  exact (mul_eq_zero.mp hcoord).resolve_left hrne

end mgsyz_ProjectiveKernel

section mgsyz_Stages

private noncomputable def mgsyz_next (K : Type u) [Field K] (n : ℕ)
    (S : mgsyz_Stage K n) : mgsyz_Stage K n := by
  letI : Module K
      (mgsyz_ι (K := K) n S →₀ MvPolynomial (Fin n) K) :=
    Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)
  exact
    { W := mgsyz_ι (K := K) n S →₀ MvPolynomial (Fin n) K
      addCommGroup := inferInstance
      moduleR := inferInstance
      moduleK := Module.compHom _
        (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)
      gW := mgsyz_freeGraded K (mgsyz_delta (K := K) n S)
      N := LinearMap.ker (mgsyz_phi (K := K) n S)
      graded := by
        intro x hx β
        exact @mgsyz_ker_graded K _ n _ _ _ _
          (Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)) _ _ _
          (mgsyz_freeGraded K (mgsyz_delta (K := K) n S)) S.gW
          (mgsyz_phi (K := K) n S) (mgsyz_phi_degreeZero K n S) x hx β
      fg := IsNoetherian.noetherian _ }

private noncomputable def mgsyz_stage0 (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] : mgsyz_Stage K n where
  W := M
  addCommGroup := inferInstance
  moduleR := inferInstance
  moduleK := inferInstance
  gW := targetGraded
  N := ⊤
  graded := by
    intro x hx β
    exact Submodule.mem_top
  fg := Module.Finite.fg_top

private noncomputable def mgsyz_stage (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] : ℕ → mgsyz_Stage K n
  | 0 => mgsyz_stage0 K n M targetGraded
  | k + 1 => mgsyz_next K n (mgsyz_stage K n M targetGraded k)

private abbrev mgsyz_ιk (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] (k : ℕ) : Type u :=
  mgsyz_ι (K := K) n (mgsyz_stage K n M targetGraded k)

private abbrev mgsyz_Fk (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] (k : ℕ) : Type u :=
  mgsyz_ιk K n M targetGraded k →₀ MvPolynomial (Fin n) K

private noncomputable def mgsyz_phik (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] (k : ℕ) :
    mgsyz_Fk K n M targetGraded k →ₗ[MvPolynomial (Fin n) K]
      (mgsyz_stage K n M targetGraded k).W :=
  mgsyz_phi (K := K) n (mgsyz_stage K n M targetGraded k)

private theorem mgsyz_projDim (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] (k : ℕ) (hk : k ≤ n) :
    CategoryTheory.HasProjectiveDimensionLE
      (ModuleCat.of (MvPolynomial (Fin n) K)
        ↥(mgsyz_stage K n M targetGraded k).N) (n - k) := by
  induction k with
  | zero =>
      let : Module.Finite (MvPolynomial (Fin n) K)
          ↥(mgsyz_stage K n M targetGraded 0).N :=
        Module.Finite.of_fg (mgsyz_stage K n M targetGraded 0).fg
      exact
        MathlibExt.RingTheory.Polynomial.HilbertSyzygyWanted.hilbert_syzygy
  | succ k ih =>
      let S := mgsyz_stage K n M targetGraded k
      let φ' := mgsyz_phiToN K n S
      let T := LinearMap.shortComplexKer φ'
      have hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      have hprev := ih hk'
      change CategoryTheory.HasProjectiveDimensionLT
        (ModuleCat.of (MvPolynomial (Fin n) K) ↥S.N) (n - k + 1) at hprev
      have hshort : T.ShortExact :=
        LinearMap.shortExact_shortComplexKer (mgsyz_phiToN_surjective K n S)
      have hfree : CategoryTheory.Projective T.X₂ := by
        exact ModuleCat.projective_of_free Finsupp.basisSingleOne
      have hker : CategoryTheory.HasProjectiveDimensionLT T.X₁
          (n - (k + 1) + 1) := by
        apply (hshort.hasProjectiveDimensionLT_X₃_iff (n - k - 1) hfree).mp
        simpa only [show n - k - 1 + 2 = n - k + 1 by omega] using hprev
      let e : T.X₁ ≅ ModuleCat.of (MvPolynomial (Fin n) K)
          ↥(mgsyz_stage K n M targetGraded (k + 1)).N :=
        (LinearEquiv.ofEq _ _ (by
          simpa [T, φ', S, mgsyz_stage, mgsyz_next] using
            (mgsyz_phiToN_ker K n S))).toModuleIso
      let : CategoryTheory.HasProjectiveDimensionLT T.X₁
          (n - (k + 1) + 1) := hker
      change CategoryTheory.HasProjectiveDimensionLT
        (ModuleCat.of (MvPolynomial (Fin n) K)
          ↥(mgsyz_stage K n M targetGraded (k + 1)).N)
        (n - (k + 1) + 1)
      exact CategoryTheory.hasProjectiveDimensionLT_of_iso e _

private theorem mgsyz_stageN_projective (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] :
    Module.Projective (MvPolynomial (Fin n) K)
      ↥(mgsyz_stage K n M targetGraded n).N := by
  have hdim : CategoryTheory.HasProjectiveDimensionLE
      (ModuleCat.of (MvPolynomial (Fin n) K)
        ↥(mgsyz_stage K n M targetGraded n).N) 0 := by
    simpa using mgsyz_projDim K n M targetGraded n le_rfl
  have hprojective : CategoryTheory.Projective
      (ModuleCat.of (MvPolynomial (Fin n) K)
        ↥(mgsyz_stage K n M targetGraded n).N) :=
    (CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero _).mpr hdim
  exact (IsProjective.iff_projective _).mpr hprojective

private theorem mgsyz_stage_succ_N_eq_bot (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] :
    (mgsyz_stage K n M targetGraded (n + 1)).N = ⊥ := by
  let : Module.Projective (MvPolynomial (Fin n) K)
      ↥(mgsyz_stage K n M targetGraded n).N :=
    mgsyz_stageN_projective K n M targetGraded
  change LinearMap.ker
    (mgsyz_phi (K := K) n (mgsyz_stage K n M targetGraded n)) = ⊥
  exact mgsyz_ker_eq_bot_of_projective K n
    (mgsyz_stage K n M targetGraded n)

private theorem mgsyz_minCard_eq_zero_of_N_eq_bot (K : Type u) [Field K]
    (n : ℕ) (S : mgsyz_Stage K n) (hS : S.N = ⊥) :
    mgsyz_minCard (K := K) n S = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  change Nat.find (mgsyz_coverProperty_exists (K := K) n S) ≤ 0
  apply Nat.find_min' (mgsyz_coverProperty_exists (K := K) n S)
  refine ⟨∅, by simp, ?_, ?_⟩
  · intro m hm
    simp at hm
  · simp [hS]

private theorem mgsyz_cover_eq_empty_of_N_eq_bot (K : Type u) [Field K]
    (n : ℕ) (S : mgsyz_Stage K n) (hS : S.N = ⊥) :
    mgsyz_cover (K := K) n S = ∅ := by
  rw [← Finset.card_eq_zero, mgsyz_cover_card,
    mgsyz_minCard_eq_zero_of_N_eq_bot K n S hS]

private theorem mgsyz_ι_isEmpty_of_N_eq_bot (K : Type u) [Field K]
    (n : ℕ) (S : mgsyz_Stage K n) (hS : S.N = ⊥) :
    IsEmpty (mgsyz_ι (K := K) n S) := by
  constructor
  intro j
  have hne : (mgsyz_cover (K := K) n S).Nonempty := ⟨j.1, j.2⟩
  rw [mgsyz_cover_eq_empty_of_N_eq_bot K n S hS] at hne
  exact Finset.not_nonempty_empty hne

private theorem mgsyz_next_N_eq_bot_of_N_eq_bot (K : Type u) [Field K]
    (n : ℕ) (S : mgsyz_Stage K n) (hS : S.N = ⊥) :
    (mgsyz_next K n S).N = ⊥ := by
  let : IsEmpty (mgsyz_ι (K := K) n S) :=
    mgsyz_ι_isEmpty_of_N_eq_bot K n S hS
  change LinearMap.ker (mgsyz_phi (K := K) n S) = ⊥
  exact Submodule.eq_bot_of_subsingleton

private theorem mgsyz_stage_N_eq_bot_of_succ_le (K : Type u) [Field K]
    (n : ℕ) (M : Type u) [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] (i : ℕ) (hi : n + 1 ≤ i) :
    (mgsyz_stage K n M targetGraded i).N = ⊥ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
  induction d with
  | zero =>
      simpa using mgsyz_stage_succ_N_eq_bot K n M targetGraded
  | succ d ih =>
      rw [Nat.add_succ]
      change (mgsyz_next K n
        (mgsyz_stage K n M targetGraded (n + 1 + d))).N = ⊥
      exact mgsyz_next_N_eq_bot_of_N_eq_bot K n _ (ih (by omega))

private theorem mgsyz_ιk_isEmpty_of_lt (K : Type u) [Field K]
    (n : ℕ) (M : Type u) [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] (i : ℕ) (hi : n < i) :
    IsEmpty (mgsyz_ιk K n M targetGraded i) :=
  mgsyz_ι_isEmpty_of_N_eq_bot K n (mgsyz_stage K n M targetGraded i)
    (mgsyz_stage_N_eq_bot_of_succ_le K n M targetGraded i
      (Nat.succ_le_iff.mpr hi))

private theorem mgsyz_phik_range (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] (k : ℕ) :
    LinearMap.range (mgsyz_phik K n M targetGraded k) =
      (mgsyz_stage K n M targetGraded k).N :=
  mgsyz_phi_range K n (mgsyz_stage K n M targetGraded k)

private theorem mgsyz_phik_comp_succ (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] (k : ℕ) :
    (mgsyz_phik K n M targetGraded (k + 1)).comp
      (mgsyz_phik K n M targetGraded (k + 2)) = 0 := by
  apply LinearMap.ext
  intro x
  have hx : mgsyz_phik K n M targetGraded (k + 2) x ∈
      LinearMap.range (mgsyz_phik K n M targetGraded (k + 2)) :=
    (mgsyz_phik K n M targetGraded (k + 2)).mem_range_self x
  rw [mgsyz_phik_range] at hx
  exact LinearMap.mem_ker.mp hx

private theorem mgsyz_phik_range_eq_ker (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] (k : ℕ) :
    LinearMap.range (mgsyz_phik K n M targetGraded (k + 1)) =
      LinearMap.ker (mgsyz_phik K n M targetGraded k) := by
  rw [mgsyz_phik_range]
  rfl

private theorem mgsyz_phik_zero_surjective (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] :
    Function.Surjective (mgsyz_phik K n M targetGraded 0) := by
  rw [← LinearMap.range_eq_top, mgsyz_phik_range]
  rfl

private noncomputable def mgsyz_d (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] (k : ℕ) :
    mgsyz_Fk K n M targetGraded (k + 1) →ₗ[MvPolynomial (Fin n) K]
      mgsyz_Fk K n M targetGraded k where
  toFun := mgsyz_phik K n M targetGraded (k + 1)
  map_add' := map_add (mgsyz_phik K n M targetGraded (k + 1))
  map_smul' := map_smul (mgsyz_phik K n M targetGraded (k + 1))

private theorem mgsyz_d_apply (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] (k : ℕ)
    (x : mgsyz_Fk K n M targetGraded (k + 1)) :
    mgsyz_d K n M targetGraded k x =
      mgsyz_phi (K := K) n (mgsyz_stage K n M targetGraded (k + 1)) x :=
  rfl

private theorem mgsyz_d_comp_succ (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] (k : ℕ) :
    (mgsyz_d K n M targetGraded k).comp
      (mgsyz_d K n M targetGraded (k + 1)) = 0 := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (mgsyz_phik_comp_succ K n M targetGraded k) x

private theorem mgsyz_d_range_eq_ker (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] (k : ℕ) :
    LinearMap.range (mgsyz_d K n M targetGraded (k + 1)) =
      LinearMap.ker (mgsyz_d K n M targetGraded k) := by
  change LinearMap.range (mgsyz_phik K n M targetGraded (k + 2)) =
    LinearMap.ker (mgsyz_phik K n M targetGraded (k + 1))
  exact mgsyz_phik_range_eq_ker K n M targetGraded (k + 1)

private noncomputable def mgsyz_aug (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] :
    mgsyz_Fk K n M targetGraded 0 →ₗ[MvPolynomial (Fin n) K] M where
  toFun := mgsyz_phik K n M targetGraded 0
  map_add' := map_add (mgsyz_phik K n M targetGraded 0)
  map_smul' := map_smul (mgsyz_phik K n M targetGraded 0)

private theorem mgsyz_aug_surjective (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] :
    Function.Surjective (mgsyz_aug K n M targetGraded) :=
  mgsyz_phik_zero_surjective K n M targetGraded

private theorem mgsyz_aug_comp_d (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] :
    (mgsyz_aug K n M targetGraded).comp (mgsyz_d K n M targetGraded 0) = 0 := by
  apply LinearMap.ext
  intro x
  have hx : mgsyz_phik K n M targetGraded 1 x ∈
      LinearMap.range (mgsyz_phik K n M targetGraded 1) :=
    (mgsyz_phik K n M targetGraded 1).mem_range_self x
  rw [mgsyz_phik_range] at hx
  exact LinearMap.mem_ker.mp hx

private noncomputable def mgsyz_complex (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] :
    ChainComplex (ModuleCat (MvPolynomial (Fin n) K)) ℕ :=
  ChainComplex.of
    (fun k => ModuleCat.of (MvPolynomial (Fin n) K)
      (mgsyz_Fk K n M targetGraded k))
    (fun k => ModuleCat.ofHom (mgsyz_d K n M targetGraded k))
    (fun k => by
      rw [← ModuleCat.ofHom_comp, mgsyz_d_comp_succ,
        ModuleCat.ofHom_zero])

private theorem mgsyz_d_zero_range_eq_aug_ker (K : Type u) [Field K]
    (n : ℕ) (M : Type u) [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] :
    LinearMap.range (mgsyz_d K n M targetGraded 0) =
      LinearMap.ker (mgsyz_aug K n M targetGraded) := by
  change LinearMap.range (mgsyz_phik K n M targetGraded 1) =
    LinearMap.ker (mgsyz_phik K n M targetGraded 0)
  exact mgsyz_phik_range_eq_ker K n M targetGraded 0

set_option backward.isDefEq.respectTransparency false in
private theorem mgsyz_complex_d_comp_aug (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] :
    (mgsyz_complex K n M targetGraded).d 1 0 ≫
      ModuleCat.ofHom (mgsyz_aug K n M targetGraded) = 0 := by
  change ModuleCat.ofHom (mgsyz_d K n M targetGraded 0) ≫
    ModuleCat.ofHom (mgsyz_aug K n M targetGraded) = 0
  rw [← ModuleCat.ofHom_comp,
    mgsyz_aug_comp_d, ModuleCat.ofHom_zero]

private noncomputable def mgsyz_pi (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] :
    mgsyz_complex K n M targetGraded ⟶
      (ChainComplex.single₀ (ModuleCat (MvPolynomial (Fin n) K))).obj
        (ModuleCat.of (MvPolynomial (Fin n) K) M) :=
  (ChainComplex.toSingle₀Equiv (mgsyz_complex K n M targetGraded)
    (ModuleCat.of (MvPolynomial (Fin n) K) M)).symm
      ⟨ModuleCat.ofHom (mgsyz_aug K n M targetGraded),
        mgsyz_complex_d_comp_aug K n M targetGraded⟩

set_option backward.isDefEq.respectTransparency false in
private theorem mgsyz_zero_short_exact (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] :
    (CategoryTheory.ShortComplex.mk
      ((mgsyz_complex K n M targetGraded).d 1 0)
      (ModuleCat.ofHom (mgsyz_aug K n M targetGraded))
      (mgsyz_complex_d_comp_aug K n M targetGraded)).Exact := by
  rw [CategoryTheory.ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range (mgsyz_d K n M targetGraded 0) =
    LinearMap.ker (mgsyz_aug K n M targetGraded)
  exact mgsyz_d_zero_range_eq_aug_ker K n M targetGraded

private theorem mgsyz_aug_epi (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] :
    Epi (ModuleCat.ofHom (mgsyz_aug K n M targetGraded)) := by
  rw [ModuleCat.epi_iff_surjective]
  exact mgsyz_aug_surjective K n M targetGraded

set_option backward.isDefEq.respectTransparency false in
private theorem mgsyz_complex_exactAt_succ (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] (k : ℕ) :
    (mgsyz_complex K n M targetGraded).ExactAt (k + 1) := by
  rw [HomologicalComplex.exactAt_iff'
    (mgsyz_complex K n M targetGraded) (k + 2) (k + 1) k (by simp) (by simp)]
  rw [show k + 2 = (k + 1) + 1 by omega]
  rw [CategoryTheory.ShortComplex.moduleCat_exact_iff_range_eq_ker]
  simpa only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
    mgsyz_complex, ChainComplex.of_d, ModuleCat.hom_ofHom] using
    mgsyz_d_range_eq_ker K n M targetGraded k

set_option backward.isDefEq.respectTransparency false in
private theorem mgsyz_pi_quasiIso (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] :
    QuasiIso (mgsyz_pi K n M targetGraded) := by
  constructor
  intro i
  cases i with
  | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,
        CategoryTheory.ShortComplex.quasiIso_iff_of_zeros']
      · simp only [mgsyz_pi]
        exact ⟨mgsyz_zero_short_exact K n M targetGraded,
          mgsyz_aug_epi K n M targetGraded⟩
      all_goals rfl
  | succ k =>
      rw [quasiIsoAt_iff_exactAt']
      · exact mgsyz_complex_exactAt_succ K n M targetGraded k
      · exact ChainComplex.exactAt_succ_single_obj _ k

private noncomputable def mgsyz_resolution (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] :
    ProjectiveResolution (ModuleCat.of (MvPolynomial (Fin n) K) M) where
  complex := mgsyz_complex K n M targetGraded
  projective _i := ModuleCat.projective_of_free Finsupp.basisSingleOne
  π := mgsyz_pi K n M targetGraded
  quasiIso := mgsyz_pi_quasiIso K n M targetGraded

set_option backward.isDefEq.respectTransparency false in
private noncomputable def mgsyz_multigradedResolution
    (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] :
    MultigradedFreeResolution K n M targetGraded
      (mgsyz_resolution K n M targetGraded)
      (mgsyz_ιk K n M targetGraded) where
  termFree i := by
    letI : Module K (mgsyz_Fk K n M targetGraded i) :=
      Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)
    simpa only [mgsyz_resolution, mgsyz_complex, ChainComplex.of_X] using
      (mgsyz_freeModule K
        (mgsyz_delta (K := K) n (mgsyz_stage K n M targetGraded i)))
  diffDegreeZero i := by
    let : Module K (mgsyz_Fk K n M targetGraded (i + 1)) :=
      Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)
    let : Module K (mgsyz_Fk K n M targetGraded i) :=
      Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)
    intro α m hm
    simpa only [mgsyz_resolution, mgsyz_complex, ChainComplex.of_d,
      ModuleCat.hom_ofHom, mgsyz_d_apply, mgsyz_stage, mgsyz_next,
      mgsyz_freeModule, id_eq] using
      (mgsyz_phi_degreeZero K n
        (mgsyz_stage K n M targetGraded (i + 1)) α m hm)
  augDegreeZero := by
    let : Module K (mgsyz_Fk K n M targetGraded 0) :=
      Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)
    intro α m hm
    simp only [mgsyz_resolution, mgsyz_pi,
      ChainComplex.toSingle₀Equiv_symm_apply_f_zero, ModuleCat.hom_ofHom]
    change mgsyz_phi (K := K) n
      (mgsyz_stage K n M targetGraded 0) m ∈ targetGraded.component α
    exact mgsyz_phi_degreeZero K n
      (mgsyz_stage K n M targetGraded 0) α m hm

end mgsyz_Stages

/-- **Existence of finite multigraded free resolutions.** Let $K$ be a field, let
$R = K[x_1, \dots, x_n]$, and let $M$ be a multigraded $R$-module that is finitely generated over
$R$. Then there are a projective resolution $P_\bullet \to M$ over $R$, index types $\iota_i$ for
$i \in \mathbb{N}$, a multigraded free resolution structure on $P_\bullet$ for the given grading
of $M$ in which $P_i$ has basis indexed by $\iota_i$, and a number $b \in \mathbb{N}$ such that
every $\iota_i$ is finite and $\iota_i$ is empty for every $i > b$.

The proof uses stagewise minimal homogeneous free covers, the determinant trick,
dimension shifting, and Hilbert's syzygy theorem.

Proves `Wanted` entry `exists_finite_multigraded_free_resolution`.

Source: Hoffman–Wang,
https://export.arxiv.org/e-print/math/0601101v1 lines 592-612 (finite free
graded resolution). The Braun–Davis JIS passage
https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex lines 856-876
supplies the motivating Hilbert-syzygy / Poincaré-series context only. No
`≤ n` bound is claimed here.
-/
public theorem exists_finite_multigraded_free_resolution
    (K : Type u) (n : ℕ) (M : Type u)
    [Field K] [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] :
    ∃ (resolution : CategoryTheory.ProjectiveResolution
        (ModuleCat.of (MvPolynomial (Fin n) K) M))
      (ι : ℕ → Type u)
      (res : MultigradedFreeResolution K n M targetGraded resolution ι)
      (bound : ℕ),
      (∀ i, Finite (ι i)) ∧ ∀ i, bound < i → IsEmpty (ι i) := by
  refine ⟨mgsyz_resolution K n M targetGraded,
    mgsyz_ιk K n M targetGraded,
    mgsyz_multigradedResolution K n M targetGraded, n, ?_, ?_⟩
  · intro i
    infer_instance
  · intro i hi
    exact mgsyz_ιk_isEmpty_of_lt K n M targetGraded i hi

end

end MetaMathlibExt
