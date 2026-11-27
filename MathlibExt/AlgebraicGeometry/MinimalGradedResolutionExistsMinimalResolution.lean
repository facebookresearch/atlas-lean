/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RingTheory.MinimalGradedResolution

import MathlibExt.RingTheory.Polynomial.HilbertSyzygy
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Nakayama
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.GroupWithZero.Action.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Existence of minimal graded resolutions over polynomial rings

Every finitely generated graded module over a polynomial ring over a field
admits a minimal graded free resolution of length at most the number of
variables, with actual finite free modules, kernel/range exactness and
differential image in the irrelevant ideal times the target.

References:
* Eisenbud, *Commutative Algebra with a View Toward Algebraic Geometry*, GTM 150,
  Chapter 1 (Hilbert's syzygy theorem), Chapter 19 (minimal resolutions and projective
  dimension) and Chapter 20 (free resolutions), https://doi.org/10.1007/978-1-4612-5350-1.
* Adapted from `MathlibExt/RingTheory/GradedAlgebra/MultigradedHilbertSyzygy.lean` in this
  repository: the cover and kernel proofs (`emr_exists_homogeneous_span` through
  `emr_ker_eq_bot_of_projective`) follow its `mgsyz_` proofs, adapted from multidegrees and
  finitely supported vectors to integer degrees and finite tuples.
* Background only, not adapted here: AxiomMath/Stacks at
  c496df0d9beea9deaeabcea8492605f9a0a2313b,
  `StacksFrontier/AlgebraicGeometry/ResolutionsAndBounds/LocalSyzygy.lean`, a local free-cover
  step for coherent sheaves.
-/

noncomputable section

namespace WantedExt.AlgebraicGeometry.MinimalGradedResolutionWanted

open MathlibExt.RingTheory.MinimalGradedResolution

private theorem emr_weight_one_eq_zero_iff {n : ℕ} (d : Fin n →₀ ℕ) :
    Finsupp.weight (fun _ : Fin n ↦ (1 : ℤ)) d = 0 ↔ d = 0 := by
  constructor
  · intro h
    rw [Finsupp.weight_eq_sum] at h
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin n)), (0 : ℤ) ≤ (d i : ℕ) • (1 : ℤ) := by
      intro i _
      have hsm : ((d i : ℕ) • (1 : ℤ)) = ((d i : ℕ) : ℤ) := by simp
      rw [hsm]
      exact Int.natCast_nonneg _
    rw [Finset.sum_eq_zero_iff_of_nonneg hnn] at h
    ext i
    have hi := h i (Finset.mem_univ i)
    have hii : ((d i : ℕ) : ℤ) = 0 := by simpa using hi
    exact Nat.cast_eq_zero.mp hii
  · intro h
    rw [h]
    exact map_zero _

private theorem emr_mem_freePiece {k : Type*} [Field k] {n b : ℕ} (δ : Fin b → ℤ) (j : ℤ)
    (f : Fin b → PolynomialRing k n) :
    f ∈ freePiece (k := k) (n := n) δ j ↔
      ∀ i, f i ∈ polynomialPiece (k := k) (n := n) (j - δ i) := Iff.rfl

private theorem emr_mem_polynomialPiece {k : Type*} [Field k] {n : ℕ} (j : ℤ)
    (p : PolynomialRing k n) :
    p ∈ polynomialPiece (k := k) (n := n) j ↔
      MvPolynomial.IsWeightedHomogeneous (fun _ : Fin n ↦ (1 : ℤ)) p j := by
  simp only [polynomialPiece, MvPolynomial.mem_weightedHomogeneousSubmodule]

private theorem emr_irrelevant_eq {k : Type*} [Field k] {n : ℕ} :
    irrelevant (k := k) (n := n) = MvPolynomial.idealOfVars (Fin n) k := rfl

private theorem emr_constantCoeff_mem_irrelevant {k : Type*} [Field k] {n : ℕ}
    (p : PolynomialRing k n) (h : MvPolynomial.constantCoeff p = 0) :
    p ∈ irrelevant (k := k) (n := n) := by
  rw [emr_irrelevant_eq]
  have h1 : MvPolynomial.idealOfVars (Fin n) k
      = MvPolynomial.idealOfVars (Fin n) k ^ 1 := by rw [pow_one]
  rw [h1, MvPolynomial.mem_pow_idealOfVars_iff']
  intro x hx
  have hx0 : x = 0 := by
    have hdeg : Finsupp.degree x = 0 := by omega
    exact (Finsupp.degree_eq_zero_iff x).mp hdeg
  rw [hx0, ← MvPolynomial.constantCoeff_eq]
  exact h

private noncomputable def emr_freePart {k : Type*} [Field k] {n b : ℕ} (δ : Fin b → ℤ)
    (β : ℤ) (f : Fin b → PolynomialRing k n) : Fin b → PolynomialRing k n :=
  fun i => MvPolynomial.weightedHomogeneousComponent (fun _ : Fin n ↦ (1 : ℤ)) (β - δ i) (f i)

private theorem emr_freePart_mem {k : Type*} [Field k] {n b : ℕ} (δ : Fin b → ℤ) (β : ℤ)
    (f : Fin b → PolynomialRing k n) :
    emr_freePart (k := k) δ β f ∈ freePiece (k := k) (n := n) δ β := by
  rw [emr_mem_freePiece]
  intro i
  exact MvPolynomial.weightedHomogeneousComponent_mem _ _ _

private def emr_freeSupport {k : Type*} [Field k] {n b : ℕ} (δ : Fin b → ℤ)
    (f : Fin b → PolynomialRing k n) : Finset ℤ :=
  Finset.univ.biUnion fun i =>
    Finset.image (fun d => d + δ i)
      (Finset.image (Finsupp.weight (fun _ : Fin n ↦ (1 : ℤ))) (f i).support)

private theorem emr_freePart_eq_zero_of_notMem {k : Type*} [Field k] {n b : ℕ} (δ : Fin b → ℤ)
    (f : Fin b → PolynomialRing k n) (β : ℤ) (hβ : β ∉ emr_freeSupport (k := k) δ f) :
    emr_freePart (k := k) δ β f = 0 := by
  funext i
  change MvPolynomial.weightedHomogeneousComponent _ _ _ = 0
  apply MvPolynomial.weightedHomogeneousComponent_eq_zero' _ _ _
  intro d hd hcon
  apply hβ
  rw [emr_freeSupport, Finset.mem_biUnion]
  refine ⟨i, Finset.mem_univ i,
    Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr ⟨d, hd, rfl⟩, by omega⟩⟩

private theorem emr_freeReconstruct {k : Type*} [Field k] {n b : ℕ} (δ : Fin b → ℤ)
    (f : Fin b → PolynomialRing k n) :
    (∑ β ∈ emr_freeSupport (k := k) δ f, emr_freePart (k := k) δ β f) = f := by
  funext i
  rw [Finset.sum_apply]
  simp only [emr_freePart]
  have hsup : Function.support
        (fun β => MvPolynomial.weightedHomogeneousComponent (fun _ : Fin n ↦ (1 : ℤ)) (β - δ i)
          (f i)) ⊆ ↑(emr_freeSupport (k := k) δ f) := by
    intro β hβ
    by_contra hcon
    simp only [Finset.mem_coe] at hcon
    have h0 := emr_freePart_eq_zero_of_notMem (k := k) δ f β hcon
    have h0i := congrFun h0 i
    simp only [emr_freePart] at h0i
    exact Function.mem_support.mp hβ h0i
  rw [(finsum_eq_sum_of_support_subset _ hsup).symm]
  have hre := finsum_comp_equiv (f := fun d =>
      MvPolynomial.weightedHomogeneousComponent (fun _ : Fin n ↦ (1 : ℤ)) d (f i))
    (Equiv.subRight (δ i))
  simp only [Equiv.subRight_apply] at hre
  rw [hre]
  exact MvPolynomial.sum_weightedHomogeneousComponent _ (f i)

private theorem emr_freePiece_coe_injective {k : Type*} [Field k] {n b : ℕ} (δ : Fin b → ℤ)
    (x : DirectSum ℤ fun β => ↥(freePiece (k := k) (n := n) δ β))
    (hx : DirectSum.coeAddMonoidHom (freePiece (k := k) (n := n) δ) x = 0) :
    x = 0 := by
  classical
  rw [DirectSum.coeAddMonoidHom_eq_dfinsuppSum] at hx
  have hxsum : (∑ β ∈ x.support,
      ((x β : ↥(freePiece (k := k) (n := n) δ β)) : Fin b → PolynomialRing k n)) = 0 := hx
  have hcoord : ∀ (β : ℤ) (i : Fin b),
      ((x β : ↥(freePiece (k := k) (n := n) δ β)) : Fin b → PolynomialRing k n) i = 0 := by
    intro β i
    have hii : (∑ γ ∈ x.support,
        ((x γ : ↥(freePiece (k := k) (n := n) δ γ)) : Fin b → PolynomialRing k n) i) = 0 := by
      have h2 := congrFun hxsum i
      simpa [Finset.sum_apply] using h2
    have hcomp := congrArg (fun p => MvPolynomial.weightedHomogeneousComponent
      (fun _ : Fin n ↦ (1 : ℤ)) (β - δ i) p) hii
    simp only [map_sum, map_zero] at hcomp
    have hterm : ∀ γ ∈ x.support,
        MvPolynomial.weightedHomogeneousComponent (fun _ : Fin n ↦ (1 : ℤ)) (β - δ i)
          (((x γ : ↥(freePiece (k := k) (n := n) δ γ)) : Fin b → PolynomialRing k n) i)
        = if γ = β then
          ((x γ : ↥(freePiece (k := k) (n := n) δ γ)) : Fin b → PolynomialRing k n) i else 0 := by
      intro γ _
      have hmem : (((x γ : ↥(freePiece (k := k) (n := n) δ γ)) : Fin b → PolynomialRing k n) i)
          ∈ MvPolynomial.weightedHomogeneousSubmodule k (fun _ : Fin n ↦ (1 : ℤ)) (γ - δ i) := by
        have hγ := (x γ).property
        rw [emr_mem_freePiece] at hγ
        exact hγ i
      rw [MvPolynomial.weightedHomogeneousComponent_of_mem hmem]
      have hcond : ((β - δ i) = (γ - δ i)) ↔ (γ = β) := by
        constructor <;> intro h <;> omega
      simp only [hcond]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq'] at hcomp
    split_ifs at hcomp with hβs
    · exact hcomp
    · have hxβ : x β = 0 := DFinsupp.notMem_support_iff.mp hβs
      have hci := congrArg (fun y : ↥(freePiece (k := k) (n := n) δ β) =>
        ((y : Fin b → PolynomialRing k n) i)) hxβ
      simpa using hci
  apply DFinsupp.ext
  intro β
  rw [DFinsupp.zero_apply]
  apply Subtype.ext
  funext i
  exact hcoord β i

private theorem emr_freePiece_isInternal {k : Type*} [Field k] {n b : ℕ} (δ : Fin b → ℤ) :
    DirectSum.IsInternal (freePiece (k := k) (n := n) δ) := by
  constructor
  · intro x y hxy
    have h0 : x - y = 0 := by
      apply emr_freePiece_coe_injective δ
      rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp h0
  · intro f
    refine ⟨∑ β ∈ emr_freeSupport (k := k) δ f,
      DirectSum.of _ β (⟨emr_freePart (k := k) δ β f, emr_freePart_mem _ _ _⟩ :
        ↥(freePiece (k := k) (n := n) δ β)), ?_⟩
    rw [map_sum]
    simp only [DirectSum.coeAddMonoidHom_of]
    exact emr_freeReconstruct δ f

private structure emr_PreGrading (k : Type*) [Field k] (n : ℕ) (W : Type*) [AddCommGroup W]
    [Module (PolynomialRing k n) W] [Module k W] where
  piece : ℤ → Submodule k W
  part : ℤ → W → W
  part_mem : ∀ (β : ℤ) (x : W), part β x ∈ piece β
  supp : W → Finset ℤ
  reconstruct : ∀ x, (∑ β ∈ supp x, part β x) = x
  vanish : ∀ x β, β ∉ supp x → part β x = 0
  decomp : DirectSum.Decomposition piece
  smul_mem : ∀ a b, ∀ p ∈ polynomialPiece (k := k) (n := n) a,
    ∀ m ∈ piece b, p • m ∈ piece (a + b)

open scoped Classical in
private noncomputable def emr_preGradingOfGrading {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M] [Module k M]
    [IsScalarTower k (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) : emr_PreGrading k n M :=
  letI _decomp : DirectSum.Decomposition G.piece :=
    DirectSum.IsInternal.chooseDecomposition G.piece G.isInternal
  { piece := G.piece
    part β x := (((DirectSum.decompose G.piece x) β : G.piece β) : M)
    part_mem β x := ((DirectSum.decompose G.piece x) β).property
    supp x := (DirectSum.decompose G.piece x).support
    reconstruct x := DirectSum.sum_support_decompose G.piece x
    vanish x β hβ := by
      show ((((DirectSum.decompose G.piece x) β : G.piece β) : M)) = 0
      rw [DFinsupp.notMem_support_iff.mp hβ]
      rfl
    decomp := _decomp
    smul_mem := G.smul_mem }

private noncomputable def emr_freePreGrading {k : Type*} [Field k] {n b : ℕ} (δ : Fin b → ℤ) :
    emr_PreGrading k n (Fin b → PolynomialRing k n) where
  piece := freePiece (k := k) (n := n) δ
  part := emr_freePart (k := k) δ
  part_mem := emr_freePart_mem (k := k) δ
  supp := emr_freeSupport (k := k) δ
  reconstruct := emr_freeReconstruct (k := k) δ
  vanish := emr_freePart_eq_zero_of_notMem (k := k) δ
  decomp := DirectSum.IsInternal.chooseDecomposition _ (emr_freePiece_isInternal (k := k) δ)
  smul_mem a b p hp f hf := by
    rw [emr_mem_freePiece]
    intro i
    have hfi := (emr_mem_freePiece (k := k) δ b f).mp hf i
    have hdeg : a + (b - δ i) = a + b - δ i := by omega
    rw [← hdeg]
    exact MvPolynomial.IsWeightedHomogeneous.mul hp hfi

private structure emr_StageData (k : Type*) [Field k] (n : ℕ) (W : Type*) [AddCommGroup W]
    [Module (PolynomialRing k n) W] [Module k W] where
  gW : emr_PreGrading k n W
  N : Submodule (PolynomialRing k n) W
  graded : ∀ x ∈ N, ∀ β, gW.part β x ∈ N
  fg : N.FG

private theorem emr_exists_homogeneous_span {k : Type*} [Field k] {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module (PolynomialRing k n) W] [Module k W]
    (gW : emr_PreGrading k n W) (N : Submodule (PolynomialRing k n) W)
    (graded : ∀ x ∈ N, ∀ β, gW.part β x ∈ N) (fg : N.FG) :
    ∃ s : Finset W,
      (∀ m ∈ s, ∃ α : ℤ, m ∈ gW.piece α) ∧
      Submodule.span (PolynomialRing k n) (s : Set W) = N := by
  classical
  obtain ⟨genCount, genFun, genSpan⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp fg
  let s : Finset W := Finset.univ.biUnion fun genIdx =>
    (gW.supp (genFun genIdx)).image (fun deg => gW.part deg (genFun genIdx))
  refine ⟨s, ?_, le_antisymm ?_ ?_⟩
  · intro homElem homMem
    rw [Finset.mem_biUnion] at homMem
    obtain ⟨genIdx, _, imageMem⟩ := homMem
    rw [Finset.mem_image] at imageMem
    obtain ⟨deg, _, rfl⟩ := imageMem
    exact ⟨deg, gW.part_mem deg _⟩
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
        ∑ deg ∈ gW.supp (genFun genIdx), gW.part deg (genFun genIdx) :=
      (gW.reconstruct (genFun genIdx)).symm
    rw [recon]
    apply Submodule.sum_mem
    intro deg degMem
    apply Submodule.subset_span
    rw [Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨genIdx, Finset.mem_univ genIdx, Finset.mem_image.mpr ⟨deg, degMem, rfl⟩⟩

private noncomputable def emr_CoverProperty {k : Type*} [Field k] {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module (PolynomialRing k n) W] [Module k W]
    (S : emr_StageData k n W) (r : ℕ) : Prop :=
  ∃ s : Finset W, s.card = r ∧ (∀ m ∈ s, ∃ α : ℤ, m ∈ S.gW.piece α) ∧
    Submodule.span (PolynomialRing k n) (s : Set W) = S.N

private theorem emr_coverProperty_exists {k : Type*} [Field k] {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module (PolynomialRing k n) W] [Module k W]
    (S : emr_StageData k n W) : ∃ r, emr_CoverProperty S r := by
  obtain ⟨s, hhom, hspan⟩ :=
    emr_exists_homogeneous_span S.gW S.N S.graded S.fg
  exact ⟨s.card, s, rfl, hhom, hspan⟩

open scoped Classical in
private noncomputable def emr_minCard {k : Type*} [Field k] {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module (PolynomialRing k n) W] [Module k W]
    (S : emr_StageData k n W) : ℕ :=
  Nat.find (emr_coverProperty_exists S)

private theorem emr_minCard_spec {k : Type*} [Field k] {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module (PolynomialRing k n) W] [Module k W]
    (S : emr_StageData k n W) : emr_CoverProperty S (emr_minCard S) := by
  classical
  exact Nat.find_spec (emr_coverProperty_exists S)

private noncomputable def emr_cover {k : Type*} [Field k] {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module (PolynomialRing k n) W] [Module k W]
    (S : emr_StageData k n W) : Finset W :=
  Classical.choose (emr_minCard_spec S)

private theorem emr_cover_spec {k : Type*} [Field k] {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module (PolynomialRing k n) W] [Module k W]
    (S : emr_StageData k n W) :
    (emr_cover S).card = emr_minCard S ∧
      (∀ m ∈ emr_cover S, ∃ α : ℤ, m ∈ S.gW.piece α) ∧
      Submodule.span (PolynomialRing k n) (emr_cover S : Set W) = S.N :=
  Classical.choose_spec (emr_minCard_spec S)

private theorem emr_cover_card {k : Type*} [Field k] {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module (PolynomialRing k n) W] [Module k W]
    (S : emr_StageData k n W) : (emr_cover S).card = emr_minCard S :=
  (emr_cover_spec S).1

private theorem emr_cover_homogeneous {k : Type*} [Field k] {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module (PolynomialRing k n) W] [Module k W]
    (S : emr_StageData k n W) (m : W) (hm : m ∈ emr_cover S) :
    ∃ α : ℤ, m ∈ S.gW.piece α :=
  (emr_cover_spec S).2.1 m hm

private theorem emr_cover_span {k : Type*} [Field k] {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module (PolynomialRing k n) W] [Module k W]
    (S : emr_StageData k n W) :
    Submodule.span (PolynomialRing k n) (emr_cover S : Set W) = S.N :=
  (emr_cover_spec S).2.2

private noncomputable def emr_rank {k : Type*} [Field k] {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module (PolynomialRing k n) W] [Module k W]
    (S : emr_StageData k n W) : ℕ :=
  (emr_cover S).card

private noncomputable def emr_gen {k : Type*} [Field k] {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module (PolynomialRing k n) W] [Module k W]
    (S : emr_StageData k n W) : Fin (emr_rank S) → W :=
  fun j => ((Finset.equivFin (emr_cover S)).symm j).val

private noncomputable def emr_shift {k : Type*} [Field k] {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module (PolynomialRing k n) W] [Module k W]
    (S : emr_StageData k n W) : Fin (emr_rank S) → ℤ :=
  fun j => Classical.choose (emr_cover_homogeneous S _
    (((Finset.equivFin (emr_cover S)).symm j).property))

private theorem emr_shift_mem {k : Type*} [Field k] {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module (PolynomialRing k n) W] [Module k W]
    (S : emr_StageData k n W) (j : Fin (emr_rank S)) :
    emr_gen S j ∈ S.gW.piece (emr_shift S j) :=
  Classical.choose_spec (emr_cover_homogeneous S
    (((Finset.equivFin (emr_cover S)).symm j).val)
    (((Finset.equivFin (emr_cover S)).symm j).property))

private noncomputable def emr_phi {k : Type*} [Field k] {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module (PolynomialRing k n) W] [Module k W]
    (S : emr_StageData k n W) :
    (Fin (emr_rank S) → PolynomialRing k n) →ₗ[PolynomialRing k n] W where
  toFun f := ∑ j, (f j) • (emr_gen S j)
  map_add' f g := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul]
    have h := map_sum (DistribSMul.toLinearMap (PolynomialRing k n) W c)
      (fun j => (f j) • emr_gen S j) Finset.univ
    simpa only [DistribSMul.toLinearMap_apply, RingHom.id_apply] using h.symm

private theorem emr_phi_range {k : Type*} [Field k] {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module (PolynomialRing k n) W] [Module k W]
    (S : emr_StageData k n W) : LinearMap.range (emr_phi S) = S.N := by
  classical
  have hset : Set.range (emr_gen S) = ↑(emr_cover S) := by
    ext m
    constructor
    · rintro ⟨j, rfl⟩
      exact ((Finset.equivFin (emr_cover S)).symm j).property
    · intro hm
      exact ⟨(Finset.equivFin (emr_cover S)) ⟨m, hm⟩, by simp [emr_gen]⟩
  have hspan : Submodule.span (PolynomialRing k n) (Set.range (emr_gen S)) = S.N := by
    rw [hset]
    exact emr_cover_span S
  apply le_antisymm
  · intro y hy
    obtain ⟨f, rfl⟩ := hy
    rw [← hspan]
    change (∑ j, ((f j) • emr_gen S j)) ∈
      Submodule.span (PolynomialRing k n) (Set.range (emr_gen S))
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))
  · rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    have hsingle : emr_phi S (Pi.single j (1 : PolynomialRing k n) :
        Fin (emr_rank S) → PolynomialRing k n) = emr_gen S j := by
      change (∑ l, ((Pi.single j (1 : PolynomialRing k n) :
        Fin (emr_rank S) → PolynomialRing k n) l) • emr_gen S l) = _
      have h0 : ∀ l ∈ (Finset.univ : Finset (Fin (emr_rank S))), l ≠ j →
          ((Pi.single j (1 : PolynomialRing k n) :
            Fin (emr_rank S) → PolynomialRing k n) l) • emr_gen S l = 0 := by
        intro l _ hlj
        simp [Pi.single_eq_of_ne hlj]
      have h1 : j ∉ (Finset.univ : Finset (Fin (emr_rank S))) →
          ((Pi.single j (1 : PolynomialRing k n) :
            Fin (emr_rank S) → PolynomialRing k n) j) • emr_gen S j = 0 :=
        fun hj => absurd (Finset.mem_univ j) hj
      rw [Finset.sum_eq_single j h0 h1]
      simp [Pi.single_eq_same]
    exact ⟨(Pi.single j (1 : PolynomialRing k n) :
      Fin (emr_rank S) → PolynomialRing k n), hsingle⟩

private theorem emr_phi_graded {k : Type*} [Field k] {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module (PolynomialRing k n) W] [Module k W]
    (S : emr_StageData k n W) :
    ∀ (β : ℤ) (f) (_ : f ∈ freePiece (k := k) (n := n) (emr_shift S) β),
      emr_phi S f ∈ S.gW.piece β := by
  intro β f hf
  rw [emr_mem_freePiece] at hf
  change (∑ j, ((f j) • emr_gen S j)) ∈ S.gW.piece β
  apply Submodule.sum_mem
  intro j _
  have hfij : f j ∈ polynomialPiece (k := k) (n := n) (β - emr_shift S j) := hf j
  have hgj := emr_shift_mem S j
  have hmem := S.gW.smul_mem _ _ (f j) hfij (emr_gen S j) hgj
  rwa [sub_add_cancel] at hmem

private theorem emr_ker_graded {k : Type*} [Field k] {n b : ℕ} {W : Type*}
    [AddCommGroup W] [Module (PolynomialRing k n) W] [Module k W]
    (δ : Fin b → ℤ) (gW : emr_PreGrading k n W)
    (φ : (Fin b → PolynomialRing k n) →ₗ[PolynomialRing k n] W)
    (hφ : ∀ (β : ℤ) (f) (_ : f ∈ freePiece (k := k) (n := n) δ β), φ f ∈ gW.piece β)
    (q : Fin b → PolynomialRing k n) (hq : q ∈ LinearMap.ker φ) (β : ℤ) :
    emr_freePart (k := k) δ β q ∈ LinearMap.ker φ := by
  classical
  let this := gW.decomp
  rw [LinearMap.mem_ker]
  have hpartmem : ∀ γ, φ (emr_freePart (k := k) δ γ q) ∈ gW.piece γ := fun γ =>
    hφ γ _ (emr_freePart_mem (k := k) δ γ q)
  have hsumW : (∑ γ ∈ emr_freeSupport (k := k) δ q,
      φ (emr_freePart (k := k) δ γ q)) = 0 := by
    rw [← map_sum, emr_freeReconstruct (k := k) δ q]
    exact LinearMap.mem_ker.mp hq
  have hdec := congrArg (DirectSum.decompose gW.piece) hsumW
  rw [DirectSum.decompose_sum, DirectSum.decompose_zero] at hdec
  have hβeq := congrArg (fun z => ((z β : gW.piece β) : W)) hdec
  rw [DFinsupp.finsetSum_apply] at hβeq
  by_cases hβs : β ∈ emr_freeSupport (k := k) δ q
  · have hoff : ∀ γ ∈ emr_freeSupport (k := k) δ q, γ ≠ β →
        (DirectSum.decompose gW.piece (φ (emr_freePart (k := k) δ γ q))) β = 0 := by
      intro γ hγ hγβ
      apply Subtype.ext
      apply DirectSum.decompose_of_mem_ne gW.piece
      · exact hpartmem γ
      · exact hγβ
    have hsingle := Finset.sum_eq_single β hoff (fun h => (h hβs).elim)
    rw [hsingle] at hβeq
    exact (DirectSum.decompose_of_mem_same gW.piece (hpartmem β)).symm.trans hβeq
  · have hzero : emr_freePart (k := k) δ β q = 0 :=
      emr_freePart_eq_zero_of_notMem (k := k) δ q β hβs
    rw [hzero, map_zero]

private theorem emr_ker_constantCoeff {k : Type*} [Field k] {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module (PolynomialRing k n) W] [Module k W]
    (S : emr_StageData k n W)
    (q : Fin (emr_rank S) → PolynomialRing k n)
    (hq : q ∈ LinearMap.ker (emr_phi S)) (j : Fin (emr_rank S)) :
    MvPolynomial.constantCoeff (q j) = 0 := by
  classical
  by_contra hconstant
  let q' : Fin (emr_rank S) → PolynomialRing k n :=
    emr_freePart (k := k) (emr_shift S) (emr_shift S j) q
  have hq'ker : q' ∈ LinearMap.ker (emr_phi S) :=
    emr_ker_graded (k := k) (emr_shift S) S.gW (emr_phi S) (emr_phi_graded S) q hq _
  have hq'mem : q' ∈ freePiece (k := k) (n := n) (emr_shift S) (emr_shift S j) :=
    emr_freePart_mem (k := k) (emr_shift S) (emr_shift S j) q
  have hq'j : q' j = MvPolynomial.weightedHomogeneousComponent (fun _ : Fin n ↦ (1 : ℤ))
      ((emr_shift S j) - emr_shift S j) (q j) := rfl
  have hβ0 : (emr_shift S j) - emr_shift S j = 0 := sub_self _
  have hcoeff : (q' j).coeff 0 = (q j).coeff 0 := by
    have hw0 : Finsupp.weight (fun _ : Fin n ↦ (1 : ℤ)) (0 : Fin n →₀ ℕ) = 0 := map_zero _
    simp [hq'j, MvPolynomial.coeff_weightedHomogeneousComponent, hw0]
  have hcoeff_ne : (q' j).coeff 0 ≠ 0 := by
    rw [hcoeff]
    simpa [MvPolynomial.constantCoeff_eq] using hconstant
  have hmem_j : (q' j) ∈ polynomialPiece (k := k) (n := n) ((emr_shift S j) - emr_shift S j) :=
    (emr_mem_freePiece (k := k) (emr_shift S) (emr_shift S j) _).mp hq'mem j
  have hsupport : (q' j).support = {0} := by
    ext a
    constructor
    · intro ha
      have hne : (q' j).coeff a ≠ 0 := MvPolynomial.mem_support_iff.mp ha
      have hw := (emr_mem_polynomialPiece _ _).mp hmem_j hne
      rw [hβ0] at hw
      have ha0 := (emr_weight_one_eq_zero_iff a).mp hw
      simp [ha0]
    · intro ha
      have ha0 : a = 0 := by simpa using ha
      subst ha0
      exact MvPolynomial.mem_support_iff.mpr hcoeff_ne
  have hpolynomial : q' j = MvPolynomial.C ((q' j).coeff 0) := by
    calc
      q' j = ∑ a ∈ (q' j).support,
          MvPolynomial.monomial a ((q' j).coeff a) := MvPolynomial.as_sum (q' j)
      _ = MvPolynomial.C ((q' j).coeff 0) := by
        rw [hsupport]
        simp [MvPolynomial.monomial_zero']
  have hkernelEq : emr_phi S q' = 0 := LinearMap.mem_ker.mp hq'ker
  have hsplit : (q' j) • emr_gen S j + ∑ l ∈ (Finset.univ.erase j), (q' l) • emr_gen S l = 0 := by
    have h := Finset.add_sum_erase Finset.univ (fun l => (q' l) • emr_gen S l)
      (Finset.mem_univ j)
    have hphi0 : (∑ l, (q' l) • emr_gen S l) = 0 := hkernelEq
    rwa [hphi0] at h
  rw [hpolynomial] at hsplit
  have hsolve : (MvPolynomial.C ((q' j).coeff 0) : PolynomialRing k n) • emr_gen S j =
      -(∑ l ∈ (Finset.univ.erase j), (q' l) • emr_gen S l) :=
    eq_neg_of_add_eq_zero_left hsplit
  let t := (emr_cover S).erase (emr_gen S j)
  have hgen_mem : emr_gen S j ∈ emr_cover S :=
    ((Finset.equivFin (emr_cover S)).symm j).property
  have hsumSpan : (∑ l ∈ (Finset.univ.erase j), (q' l) • emr_gen S l) ∈
      Submodule.span (PolynomialRing k n) (t : Set W) := by
    apply Submodule.sum_mem
    intro l hl
    apply Submodule.smul_mem
    apply Submodule.subset_span
    rw [Finset.mem_coe, Finset.mem_erase]
    have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
    refine ⟨?_, ?_⟩
    · intro hcon
      apply hlj
      have hval : (((Finset.equivFin (emr_cover S)).symm l).val) =
          (((Finset.equivFin (emr_cover S)).symm j).val) := hcon
      have hsub := Subtype.ext hval
      exact (Finset.equivFin (emr_cover S)).symm.injective hsub
    · exact ((Finset.equivFin (emr_cover S)).symm l).property
  have hCcj : (MvPolynomial.C ((q' j).coeff 0) : PolynomialRing k n) • emr_gen S j ∈
      Submodule.span (PolynomialRing k n) (t : Set W) := by
    rw [hsolve]
    exact Submodule.neg_mem _ hsumSpan
  have hc : (q' j).coeff 0 ≠ 0 := hcoeff_ne
  have hjSpan : emr_gen S j ∈ Submodule.span (PolynomialRing k n) (t : Set W) := by
    have hscaled := (Submodule.span (PolynomialRing k n) (t : Set W)).smul_mem
      (MvPolynomial.C ((q' j).coeff 0)⁻¹ : PolynomialRing k n) hCcj
    have hC : (MvPolynomial.C ((q' j).coeff 0)⁻¹ : PolynomialRing k n)
        * MvPolynomial.C ((q' j).coeff 0) = 1 := by
      rw [← MvPolynomial.C_mul]
      simp [hc]
    simpa only [smul_smul, hC, one_smul] using hscaled
  have htSpan : Submodule.span (PolynomialRing k n) (t : Set W) = S.N := by
    calc
      Submodule.span (PolynomialRing k n) (t : Set W) =
          Submodule.span (PolynomialRing k n) (insert (emr_gen S j) (t : Set W)) :=
        (Submodule.span_insert_eq_span hjSpan).symm
      _ = Submodule.span (PolynomialRing k n) (emr_cover S : Set W) := by
        rw [← Finset.coe_insert, show insert (emr_gen S j) t = emr_cover S by
          exact Finset.insert_erase hgen_mem]
      _ = S.N := emr_cover_span S
  have htProperty : emr_CoverProperty S t.card := by
    refine ⟨t, rfl, ?_, htSpan⟩
    intro m hm
    exact emr_cover_homogeneous S m (Finset.erase_subset _ _ hm)
  have hle : emr_minCard S ≤ t.card := by
    classical
    change Nat.find (emr_coverProperty_exists S) ≤ t.card
    exact Nat.find_min' (emr_coverProperty_exists S) htProperty
  have hlt : t.card < emr_minCard S := by
    rw [← emr_cover_card S]
    exact Finset.card_erase_lt_of_mem hgen_mem
  exact (not_lt_of_ge hle hlt).elim

private noncomputable def emr_phiToN {k : Type*} [Field k] {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module (PolynomialRing k n) W] [Module k W]
    (S : emr_StageData k n W) :
    (Fin (emr_rank S) → PolynomialRing k n) →ₗ[PolynomialRing k n] ↥S.N :=
  (emr_phi S).codRestrict S.N fun x => by
    rw [← emr_phi_range S]
    exact (emr_phi S).mem_range_self x

private theorem emr_phiToN_surjective {k : Type*} [Field k] {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module (PolynomialRing k n) W] [Module k W]
    (S : emr_StageData k n W) : Function.Surjective (emr_phiToN S) := by
  intro y
  have hy : y.1 ∈ LinearMap.range (emr_phi S) := by
    rw [emr_phi_range S]
    exact y.2
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

private theorem emr_phiToN_ker {k : Type*} [Field k] {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module (PolynomialRing k n) W] [Module k W]
    (S : emr_StageData k n W) :
    LinearMap.ker (emr_phiToN S) = LinearMap.ker (emr_phi S) :=
  LinearMap.ker_codRestrict _ _ _

private theorem emr_ker_eq_bot_of_projective {k : Type*} [Field k] {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module (PolynomialRing k n) W] [Module k W]
    (S : emr_StageData k n W)
    [Module.Projective (PolynomialRing k n) ↥S.N] :
    LinearMap.ker (emr_phi S) = ⊥ := by
  classical
  let φ' := emr_phiToN S
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property φ' LinearMap.id
    (emr_phiToN_surjective S)
  let p : (Fin (emr_rank S) → PolynomialRing k n) →ₗ[PolynomialRing k n]
      (Fin (emr_rank S) → PolynomialRing k n) :=
    LinearMap.id - σ.comp φ'
  have hσ_apply (y : ↥S.N) : φ' (σ y) = y := by
    have h := congrArg (fun f => f y) hσ
    simpa using h
  have hpker (x : Fin (emr_rank S) → PolynomialRing k n) :
      p x ∈ LinearMap.ker (emr_phi S) := by
    rw [← emr_phiToN_ker S, LinearMap.mem_ker]
    change φ' (x - σ (φ' x)) = 0
    rw [map_sub, hσ_apply]
    exact sub_self _
  have hpfix (x : Fin (emr_rank S) → PolynomialRing k n)
      (hx : x ∈ LinearMap.ker (emr_phi S)) : p x = x := by
    have hx' : x ∈ LinearMap.ker φ' := by
      rw [emr_phiToN_ker S]
      exact hx
    have hx0 := LinearMap.mem_ker.mp hx'
    change x - σ (φ' x) = x
    rw [hx0]
    simp
  let I : Ideal (PolynomialRing k n) :=
    RingHom.ker (MvPolynomial.constantCoeff : PolynomialRing k n →+* k)
  have hle : LinearMap.ker (emr_phi S) ≤ I • LinearMap.ker (emr_phi S) := by
    intro x hx
    have hrepr : (∑ j, (x j) • ((Pi.single j (1 : PolynomialRing k n) :
        Fin (emr_rank S) → PolynomialRing k n))) = x := by
      have h1 : ∀ j : Fin (emr_rank S), (x j) • ((Pi.single j (1 : PolynomialRing k n) :
          Fin (emr_rank S) → PolynomialRing k n)) =
          (Pi.single j (x j) : Fin (emr_rank S) → PolynomialRing k n) := by
        intro j
        rw [← Pi.single_smul]
        simp [smul_eq_mul]
      simp only [h1]
      funext l
      rw [Finset.sum_apply, Finset.sum_pi_single]
      simp
    rw [← hpfix x hx, ← hrepr, map_sum]
    simp only [map_smul]
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem_smul
    · rw [RingHom.mem_ker]
      exact emr_ker_constantCoeff S x hx j
    · exact hpker _
  have hfg : (LinearMap.ker (emr_phi S)).FG :=
    IsNoetherian.noetherian _
  obtain ⟨r, hrI, hrann⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I
      (LinearMap.ker (emr_phi S)) hfg hle
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
  funext j
  have hcoord := congrFun (hrann x hx) j
  change r * x j = 0 at hcoord
  exact (mul_eq_zero.mp hcoord).resolve_left hrne

private noncomputable def emr_nextStageData {k : Type*} [Field k] {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module (PolynomialRing k n) W] [Module k W]
    (S : emr_StageData k n W) :
    emr_StageData k n (Fin (emr_rank S) → PolynomialRing k n) where
  gW := emr_freePreGrading (k := k) (emr_shift S)
  N := LinearMap.ker (emr_phi S)
  graded x hx β := emr_ker_graded (k := k) (emr_shift S) S.gW (emr_phi S)
    (emr_phi_graded S) x hx β
  fg := IsNoetherian.noetherian _

private def emr_SigmaStage (k : Type*) [Field k] (n : ℕ) :=
  Σ b : ℕ, emr_StageData k n (Fin b → PolynomialRing k n)

private noncomputable def emr_nextS {k : Type*} [Field k] {n : ℕ} :
    emr_SigmaStage k n → emr_SigmaStage k n
  | ⟨_, S⟩ => ⟨_, emr_nextStageData S⟩

private noncomputable def emr_stageZero {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M] [Module k M]
    [IsScalarTower k (PolynomialRing k n) M] [Module.Finite (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) : emr_StageData k n M where
  gW := emr_preGradingOfGrading G
  N := ⊤
  graded := fun _ _ _ => Submodule.mem_top
  fg := Module.Finite.fg_top

private noncomputable def emr_stage' {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M] [Module k M]
    [IsScalarTower k (PolynomialRing k n) M] [Module.Finite (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) : ℕ → emr_SigmaStage k n
  | 0 => ⟨_, emr_nextStageData (emr_stageZero G)⟩
  | t + 1 => emr_nextS (emr_stage' G t)

private noncomputable def emr_b {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M] [Module k M]
    [IsScalarTower k (PolynomialRing k n) M] [Module.Finite (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) (t : ℕ) : ℕ :=
  (emr_stage' G t).1

private noncomputable def emr_Sk {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M] [Module k M]
    [IsScalarTower k (PolynomialRing k n) M] [Module.Finite (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) (t : ℕ) :
    emr_StageData k n (Fin (emr_b G t) → PolynomialRing k n) :=
  (emr_stage' G t).2

private theorem emr_b_succ {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M] [Module k M]
    [IsScalarTower k (PolynomialRing k n) M] [Module.Finite (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) (t : ℕ) :
    emr_b G (t + 1) = emr_rank (emr_Sk G t) := rfl

private theorem emr_Sk_zero {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M] [Module k M]
    [IsScalarTower k (PolynomialRing k n) M] [Module.Finite (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) :
    emr_Sk G 0 = emr_nextStageData (emr_stageZero G) := rfl

private theorem emr_Sk_succ {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M] [Module k M]
    [IsScalarTower k (PolynomialRing k n) M] [Module.Finite (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) (t : ℕ) :
    emr_Sk G (t + 1) = emr_nextStageData (emr_Sk G t) := rfl

private theorem emr_Sk_zero_N {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M] [Module k M]
    [IsScalarTower k (PolynomialRing k n) M] [Module.Finite (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) :
    (emr_Sk G 0).N = LinearMap.ker (emr_phi (emr_stageZero G)) := rfl

private theorem emr_Sk_succ_N {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M] [Module k M]
    [IsScalarTower k (PolynomialRing k n) M] [Module.Finite (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) (t : ℕ) :
    (emr_Sk G (t + 1)).N = LinearMap.ker (emr_phi (emr_Sk G t)) := rfl

open CategoryTheory in
private theorem emr_finite_quotient {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M] [Module k M]
    [IsScalarTower k (PolynomialRing k n) M] [Module.Finite (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) :
    Module.Finite (PolynomialRing k n)
      ((Fin (emr_rank (emr_stageZero G)) → PolynomialRing k n) ⧸
        LinearMap.ker (emr_phi (emr_stageZero G))) :=
  Module.Finite.of_surjective (Submodule.mkQ _)
    (Submodule.mkQ_surjective _)

open CategoryTheory in
private theorem emr_pdim_base {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M] [Module k M]
    [IsScalarTower k (PolynomialRing k n) M] [Module.Finite (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) :
    HasProjectiveDimensionLE
      (ModuleCat.of (PolynomialRing k n)
        ((Fin (emr_rank (emr_stageZero G)) → PolynomialRing k n) ⧸
          LinearMap.ker (emr_phi (emr_stageZero G)))) n := by
  have := emr_finite_quotient G
  exact MathlibExt.RingTheory.Polynomial.HilbertSyzygyWanted.hilbert_syzygy

open CategoryTheory in
private theorem emr_pdim_one {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M] [Module k M]
    [IsScalarTower k (PolynomialRing k n) M] [Module.Finite (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) :
    HasProjectiveDimensionLE
      (ModuleCat.of (PolynomialRing k n)
        ↥(LinearMap.ker (emr_phi (emr_stageZero G)))) (n - 1) := by
  let N₁ := LinearMap.ker (emr_phi (emr_stageZero G))
  let Q := (Fin (emr_rank (emr_stageZero G)) → PolynomialRing k n) ⧸ N₁
  let ψ : (Fin (emr_rank (emr_stageZero G)) → PolynomialRing k n) →ₗ[PolynomialRing k n] Q :=
    Submodule.mkQ N₁
  let T := LinearMap.shortComplexKer ψ
  have hprev : HasProjectiveDimensionLT (ModuleCat.of (PolynomialRing k n) Q) (n + 1) :=
    emr_pdim_base G
  have hboost : HasProjectiveDimensionLT (ModuleCat.of (PolynomialRing k n) Q) (n - 1 + 2) :=
    hasProjectiveDimensionLT_of_ge _ (n := n + 1) (m := n - 1 + 2) (h := by omega)
  have hshort : T.ShortExact :=
    LinearMap.shortExact_shortComplexKer (Submodule.mkQ_surjective _)
  have hfree : Projective T.X₂ :=
    ModuleCat.projective_of_free
      (Pi.basisFun (PolynomialRing k n) (Fin (emr_rank (emr_stageZero G))))
  have hker : HasProjectiveDimensionLT T.X₁ (n - 1 + 1) :=
    (hshort.hasProjectiveDimensionLT_X₃_iff (n - 1) hfree).mp hboost
  let e : T.X₁ ≅ ModuleCat.of (PolynomialRing k n)
      ↥(LinearMap.ker (emr_phi (emr_stageZero G))) :=
    (LinearEquiv.ofEq _ _ (Submodule.ker_mkQ N₁)).toModuleIso
  have hkerN : HasProjectiveDimensionLT (ModuleCat.of (PolynomialRing k n)
      ↥(LinearMap.ker (emr_phi (emr_stageZero G)))) (n - 1 + 1) :=
    hasProjectiveDimensionLT_of_iso e _
  exact hkerN

open CategoryTheory in
private theorem emr_pdim_step {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M] [Module k M]
    [IsScalarTower k (PolynomialRing k n) M] [Module.Finite (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) (t : ℕ) (ht : t + 1 + 1 ≤ n)
    (ih : HasProjectiveDimensionLE (ModuleCat.of (PolynomialRing k n)
      ↥(emr_Sk G t).N) (n - (t + 1))) :
    HasProjectiveDimensionLE (ModuleCat.of (PolynomialRing k n)
      ↥(emr_Sk G (t + 1)).N) (n - (t + 1 + 1)) := by
  let T := LinearMap.shortComplexKer (emr_phiToN (emr_Sk G t))
  have hprev : HasProjectiveDimensionLT (ModuleCat.of (PolynomialRing k n)
      ↥(emr_Sk G t).N) (n - (t + 1) + 1) := ih
  have hboost : HasProjectiveDimensionLT (ModuleCat.of (PolynomialRing k n)
      ↥(emr_Sk G t).N) (n - (t + 1) - 1 + 2) :=
    hasProjectiveDimensionLT_of_ge _ (n := n - (t + 1) + 1)
      (m := n - (t + 1) - 1 + 2) (h := by omega)
  have hshort : T.ShortExact :=
    LinearMap.shortExact_shortComplexKer (emr_phiToN_surjective (emr_Sk G t))
  have hfree : Projective T.X₂ :=
    ModuleCat.projective_of_free
      (Pi.basisFun (PolynomialRing k n) (Fin (emr_rank (emr_Sk G t))))
  have hker : HasProjectiveDimensionLT T.X₁ (n - (t + 1) - 1 + 1) :=
    (hshort.hasProjectiveDimensionLT_X₃_iff (n - (t + 1) - 1) hfree).mp hboost
  have hNeq : LinearMap.ker (emr_phiToN (emr_Sk G t)) = (emr_Sk G (t + 1)).N := by
    rw [emr_phiToN_ker]
    exact (emr_Sk_succ_N G t).symm
  let e : T.X₁ ≅ ModuleCat.of (PolynomialRing k n) ↥(emr_Sk G (t + 1)).N :=
    (LinearEquiv.ofEq _ _ hNeq).toModuleIso
  have hkerN : HasProjectiveDimensionLT (ModuleCat.of (PolynomialRing k n)
      ↥(emr_Sk G (t + 1)).N) (n - (t + 1) - 1 + 1) :=
    hasProjectiveDimensionLT_of_iso e _
  have heq : n - (t + 1) - 1 + 1 = n - (t + 1 + 1) + 1 := by omega
  rw [heq] at hkerN
  exact hkerN

open CategoryTheory in
private theorem emr_pdim_le {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M] [Module k M]
    [IsScalarTower k (PolynomialRing k n) M] [Module.Finite (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) (t : ℕ) : t + 1 ≤ n →
    HasProjectiveDimensionLE (ModuleCat.of (PolynomialRing k n)
      ↥(emr_Sk G t).N) (n - (t + 1)) := by
  induction t with
  | zero =>
    intro _
    exact emr_pdim_one G
  | succ t ih =>
    intro ht
    exact emr_pdim_step G t ht (ih (by omega))

private theorem emr_ker_eq_bot_of_rank_eq_zero {k : Type*} [Field k] {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module (PolynomialRing k n) W] [Module k W]
    (S : emr_StageData k n W) (hS : emr_rank S = 0) :
    LinearMap.ker (emr_phi S) = ⊥ := by
  have hI : IsEmpty (Fin (emr_rank S)) :=
    ⟨fun j => by have h2 := j.isLt; omega⟩
  have : Subsingleton (Fin (emr_rank S) → PolynomialRing k n) :=
    ⟨fun f g => funext fun j => hI.elim j⟩
  rw [Submodule.eq_bot_iff]
  intro x _
  exact Subsingleton.elim x 0

private theorem emr_eq_C_constantCoeff_of_zero_vars {k : Type*} [Field k]
    (p : PolynomialRing k 0) : p = MvPolynomial.C (MvPolynomial.constantCoeff p) := by
  apply MvPolynomial.ext
  intro a
  by_cases ha : a = 0
  · subst ha
    have hC0 : (MvPolynomial.C (MvPolynomial.constantCoeff p) : PolynomialRing k 0).coeff 0
        = MvPolynomial.constantCoeff p := by simp
    rw [hC0, MvPolynomial.constantCoeff_eq]
  · have hempty : a = 0 := Finsupp.ext fun i => Fin.elim0 i
    exact absurd hempty ha

open CategoryTheory in
private theorem emr_N_succ_bot {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M] [Module k M]
    [IsScalarTower k (PolynomialRing k n) M] [Module.Finite (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) : (emr_Sk G n).N = ⊥ := by
  by_cases hn : n = 0
  · subst hn
    change LinearMap.ker (emr_phi (emr_stageZero G)) = ⊥
    rw [Submodule.eq_bot_iff]
    intro x hx
    funext j
    have hcc := emr_ker_constantCoeff (emr_stageZero G) x hx j
    rw [emr_eq_C_constantCoeff_of_zero_vars (x j), hcc]
    simp
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hle := emr_pdim_le G m (by omega : m + 1 ≤ m + 1)
    rw [Nat.sub_self] at hle
    have hproj : Projective
        (ModuleCat.of (PolynomialRing k (m + 1)) ↥(emr_Sk G m).N) :=
      (projective_iff_hasProjectiveDimensionLE_zero _).mpr hle
    have hmod : Module.Projective (PolynomialRing k (m + 1)) ↥(emr_Sk G m).N :=
      (IsProjective.iff_projective _).mpr hproj
    have hker := emr_ker_eq_bot_of_projective (emr_Sk G m)
    rwa [emr_Sk_succ_N]

private theorem emr_minCard_eq_zero_of_N_eq_bot {k : Type*} [Field k] {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module (PolynomialRing k n) W] [Module k W]
    (S : emr_StageData k n W) (hS : S.N = ⊥) : emr_minCard S = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  change Nat.find (emr_coverProperty_exists S) ≤ 0
  apply Nat.find_min' (emr_coverProperty_exists S)
  refine ⟨∅, by simp, ?_, ?_⟩
  · intro m hm
    simp at hm
  · simp [hS]

private theorem emr_rank_eq_zero_of_N_eq_bot {k : Type*} [Field k] {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module (PolynomialRing k n) W] [Module k W]
    (S : emr_StageData k n W) (hS : S.N = ⊥) : emr_rank S = 0 := by
  rw [emr_rank, emr_cover_card, emr_minCard_eq_zero_of_N_eq_bot S hS]

private theorem emr_Sk_N_eq_bot_add {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M] [Module k M]
    [IsScalarTower k (PolynomialRing k n) M] [Module.Finite (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) (d : ℕ) : (emr_Sk G (n + d)).N = ⊥ := by
  induction d with
  | zero =>
    simpa using emr_N_succ_bot G
  | succ d ih =>
    have h1 : (emr_Sk G (n + (d + 1))).N
        = LinearMap.ker (emr_phi (emr_Sk G (n + d))) :=
      emr_Sk_succ_N G (n + d)
    rw [h1]
    exact emr_ker_eq_bot_of_rank_eq_zero _ (emr_rank_eq_zero_of_N_eq_bot _ ih)

private theorem emr_Sk_N_eq_bot_of_le {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M] [Module k M]
    [IsScalarTower k (PolynomialRing k n) M] [Module.Finite (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) (t : ℕ) (ht : n ≤ t) :
    (emr_Sk G t).N = ⊥ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
  exact emr_Sk_N_eq_bot_add G d

private theorem emr_pi_repr {k : Type*} [Field k] {n b : ℕ}
    (x : Fin b → PolynomialRing k n) :
    (∑ j, (x j) • ((Pi.single j (1 : PolynomialRing k n)) :
      Fin b → PolynomialRing k n)) = x := by
  have h1 : ∀ j : Fin b, (x j) • ((Pi.single j (1 : PolynomialRing k n)) :
      Fin b → PolynomialRing k n) =
      (Pi.single j (x j) : Fin b → PolynomialRing k n) := by
    intro j
    rw [← Pi.single_smul]
    simp [smul_eq_mul]
  simp only [h1]
  funext l
  rw [Finset.sum_apply, Finset.sum_pi_single]
  simp

private theorem emr_ker_le_irrelevant_smul {k : Type*} [Field k] {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module (PolynomialRing k n) W] [Module k W]
    (S : emr_StageData k n W) :
    LinearMap.ker (emr_phi S) ≤ irrelevant (k := k) (n := n) •
      (⊤ : Submodule (PolynomialRing k n) (Fin (emr_rank S) → PolynomialRing k n)) := by
  intro x hx
  rw [← emr_pi_repr x]
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem_smul
  · apply emr_constantCoeff_mem_irrelevant
    exact emr_ker_constantCoeff S x hx j
  · exact Submodule.mem_top

private noncomputable def emr_degrees {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M] [Module k M]
    [IsScalarTower k (PolynomialRing k n) M] [Module.Finite (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) (i : ℕ) : Fin (emr_b G i) → ℤ := by
  cases i with
  | zero => exact emr_shift (emr_stageZero G)
  | succ i => exact emr_shift (emr_Sk G i)

private theorem emr_degrees_zero {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M] [Module k M]
    [IsScalarTower k (PolynomialRing k n) M] [Module.Finite (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) :
    emr_degrees G 0 = emr_shift (emr_stageZero G) := rfl

private theorem emr_degrees_succ {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M] [Module k M]
    [IsScalarTower k (PolynomialRing k n) M] [Module.Finite (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) (i : ℕ) :
    emr_degrees G (i + 1) = emr_shift (emr_Sk G i) := rfl

private noncomputable def emr_differential {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M] [Module k M]
    [IsScalarTower k (PolynomialRing k n) M] [Module.Finite (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) (i : ℕ) :
    (Fin (emr_b G (i + 1)) → PolynomialRing k n) →ₗ[PolynomialRing k n]
      (Fin (emr_b G i) → PolynomialRing k n) :=
  emr_phi (emr_Sk G i)

private noncomputable def emr_augmentation {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M] [Module k M]
    [IsScalarTower k (PolynomialRing k n) M] [Module.Finite (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) :
    (Fin (emr_b G 0) → PolynomialRing k n) →ₗ[PolynomialRing k n] M :=
  emr_phi (emr_stageZero G)

private theorem emr_Sk_gW_piece_zero {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M] [Module k M]
    [IsScalarTower k (PolynomialRing k n) M] [Module.Finite (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) :
    (emr_Sk G 0).gW.piece = freePiece (k := k) (n := n) (emr_shift (emr_stageZero G)) := rfl

private theorem emr_Sk_gW_piece_succ {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M] [Module k M]
    [IsScalarTower k (PolynomialRing k n) M] [Module.Finite (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) (i : ℕ) :
    (emr_Sk G (i + 1)).gW.piece = freePiece (k := k) (n := n) (emr_shift (emr_Sk G i)) := rfl

private noncomputable def emr_resolution {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M]
    [Module k M] [IsScalarTower k (PolynomialRing k n) M]
    [Module.Finite (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) : MinimalResolution G where
  ranks := emr_b G
  degrees := emr_degrees G
  differential := emr_differential G
  augmentation := emr_augmentation G
  differential_graded i j x hx := by
    cases i with
    | zero =>
      change emr_phi (emr_Sk G 0) x ∈ freePiece (k := k) (n := n) (emr_degrees G 0) j
      rw [emr_degrees_zero]
      have hx' : x ∈ freePiece (k := k) (n := n) (emr_shift (emr_Sk G 0)) j := by
        have h1 : emr_degrees G (0 + 1) = emr_shift (emr_Sk G 0) := emr_degrees_succ G 0
        rwa [h1] at hx
      have hmem := emr_phi_graded (emr_Sk G 0) j x hx'
      rwa [emr_Sk_gW_piece_zero] at hmem
    | succ i =>
      change emr_phi (emr_Sk G (i + 1)) x ∈ freePiece (k := k) (n := n) (emr_degrees G (i + 1)) j
      rw [emr_degrees_succ]
      have hx' : x ∈ freePiece (k := k) (n := n) (emr_shift (emr_Sk G (i + 1))) j := by
        have h1 : emr_degrees G (i + 1 + 1) = emr_shift (emr_Sk G (i + 1)) :=
          emr_degrees_succ G (i + 1)
        rwa [h1] at hx
      have hmem := emr_phi_graded (emr_Sk G (i + 1)) j x hx'
      rwa [emr_Sk_gW_piece_succ] at hmem
  augmentation_graded j x hx := by
    change emr_phi (emr_stageZero G) x ∈ G.piece j
    have hx' : x ∈ freePiece (k := k) (n := n) (emr_shift (emr_stageZero G)) j := by
      rwa [emr_degrees_zero] at hx
    have hmem := emr_phi_graded (emr_stageZero G) j x hx'
    have hpiece : (emr_stageZero G).gW.piece = G.piece := rfl
    rwa [hpiece] at hmem
  augmentation_surjective := by
    intro m
    have hmem : m ∈ LinearMap.range (emr_phi (emr_stageZero G)) := by
      rw [emr_phi_range (emr_stageZero G)]
      exact Submodule.mem_top
    obtain ⟨x, hx⟩ := hmem
    exact ⟨x, hx⟩
  exact_zero := by
    change LinearMap.range (emr_phi (emr_Sk G 0))
      = LinearMap.ker (emr_phi (emr_stageZero G))
    rw [emr_phi_range (emr_Sk G 0)]
    exact emr_Sk_zero_N G
  exact_succ i := by
    change LinearMap.range (emr_phi (emr_Sk G (i + 1)))
      = LinearMap.ker (emr_phi (emr_Sk G i))
    rw [emr_phi_range]
    exact emr_Sk_succ_N G i
  minimal i := by
    cases i with
    | zero =>
      change LinearMap.range (emr_phi (emr_Sk G 0)) ≤ _
      rw [emr_phi_range, emr_Sk_zero_N]
      exact emr_ker_le_irrelevant_smul _
    | succ i =>
      change LinearMap.range (emr_phi (emr_Sk G (i + 1))) ≤ _
      rw [emr_phi_range, emr_Sk_succ_N]
      exact emr_ker_le_irrelevant_smul _
  length_bound i hi := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    change emr_b G (t + 1) = 0
    rw [emr_b_succ]
    apply emr_rank_eq_zero_of_N_eq_bot
    apply emr_Sk_N_eq_bot_of_le
    omega

/-- Graded Hilbert syzygy with minimal differentials and the correct length bound. -/
public theorem exists_minimalResolution {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M]
    [Module k M] [IsScalarTower k (PolynomialRing k n) M]
    [Module.Finite (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) : Nonempty (MinimalResolution G) :=
  ⟨emr_resolution G⟩

end WantedExt.AlgebraicGeometry.MinimalGradedResolutionWanted
