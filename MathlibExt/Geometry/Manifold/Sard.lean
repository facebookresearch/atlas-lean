/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.Sheaf.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.Module.Multilinear.Topology
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import MathlibExt.MeasureTheory.Measure.ImageNull

@[expose] public section

open scoped Manifold ContDiff Topology ENNReal MeasureTheory
open MeasureTheory

section
noncomputable section

namespace MathlibExt.Geometry.Manifold.SardWanted

universe u v

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [T2Space M] [SecondCountableTopology M]
variable {n : ℕ} [MeasurableSpace (EuclideanSpace ℝ (Fin n))]
  [BorelSpace (EuclideanSpace ℝ (Fin n))]

/-- **Critical points of a map to Euclidean space.** Let $M$ be a Hausdorff, second-countable
smooth manifold without boundary modelled on a finite-dimensional real normed space, and let
$f : M \to \mathbb{R}^n$ be a map. The critical set of $f$ is the set of points $x \in M$ at which
the manifold derivative of $f$ at $x$, a linear map $T_xM \to \mathbb{R}^n$, is not surjective.

The derivative is taken to be $0$ at points where $f$ is not differentiable. -/
def criticalSet (f : M → EuclideanSpace ℝ (Fin n)) : Set M :=
  {x | ¬ Function.Surjective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) f x)}

/-- **Critical values of a map to Euclidean space.** Let $M$ be a Hausdorff, second-countable
smooth manifold without boundary modelled on a finite-dimensional real normed space, and let
$f : M \to \mathbb{R}^n$ be a map. The set of critical values of $f$ is the image under $f$ of its
critical set, the set of points $x \in M$ at which the manifold derivative of $f$ at $x$ is not
surjective. -/
def criticalValues (f : M → EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  f '' criticalSet (I := I) (M := M) (n := n) f

/-- Euclidean critical points of `g` in `U`: points of `U` where `fderiv` is not surjective. -/
private def critPtsOn {E6 : Type*} [NormedAddCommGroup E6] [NormedSpace ℝ E6]
    {F6 : Type*} [NormedAddCommGroup F6] [NormedSpace ℝ F6] (g : E6 → F6)
    (U : Set E6) : Set E6 :=
  {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ g x)}

private theorem mem_critPtsOn {E6 : Type*} [NormedAddCommGroup E6] [NormedSpace ℝ E6]
    {F6 : Type*} [NormedAddCommGroup F6] [NormedSpace ℝ F6] (g : E6 → F6)
    (U : Set E6) (x : E6) :
    x ∈ critPtsOn g U ↔ x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ g x) :=
  Iff.rfl

/-- Flat points of order `k`: points of `U` where all iterated derivatives `1..k` vanish. -/
private def flatPtsOn {E6 : Type*} [NormedAddCommGroup E6] [NormedSpace ℝ E6]
    {F6 : Type*} [NormedAddCommGroup F6] [NormedSpace ℝ F6] (g : E6 → F6)
    (U : Set E6) (k : ℕ) : Set E6 :=
  {x | x ∈ U ∧ ∀ j, 1 ≤ j → j ≤ k → iteratedFDeriv ℝ j g x = 0}

private theorem mem_flatPtsOn {E6 : Type*} [NormedAddCommGroup E6] [NormedSpace ℝ E6]
    {F6 : Type*} [NormedAddCommGroup F6] [NormedSpace ℝ F6] (g : E6 → F6)
    (U : Set E6) (k : ℕ) (x : E6) :
    x ∈ flatPtsOn g U k ↔
      x ∈ U ∧ ∀ j, 1 ≤ j → j ≤ k → iteratedFDeriv ℝ j g x = 0 :=
  Iff.rfl

private theorem flatPtsOn_zero {E6 : Type*} [NormedAddCommGroup E6] [NormedSpace ℝ E6]
    {F6 : Type*} [NormedAddCommGroup F6] [NormedSpace ℝ F6] (g : E6 → F6)
    (U : Set E6) : flatPtsOn g U 0 = U := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    refine ⟨hx, fun j h1 hj => ?_⟩
    have hfalse : False := by omega
    exact hfalse.elim

private theorem flatPtsOn_antitone {E6 : Type*} [NormedAddCommGroup E6]
    [NormedSpace ℝ E6] {F6 : Type*} [NormedAddCommGroup F6] [NormedSpace ℝ F6]
    (g : E6 → F6) (U : Set E6) {k₁ k₂ : ℕ} (hle : k₁ ≤ k₂) :
    flatPtsOn g U k₂ ⊆ flatPtsOn g U k₁ := by
  intro x hx
  refine ⟨hx.1, fun j h1 hj => hx.2 j h1 (le_trans hj hle)⟩

-- Helper N1: null sets transfer along continuous linear equivalences.
private theorem addHaar_image_equiv_null_iff
    (F1 G1 : Type*) [NormedAddCommGroup F1] [NormedSpace ℝ F1] [FiniteDimensional ℝ F1]
    [MeasurableSpace F1] [BorelSpace F1]
    [NormedAddCommGroup G1] [NormedSpace ℝ G1] [FiniteDimensional ℝ G1]
    [MeasurableSpace G1] [BorelSpace G1]
    (μ1 : Measure F1) [μ1.IsAddHaarMeasure] (ν1 : Measure G1) [ν1.IsAddHaarMeasure]
    (A1 : F1 ≃L[ℝ] G1) (T1 : Set F1) :
    ν1 (A1 '' T1) = 0 ↔ μ1 T1 = 0 := by
  let e : F1 ≃ᵐ G1 := A1.toHomeomorph.toMeasurableEquiv
  have hcoe : (e : F1 → G1) = (A1 : F1 → G1) := rfl
  have hmap_eq : Measure.map (e : F1 → G1) μ1 = Measure.map (A1 : F1 → G1) μ1 := by
    rw [hcoe]
  have hpre : (e : F1 ≃ᵐ G1) ⁻¹' (A1 '' T1) = T1 := by
    have : (e : F1 → G1) ⁻¹' (A1 '' T1) = A1 ⁻¹' (A1 '' T1) := by rw [hcoe]
    rw [this]
    rw [ContinuousLinearEquiv.image_eq_preimage_symm]
    simp
  have h1 : (Measure.map (A1 : F1 → G1) μ1) (A1 '' T1) = μ1 T1 := by
    rw [← hmap_eq, MeasurableEquiv.map_apply e (A1 '' T1), hpre]
  have hac1 : (Measure.map (A1 : F1 → G1) μ1) ≪ ν1 :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  have hac2 : ν1 ≪ (Measure.map (A1 : F1 → G1) μ1) :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  constructor
  · intro h
    have h2 : (Measure.map (A1 : F1 → G1) μ1) (A1 '' T1) = 0 := hac1 h
    rw [h1] at h2
    exact h2
  · intro h
    have h2 : (Measure.map (A1 : F1 → G1) μ1) (A1 '' T1) = 0 := by rw [h1]; exact h
    exact hac2 h2

-- Helper N6: criticality invariant under diffeomorphism of source / linear change of target.
private theorem surjective_fderiv_equiv_comp_comp_iff
    (E1 E2 F1 F2 : Type*)
    [NormedAddCommGroup E1] [NormedSpace ℝ E1]
    [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    [NormedAddCommGroup F1] [NormedSpace ℝ F1]
    [NormedAddCommGroup F2] [NormedSpace ℝ F2]
    (φ1 : E2 → E1) (y1 : E2) (e1 : E2 ≃L[ℝ] E1)
    (hφ1 : HasFDerivAt φ1 (e1 : E2 →L[ℝ] E1) y1)
    (g2 : E1 → F1) (hg2 : DifferentiableAt ℝ g2 (φ1 y1))
    (A2 : F1 ≃L[ℝ] F2) :
    Function.Surjective (fderiv ℝ (A2 ∘ g2 ∘ φ1) y1) ↔
    Function.Surjective (fderiv ℝ g2 (φ1 y1)) := by
  have hder : fderiv ℝ (A2 ∘ g2 ∘ φ1) y1 =
      (A2 : F1 →L[ℝ] F2).comp ((fderiv ℝ g2 (φ1 y1)).comp (e1 : E2 →L[ℝ] E1)) := by
    have hg' : HasFDerivAt g2 (fderiv ℝ g2 (φ1 y1)) (φ1 y1) := hg2.hasFDerivAt
    have hcomp1 : HasFDerivAt (g2 ∘ φ1) ((fderiv ℝ g2 (φ1 y1)).comp (e1 : E2 →L[ℝ] E1)) y1 :=
      hg'.comp y1 hφ1
    have hcomp2 : HasFDerivAt (A2 ∘ (g2 ∘ φ1))
        ((A2 : F1 →L[ℝ] F2).comp ((fderiv ℝ g2 (φ1 y1)).comp (e1 : E2 →L[ℝ] E1))) y1 :=
      (A2.hasFDerivAt).comp y1 hcomp1
    have hfun : A2 ∘ (g2 ∘ φ1) = A2 ∘ g2 ∘ φ1 := by
      funext z; rfl
    rw [hfun] at hcomp2
    exact hcomp2.fderiv
  rw [hder]
  have hAinj : Function.Injective (A2 : F1 → F2) := A2.injective
  have he_surj : Function.Surjective (e1 : E2 → E1) := e1.surjective
  constructor
  · intro h w
    obtain ⟨x, hx⟩ := h (A2 w)
    refine ⟨e1 x, hAinj hx⟩
  · intro h w
    obtain ⟨v, hv⟩ := h (A2.symm w)
    obtain ⟨u2, rfl⟩ := he_surj v
    refine ⟨u2, ?_⟩
    change A2 ((fderiv ℝ g2 (φ1 y1)) (e1 u2)) = w
    rw [hv]
    exact A2.apply_symm_apply w

-- Helper N7: split off a nonzero functional as ℝ × ker.
private theorem exists_equiv_prod_ker_of_ne_zero
    (F3 : Type*) [NormedAddCommGroup F3] [NormedSpace ℝ F3] [FiniteDimensional ℝ F3]
    (ℓ1 : F3 →L[ℝ] ℝ) (hℓ1 : ℓ1 ≠ 0) :
    ∃ A : F3 ≃L[ℝ] ℝ × LinearMap.ker (ℓ1 : F3 →ₗ[ℝ] ℝ),
      (∀ z, (A z).1 = ℓ1 z) ∧
      Module.finrank ℝ (LinearMap.ker (ℓ1 : F3 →ₗ[ℝ] ℝ)) + 1 = Module.finrank ℝ F3 := by
  have hex : ∃ z, ℓ1 z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hℓ1
    ext z
    simp [hcon z]
  obtain ⟨z0, hz0⟩ := hex
  set u : F3 := (ℓ1 z0)⁻¹ • z0 with hu_def
  have hu : ℓ1 u = 1 := by
    simp only [hu_def, map_smul, smul_eq_mul, inv_mul_cancel₀ hz0]
  let fwd : F3 →L[ℝ] ℝ × LinearMap.ker (ℓ1 : F3 →ₗ[ℝ] ℝ) :=
    { toFun := fun z => (ℓ1 z, ⟨z - ℓ1 z • u, by
        change (ℓ1 : F3 →ₗ[ℝ] ℝ) _ = 0
        simp [map_sub, map_smul, hu]⟩)
      map_add' := by
        intro x y
        apply Prod.ext
        · change ℓ1 (x + y) = ℓ1 x + ℓ1 y
          exact map_add ℓ1 x y
        · apply Subtype.ext
          change x + y - ℓ1 (x + y) • u = (x - ℓ1 x • u) + (y - ℓ1 y • u)
          simp [map_add, add_smul, add_sub_add_comm]
      map_smul' := by
        intro c x
        apply Prod.ext
        · change ℓ1 (c • x) = c • ℓ1 x
          exact map_smul ℓ1 c x
        · apply Subtype.ext
          change c • x - ℓ1 (c • x) • u = c • (x - ℓ1 x • u)
          simp [map_smul, smul_sub, smul_smul, mul_comm c (ℓ1 x)] }
  let bwd : (ℝ × LinearMap.ker (ℓ1 : F3 →ₗ[ℝ] ℝ)) →L[ℝ] F3 :=
    { toFun := fun p => p.1 • u + p.2.1
      map_add' := by intro x y; simp [add_smul, add_assoc, add_comm, add_left_comm]
      map_smul' := by intro c x; simp [smul_add, smul_smul] }
  have h1 : ∀ z, bwd (fwd z) = z := by
    intro z
    change ℓ1 z • u + (z - ℓ1 z • u) = z
    abel
  have h2 : ∀ p : ℝ × LinearMap.ker (ℓ1 : F3 →ₗ[ℝ] ℝ), fwd (bwd p) = p := by
    intro p
    obtain ⟨t, ⟨k, hk⟩⟩ := p
    have hk0 : ℓ1 k = 0 := hk
    apply Prod.ext
    · change ℓ1 (t • u + k) = t
      simp [map_add, map_smul, hu, hk0]
    · apply Subtype.ext
      change t • u + k - ℓ1 (t • u + k) • u = k
      simp [map_add, map_smul, hu, hk0]
  let A : F3 ≃L[ℝ] ℝ × LinearMap.ker (ℓ1 : F3 →ₗ[ℝ] ℝ) :=
    ContinuousLinearEquiv.equivOfInverse fwd bwd h1 h2
  refine ⟨A, ?_, ?_⟩
  · intro z
    rfl
  · have hfin : Module.finrank ℝ F3 = Module.finrank ℝ (ℝ × LinearMap.ker (ℓ1 : F3 →ₗ[ℝ] ℝ)) :=
      LinearEquiv.finrank_eq A.toLinearEquiv
    rw [hfin, Module.finrank_prod, Module.finrank_self]
    omega

-- Helper N5a: surjective continuous linear maps form an open set.
private theorem isOpen_setOf_surjective_clm
    (E3 F4 : Type*) [NormedAddCommGroup E3] [NormedSpace ℝ E3] [FiniteDimensional ℝ E3]
    [NormedAddCommGroup F4] [NormedSpace ℝ F4] [FiniteDimensional ℝ F4] :
    IsOpen {L : E3 →L[ℝ] F4 | Function.Surjective L} := by
  rw [isOpen_iff_forall_mem_open]
  intro L hL
  simp only [Set.mem_ofPred_eq] at hL
  have hrange : (L : E3 →ₗ[ℝ] F4).range = ⊤ := LinearMap.range_eq_top.mpr hL
  obtain ⟨Rlin, hR⟩ := LinearMap.exists_rightInverse_of_surjective
    (f := (L : E3 →ₗ[ℝ] F4)) hrange
  let R : F4 →L[ℝ] E3 := Rlin.toContinuousLinearMap
  have hLR : L.comp R = ContinuousLinearMap.id ℝ F4 := by
    ext y
    have h1 : (L.comp R) y = L (R y) := rfl
    have h2 : (ContinuousLinearMap.id ℝ F4) y = y := rfl
    rw [h1, h2]
    have hRlin : (L : E3 →ₗ[ℝ] F4) (Rlin y) = y := by
      have := congrArg (fun f => f y) hR
      simpa using this
    simpa [R] using hRlin
  have hcont : Continuous (fun L' : E3 →L[ℝ] F4 => L'.comp R) :=
    Continuous.clm_comp continuous_id continuous_const
  have hunits_open :
      IsOpen (Set.preimage (fun L' : E3 →L[ℝ] F4 => L'.comp R)
        {u : F4 →L[ℝ] F4 | IsUnit u}) := by
    apply hcont.isOpen_preimage
    exact Units.isOpen
  have hLmem : L ∈ Set.preimage (fun L' : E3 →L[ℝ] F4 => L'.comp R) {u | IsUnit u} := by
    change IsUnit (L.comp R)
    rw [hLR]
    exact isUnit_one
  obtain ⟨V, hVsub, hVopen, hLV⟩ := isOpen_iff_forall_mem_open.mp hunits_open _ hLmem
  refine ⟨V, hVsub.trans ?_, hVopen, hLV⟩
  intro L' hL'
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hL'
  simp only [Set.mem_ofPred_eq]
  obtain ⟨u, hu⟩ := hL'
  have hsurj_one : Function.Surjective ((1 : F4 →L[ℝ] F4) : F4 → F4) := by
    simpa using Function.surjective_id (α := F4)
  have hval : (u : F4 →L[ℝ] F4) * (u.inv : F4 →L[ℝ] F4) = 1 := u.val_inv
  have hsurj_comp :
      Function.Surjective (((u : F4 →L[ℝ] F4) : F4 → F4) ∘
        ((u.inv : F4 →L[ℝ] F4) : F4 → F4)) := by
    have hfun : (((u : F4 →L[ℝ] F4) * (u.inv : F4 →L[ℝ] F4) : F4 →L[ℝ] F4) : F4 → F4) =
        (((u : F4 →L[ℝ] F4) : F4 → F4) ∘ ((u.inv : F4 →L[ℝ] F4) : F4 → F4)) := by
      funext y; rfl
    rw [← hfun, hval]
    exact hsurj_one
  have hsurj_u : Function.Surjective ((u : F4 →L[ℝ] F4) : F4 → F4) :=
    Function.Surjective.of_comp hsurj_comp
  rw [hu] at hsurj_u
  have hsurj_fun : Function.Surjective ((L' : E3 → F4) ∘ (R : F4 → E3)) := hsurj_u
  exact Function.Surjective.of_comp hsurj_fun

-- Helper N5b: critical set intersected with a compact subset of an open smooth domain is compact.
private theorem isCompact_inter_critPtsOn
    (E5 F5 : Type*) [NormedAddCommGroup E5] [NormedSpace ℝ E5] [FiniteDimensional ℝ E5]
    [NormedAddCommGroup F5] [NormedSpace ℝ F5] [FiniteDimensional ℝ F5]
    (U : Set E5) (hU : IsOpen U) (g : E5 → F5) (hg : ContDiffOn ℝ 1 g U)
    (Q : Set E5) (hQ : IsCompact Q) (hQU : Q ⊆ U) :
    IsCompact (Q ∩ {x | ¬ Function.Surjective (fderiv ℝ g x)}) := by
  have hopen : IsOpen {L : E5 →L[ℝ] F5 | Function.Surjective (L : E5 → F5)} :=
    isOpen_setOf_surjective_clm E5 F5
  have hclosed : IsClosed {L : E5 →L[ℝ] F5 | ¬ Function.Surjective (L : E5 → F5)} := by
    have h : {L : E5 →L[ℝ] F5 | ¬ Function.Surjective (L : E5 → F5)} =
        {L : E5 →L[ℝ] F5 | Function.Surjective (L : E5 → F5)}ᶜ := rfl
    rw [h]
    exact hopen.isClosed_compl
  have hQclosed : IsClosed Q := hQ.isClosed
  have hcont : ContinuousOn (fderiv ℝ g) Q := by
    have h := hg.continuousOn_fderiv_of_isOpen hU (by norm_num : (1 : WithTop ℕ∞) ≤ 1)
    exact h.mono hQU
  have hisclosed :
      IsClosed (Q ∩ (fderiv ℝ g) ⁻¹'
        {L : E5 →L[ℝ] F5 | ¬ Function.Surjective (L : E5 → F5)}) :=
    hcont.preimage_isClosed_of_isClosed hQclosed hclosed
  have heq : (Q ∩ {x | ¬ Function.Surjective (fderiv ℝ g x)}) =
      (Q ∩ (fderiv ℝ g) ⁻¹' {L : E5 →L[ℝ] F5 | ¬ Function.Surjective (L : E5 → F5)}) := rfl
  rw [heq]
  exact hQ.of_isClosed_subset hisclosed Set.inter_subset_left

-- Helper N4: Taylor bound at flat points by iterating the mean value inequality.
private theorem norm_sub_le_of_iteratedFDeriv_eq_zero
    {E7 : Type*} [NormedAddCommGroup E7] [NormedSpace ℝ E7]
    {F7 : Type*} [NormedAddCommGroup F7] [NormedSpace ℝ F7]
    (U : Set E7) (hU : IsOpen U) (g : E7 → F7) (k : ℕ)
    (hg : ContDiffOn ℝ (↑(k + 1) : WithTop ℕ∞) g U)
    (Q : Set E7) (hQconv : Convex ℝ Q) (hQU : Q ⊆ U)
    (B : ℝ) (hB : ∀ z ∈ Q, ‖iteratedFDeriv ℝ (k + 1) g z‖ ≤ B)
    (x : E7) (hx : x ∈ Q)
    (hxflat : ∀ j, 1 ≤ j → j ≤ k → iteratedFDeriv ℝ j g x = 0)
    (y : E7) (hy : y ∈ Q) :
    ‖g y - g x‖ ≤ B * ‖y - x‖ ^ (k + 1) := by
  have hBnonneg : 0 ≤ B := le_trans (norm_nonneg _) (hB x hx)
  have key : ∀ d j, j + d = k → ∀ w ∈ Q,
      ‖iteratedFDeriv ℝ j g w - iteratedFDeriv ℝ j g x‖ ≤
        B * ‖w - x‖ ^ (k + 1 - j) := by
    intro d
    induction d with
    | zero =>
      intro j hjk w hw
      have hjk' : j = k := by omega
      subst j
      have hsegw : segment ℝ x w ⊆ Q := hQconv.segment_subset hx hw
      have hC : ∀ z ∈ segment ℝ x w,
          ‖fderiv ℝ (iteratedFDeriv ℝ k g) z‖ ≤ B := by
        intro z hz
        rw [norm_fderiv_iteratedFDeriv]
        exact hB z (hsegw hz)
      have hdiffw : ∀ z ∈ segment ℝ x w,
          DifferentiableAt ℝ (iteratedFDeriv ℝ k g) z := by
        intro z hz
        have hzU : U ∈ 𝓝 z := hU.mem_nhds (hQU (hsegw hz))
        have hcd := hg.contDiffAt hzU
        have hlt : (↑k : WithTop ℕ∞) < ↑(k + 1) := by
          norm_cast
          omega
        exact hcd.differentiableAt_iteratedFDeriv hlt
      have hle := (convex_segment x w).norm_image_sub_le_of_norm_fderiv_le
        hdiffw hC (left_mem_segment ℝ x w) (right_mem_segment ℝ x w)
      have hexp0 : k + 1 - k = 1 := by omega
      rw [hexp0, pow_one]
      exact hle
    | succ d ih =>
      intro j hjk w hw
      have hsegw : segment ℝ x w ⊆ Q := hQconv.segment_subset hx hw
      have hj1d : (j + 1) + d = k := by omega
      have hjle : j + 1 ≤ k := by omega
      have hxvan : iteratedFDeriv ℝ (j + 1) g x = 0 :=
        hxflat (j + 1) (by omega) hjle
      have hexp : k + 1 - (j + 1) = k - j := by omega
      have hC : ∀ z ∈ segment ℝ x w,
          ‖fderiv ℝ (iteratedFDeriv ℝ j g) z‖ ≤ B * ‖w - x‖ ^ (k - j) := by
        intro z hz
        rw [norm_fderiv_iteratedFDeriv]
        have hzQ : z ∈ Q := hsegw hz
        have hP := ih (j + 1) hj1d z hzQ
        rw [hexp, hxvan, sub_zero] at hP
        have hzx : ‖z - x‖ ≤ ‖w - x‖ := norm_sub_le_of_mem_segment hz
        have hpow : ‖z - x‖ ^ (k - j) ≤ ‖w - x‖ ^ (k - j) :=
          pow_le_pow_left₀ (norm_nonneg _) hzx _
        calc ‖iteratedFDeriv ℝ (j + 1) g z‖ ≤ B * ‖z - x‖ ^ (k - j) := hP
          _ ≤ B * ‖w - x‖ ^ (k - j) :=
            mul_le_mul_of_nonneg_left hpow hBnonneg
      have hdiffw : ∀ z ∈ segment ℝ x w,
          DifferentiableAt ℝ (iteratedFDeriv ℝ j g) z := by
        intro z hz
        have hzU : U ∈ 𝓝 z := hU.mem_nhds (hQU (hsegw hz))
        have hcd := hg.contDiffAt hzU
        have hlt : (↑j : WithTop ℕ∞) < ↑(k + 1) := by
          norm_cast
          omega
        exact hcd.differentiableAt_iteratedFDeriv hlt
      have hle := (convex_segment x w).norm_image_sub_le_of_norm_fderiv_le
        hdiffw hC (left_mem_segment ℝ x w) (right_mem_segment ℝ x w)
      have hexp2 : k + 1 - j = (k - j) + 1 := by omega
      rw [hexp2, pow_succ]
      calc ‖iteratedFDeriv ℝ j g w - iteratedFDeriv ℝ j g x‖
          ≤ (B * ‖w - x‖ ^ (k - j)) * ‖w - x‖ := hle
        _ = B * (‖w - x‖ ^ (k - j) * ‖w - x‖) := by ring
  have hkey0 := key k 0 (by omega) y hy
  rw [show k + 1 - 0 = k + 1 from by omega] at hkey0
  have hconv : ‖iteratedFDeriv ℝ 0 g y - iteratedFDeriv ℝ 0 g x‖ =
      ‖g y - g x‖ := by
    have h0 : ∀ t, iteratedFDeriv ℝ 0 g t =
        (continuousMultilinearCurryFin0 ℝ E7 F7).symm (g t) := fun t => by
      rw [iteratedFDeriv_zero_eq_comp]
      rfl
    rw [h0 y, h0 x, ← map_sub]
    exact LinearIsometryEquiv.norm_map _ _
  rw [hconv] at hkey0
  exact hkey0

-- Helper N3: Hölder images of low-dimensional sets are null for add-Haar measures.
private theorem addHaar_image_null_of_holderOnWith
    {E8 : Type*} [NormedAddCommGroup E8] [NormedSpace ℝ E8] [FiniteDimensional ℝ E8]
    {F8 : Type*} [NormedAddCommGroup F8] [NormedSpace ℝ F8] [FiniteDimensional ℝ F8]
    [MeasurableSpace F8] [BorelSpace F8]
    (μ : Measure F8) [μ.IsAddHaarMeasure]
    (g : E8 → F8) (S : Set E8)
    (C : NNReal) (r : NNReal) (hr : 0 < r)
    (hg : HolderOnWith C r g S)
    (hdim : (Module.finrank ℝ E8 : ℝ) < (r : ℝ) * Module.finrank ℝ F8) :
    μ (g '' S) = 0 := by
  borelize E8
  set p : ℕ := Module.finrank ℝ F8 with hp
  have hdimENN :
      (Module.finrank ℝ E8 : ℝ≥0∞) < ((r * p : NNReal) : ℝ≥0∞) := by
    exact_mod_cast hdim
  have hdimH : dimH S < ((r * p : NNReal) : ℝ≥0∞) := by
    calc dimH S ≤ dimH (Set.univ : Set E8) := dimH_mono (Set.subset_univ _)
      _ = Module.finrank ℝ E8 := Real.dimH_univ_eq_finrank E8
      _ < ((r * p : NNReal) : ℝ≥0∞) := hdimENN
  have hHzero : μH[(r : ℝ) * (p : ℝ)] S = 0 := by
    have h := hausdorffMeasure_of_dimH_lt hdimH
    simpa [NNReal.coe_mul] using h
  have hpos : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have hle := hg.hausdorffMeasure_image_le hr hpos
  rw [hHzero, mul_zero] at hle
  have hHimg : μH[(p : ℝ)] (g '' S) = 0 := nonpos_iff_eq_zero.mp hle
  have hA : Module.finrank ℝ F8 = Module.finrank ℝ (Fin p → ℝ) := by
    rw [Module.finrank_fin_fun ℝ]
  let A : F8 ≃L[ℝ] (Fin p → ℝ) := ContinuousLinearEquiv.ofFinrankEq hA
  have hAlip : LipschitzWith ‖A.toContinuousLinearMap‖₊ (A : F8 → Fin p → ℝ) :=
    A.toContinuousLinearMap.lipschitzWith
  have hHimgA : μH[(p : ℝ)] (A '' (g '' S)) = 0 := by
    have hleA := hAlip.hausdorffMeasure_image_le hpos (g '' S)
    rw [hHimg, mul_zero] at hleA
    exact nonpos_iff_eq_zero.mp hleA
  have hvol : volume (A '' (g '' S)) = 0 := by
    have hpi := hausdorffMeasure_pi_real (ι := Fin p)
    rw [Fintype.card_fin] at hpi
    rw [← hpi]
    exact hHimgA
  have hN1 := addHaar_image_equiv_null_iff F8 (Fin p → ℝ) μ volume A (g '' S)
  exact hN1.mp hvol

-- Helper N8: straightening chart with first coordinate `w`.
private theorem exists_straightening_chart
    {E9 : Type*} [NormedAddCommGroup E9] [NormedSpace ℝ E9] [FiniteDimensional ℝ E9]
    (U : Set E9) (hU : IsOpen U) (w : E9 → ℝ) (hw : ContDiffOn ℝ ∞ w U)
    (xbar : E9) (hxbar : xbar ∈ U) (hne : fderiv ℝ w xbar ≠ 0) :
    ∃ h : OpenPartialHomeomorph E9
        (ℝ × LinearMap.ker (fderiv ℝ w xbar : E9 →ₗ[ℝ] ℝ)),
      xbar ∈ h.source ∧
      h.source ⊆ U ∧
      (∀ x ∈ h.source, (h x).1 = w x) ∧
      ContDiffOn ℝ ∞ h.symm h.target ∧
      (∀ z ∈ h.target,
        ∃ e : (ℝ × LinearMap.ker (fderiv ℝ w xbar : E9 →ₗ[ℝ] ℝ)) ≃L[ℝ] E9,
          HasFDerivAt h.symm e.toContinuousLinearMap z) ∧
      Module.finrank ℝ (LinearMap.ker (fderiv ℝ w xbar : E9 →ₗ[ℝ] ℝ)) + 1 =
        Module.finrank ℝ E9 := by
  set ℓ : E9 →L[ℝ] ℝ := fderiv ℝ w xbar with hℓ
  obtain ⟨A, hA1, hAfin⟩ := exists_equiv_prod_ker_of_ne_zero E9 ℓ hne
  have h2 : ContDiffOn ℝ ∞ (fun x : E9 => (A x).2) U :=
    ((ContinuousLinearMap.snd ℝ ℝ _).comp
      A.toContinuousLinearMap).contDiff.contDiffOn
  have hwH : ContDiffOn ℝ ∞ (fun x : E9 => (w x, (A x).2)) U := hw.prodMk h2
  have hwxbar : HasFDerivAt w ℓ xbar := by
    have hcd : ContDiffAt ℝ ∞ w xbar := hw.contDiffAt (hU.mem_nhds hxbar)
    exact (hcd.differentiableAt (by simp)).hasFDerivAt
  have hA2xbar : HasFDerivAt (fun x : E9 => (A x).2)
      ((ContinuousLinearMap.snd ℝ ℝ _).comp A.toContinuousLinearMap) xbar :=
    ((ContinuousLinearMap.snd ℝ ℝ _).comp A.toContinuousLinearMap).hasFDerivAt
  have hHderiv : HasFDerivAt (fun x : E9 => (w x, (A x).2))
      A.toContinuousLinearMap xbar := by
    have hprod := hwxbar.prodMk hA2xbar
    have hDerivEq : ℓ.prod
          ((ContinuousLinearMap.snd ℝ ℝ _).comp A.toContinuousLinearMap) =
        A.toContinuousLinearMap := by
      ext z
      · exact (hA1 z).symm
      · rfl
    rw [hDerivEq] at hprod
    exact hprod
  have hxU : U ∈ 𝓝 xbar := hU.mem_nhds hxbar
  have hcdH : ContDiffAt ℝ ∞ (fun x : E9 => (w x, (A x).2)) xbar :=
    hwH.contDiffAt hxU
  set h0 : OpenPartialHomeomorph E9
      (ℝ × LinearMap.ker (ℓ : E9 →ₗ[ℝ] ℝ)) :=
    ContDiffAt.toOpenPartialHomeomorph (fun x : E9 => (w x, (A x).2))
      hcdH hHderiv (by simp) with hh0
  have h0coe : ⇑h0 = (fun x : E9 => (w x, (A x).2)) :=
    ContDiffAt.toOpenPartialHomeomorph_coe hcdH hHderiv (by simp)
  have hx0 : xbar ∈ h0.source :=
    ContDiffAt.mem_toOpenPartialHomeomorph_source hcdH hHderiv (by simp)
  have hcont : ContinuousOn (fderiv ℝ (fun x : E9 => (w x, (A x).2))) U :=
    hwH.continuousOn_fderiv_of_isOpen hU (by simp)
  have hOopen : IsOpen (U ∩ (fderiv ℝ (fun x : E9 => (w x, (A x).2))) ⁻¹'
      (Set.range ContinuousLinearEquiv.toContinuousLinearMap)) :=
    hcont.isOpen_inter_preimage hU ContinuousLinearEquiv.isOpen
  set O : Set E9 := U ∩ (fderiv ℝ (fun x : E9 => (w x, (A x).2))) ⁻¹'
    (Set.range ContinuousLinearEquiv.toContinuousLinearMap) with hOdef
  have hxO : xbar ∈ O := by
    have hfd : fderiv ℝ (fun x : E9 => (w x, (A x).2)) xbar =
        A.toContinuousLinearMap := hHderiv.fderiv
    refine ⟨hxbar, Set.mem_preimage.mpr ?_⟩
    rw [hfd]
    exact Set.mem_range_self A
  set h : OpenPartialHomeomorph E9 (ℝ × LinearMap.ker (ℓ : E9 →ₗ[ℝ] ℝ)) :=
    h0.restrOpen O hOopen with hhdef
  have hxsrc : xbar ∈ h.source := by
    rw [hhdef, OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hx0, hxO⟩
  have hsrcU : h.source ⊆ U := by
    rw [hhdef, OpenPartialHomeomorph.restrOpen_source, hOdef]
    exact Set.inter_subset_right.trans Set.inter_subset_left
  have hcoe : ∀ x ∈ h.source, h x = (w x, (A x).2) := by
    intro x hx
    have h1 : h x = h0 x := rfl
    rw [h1]
    exact congrArg (fun F => F x) h0coe
  have hfst : ∀ x ∈ h.source, (h x).1 = w x := fun x hx => by rw [hcoe x hx]
  have hsrc_pt : ∀ x ∈ h.source, ∃ e : E9 ≃L[ℝ] (ℝ × LinearMap.ker (ℓ : E9 →ₗ[ℝ] ℝ)),
      HasFDerivAt h e.toContinuousLinearMap x ∧ ContDiffAt ℝ ∞ h x := by
    intro x hx
    have hxO' : x ∈ O := by
      rw [hhdef, OpenPartialHomeomorph.restrOpen_source] at hx
      exact hx.2
    rw [hOdef] at hxO'
    obtain ⟨hxU, hxpre⟩ := hxO'
    obtain ⟨e, he⟩ := hxpre
    have hcdx : ContDiffAt ℝ ∞ (fun y : E9 => (w y, (A y).2)) x :=
      hwH.contDiffAt (hU.mem_nhds hxU)
    have hmem : h.source ∈ 𝓝 x := h.open_source.mem_nhds hx
    have heq : (h : E9 → ℝ × LinearMap.ker (ℓ : E9 →ₗ[ℝ] ℝ)) =ᶠ[𝓝 x]
        (fun y : E9 => (w y, (A y).2)) :=
      Filter.eventually_of_mem hmem (fun y hy => hcoe y hy)
    refine ⟨e, ?_, hcdx.congr_of_eventuallyEq heq⟩
    have hHdat : HasFDerivAt (fun y : E9 => (w y, (A y).2))
        (fderiv ℝ (fun y : E9 => (w y, (A y).2)) x) x :=
      (hcdx.differentiableAt (by simp)).hasFDerivAt
    have hder := hHdat.congr_of_eventuallyEq heq
    rw [← he] at hder
    exact hder
  have hsymm_deriv : ∀ z ∈ h.target,
      ∃ e : (ℝ × LinearMap.ker (ℓ : E9 →ₗ[ℝ] ℝ)) ≃L[ℝ] E9,
        HasFDerivAt h.symm e.toContinuousLinearMap z := by
    intro z hz
    set x : E9 := h.symm z with hxdef
    have hx : x ∈ h.source := h.map_target hz
    obtain ⟨e, hederiv, -⟩ := hsrc_pt x hx
    exact ⟨e.symm, h.hasFDerivAt_symm hz hederiv⟩
  have hsymm_smooth : ContDiffOn ℝ ∞ h.symm h.target := by
    intro z hz
    set x : E9 := h.symm z with hxdef
    have hx : x ∈ h.source := h.map_target hz
    obtain ⟨e, hederiv, hcd⟩ := hsrc_pt x hx
    have hsymm_at := h.contDiffAt_symm hz hederiv hcd
    exact hsymm_at.contDiffWithinAt
  exact ⟨h, hxsrc, hsrcU, hfst, hsymm_smooth, hsymm_deriv, hAfin⟩

-- Helper N9: Fubini step for maps `(t, y) ↦ (t, G_t y)`.
private theorem prod_null_image_critPts_of_slices
    {K10 : Type*} [NormedAddCommGroup K10] [NormedSpace ℝ K10]
    [FiniteDimensional ℝ K10]
    {F10 : Type*} [NormedAddCommGroup F10] [NormedSpace ℝ F10]
    [FiniteDimensional ℝ F10]
    [MeasurableSpace F10] [BorelSpace F10]
    (μ' : Measure F10) [μ'.IsAddHaarMeasure]
    (W : Set (ℝ × K10)) (hW : IsOpen W)
    (G : (ℝ × K10) → (ℝ × F10)) (hG : ContDiffOn ℝ ∞ G W)
    (hGfst : ∀ z ∈ W, (G z).1 = z.1)
    (hslice : ∀ t : ℝ, μ' ((fun y => (G (t, y)).2) ''
      critPtsOn (fun y => (G (t, y)).2) {y | (t, y) ∈ W}) = 0)
    (Q : Set (ℝ × K10)) (hQ : IsCompact Q) (hQW : Q ⊆ W) :
    ((volume : Measure ℝ).prod μ')
      (G '' (Q ∩ {z | ¬ Function.Surjective (fderiv ℝ G z)})) = 0 := by
  have hslice_iff : ∀ (t : ℝ) (y : K10), (t, y) ∈ W →
      (Function.Surjective (fderiv ℝ G (t, y)) ↔
        Function.Surjective (fderiv ℝ (fun y => (G (t, y)).2) y)) := by
    intro t y hyW
    set z : ℝ × K10 := (t, y) with hzdef
    set L : (ℝ × K10) →L[ℝ] (ℝ × F10) := fderiv ℝ G z with hLdef
    have hGdiff : DifferentiableAt ℝ G z :=
      (hG.contDiffAt (hW.mem_nhds hyW)).differentiableAt (by simp)
    have hfst_comp : (ContinuousLinearMap.fst ℝ ℝ F10).comp L =
        ContinuousLinearMap.fst ℝ ℝ K10 := by
      have hGfst_eq : (fun w => (G w).1) =ᶠ[𝓝 z] Prod.fst :=
        Filter.eventually_of_mem (hW.mem_nhds hyW) (fun w hw => hGfst w hw)
      have h1 : fderiv ℝ (fun w => (G w).1) z = fderiv ℝ Prod.fst z :=
        hGfst_eq.fderiv_eq
      rw [fderiv_fst] at h1
      have hchain : HasFDerivAt (fun w => (G w).1)
          ((ContinuousLinearMap.fst ℝ ℝ F10).comp L) z :=
        (ContinuousLinearMap.fst ℝ ℝ F10).hasFDerivAt.comp z hGdiff.hasFDerivAt
      have h2 := hchain.fderiv
      rw [h2] at h1
      exact h1
    have hLfst : ∀ w : ℝ × K10, (L w).1 = w.1 :=
      fun w => congrArg (fun F => F w) hfst_comp
    have hGt_eq : fderiv ℝ (fun y => (G (t, y)).2) y =
        (ContinuousLinearMap.snd ℝ ℝ F10).comp
          (L.comp (ContinuousLinearMap.inr ℝ ℝ K10)) := by
      have hprod_y : HasFDerivAt (fun y => (t, y))
          (ContinuousLinearMap.inr ℝ ℝ K10) y :=
        hasFDerivAt_prodMk_right t y
      have hGtderiv : HasFDerivAt (fun y => (G (t, y)).2)
          ((ContinuousLinearMap.snd ℝ ℝ F10).comp
            (L.comp (ContinuousLinearMap.inr ℝ ℝ K10))) y :=
        (ContinuousLinearMap.snd ℝ ℝ F10).hasFDerivAt.comp y
          (hGdiff.hasFDerivAt.comp y hprod_y)
      exact hGtderiv.fderiv
    constructor
    · intro hL v
      obtain ⟨u, hu⟩ := hL (0, v)
      have hs : u.1 = 0 := by
        have h1 : (L u).1 = ((0, v) : ℝ × F10).1 := congrArg Prod.fst hu
        rw [hLfst] at h1
        exact h1
      have hu_eq : u = ContinuousLinearMap.inr ℝ ℝ K10 u.2 := by
        refine Prod.ext ?_ ?_
        · exact hs
        · rfl
      have hLu : L (ContinuousLinearMap.inr ℝ ℝ K10 u.2) = (0, v) := by
        rw [← hu_eq]
        exact hu
      refine ⟨u.2, ?_⟩
      have h4 : (L (ContinuousLinearMap.inr ℝ ℝ K10 u.2)).2 = v :=
        congrArg Prod.snd hLu
      have h3 : (fderiv ℝ (fun y => (G (t, y)).2) y) u.2 = v := by
        rw [hGt_eq]
        exact h4
      exact h3
    · intro hGt w
      obtain ⟨s, v⟩ := w
      obtain ⟨y', hy'⟩ := hGt (v - (L (s, 0)).2)
      have hy2 : (L (ContinuousLinearMap.inr ℝ ℝ K10 y')).2 =
          v - (L (s, 0)).2 := by
        rw [hGt_eq] at hy'
        exact hy'
      refine ⟨(s, y'), ?_⟩
      refine Prod.ext ?_ ?_
      · have h5 := hLfst (s, y')
        exact h5
      · have hdecomp : (s, y') =
            (s, 0) + ContinuousLinearMap.inr ℝ ℝ K10 y' := by
          refine Prod.ext ?_ ?_ <;> simp
        rw [hdecomp, map_add]
        change (L (s, 0)).2 + (L (ContinuousLinearMap.inr ℝ ℝ K10 y')).2 = v
        rw [hy2]
        abel
  have hG1 : ContDiffOn ℝ 1 G W := hG.of_le (by simp)
  have hcompact : IsCompact (Q ∩ {z | ¬ Function.Surjective (fderiv ℝ G z)}) :=
    isCompact_inter_critPtsOn (ℝ × K10) (ℝ × F10) W hW G hG1 Q hQ hQW
  have hScompact : IsCompact
      (G '' (Q ∩ {z | ¬ Function.Surjective (fderiv ℝ G z)})) :=
    hcompact.image_of_continuousOn
      (hG.continuousOn.mono (Set.inter_subset_left.trans hQW))
  have hSmeas : MeasurableSet
      (G '' (Q ∩ {z | ¬ Function.Surjective (fderiv ℝ G z)})) :=
    hScompact.measurableSet
  have hsub : ∀ t : ℝ, Prod.mk t ⁻¹'
      (G '' (Q ∩ {z | ¬ Function.Surjective (fderiv ℝ G z)})) ⊆
      (fun y => (G (t, y)).2) ''
        critPtsOn (fun y => (G (t, y)).2) {y | (t, y) ∈ W} := by
    intro t v hv
    simp only [Set.mem_preimage] at hv
    obtain ⟨z, hzmem, hzEq⟩ := hv
    obtain ⟨hzQ, hzc⟩ := hzmem
    have hzW : z ∈ W := hQW hzQ
    have hfst_z := hGfst z hzW
    have hzt : z.1 = t := by
      have h1 : (G z).1 = ((t, v) : ℝ × F10).1 := congrArg Prod.fst hzEq
      rw [hfst_z] at h1
      exact h1
    have hz_eq : z = (t, z.2) := by
      refine Prod.ext ?_ ?_
      · exact hzt
      · rfl
    have hyW : (t, z.2) ∈ W := by
      rw [← hz_eq]
      exact hzW
    have hcrit : z.2 ∈ critPtsOn (fun y => (G (t, y)).2) {y | (t, y) ∈ W} := by
      rw [mem_critPtsOn]
      refine ⟨?_, ?_⟩
      · exact hyW
      · intro hsurj
        apply hzc
        have hi := (hslice_iff t z.2 hyW).mpr hsurj
        rw [hz_eq]
        exact hi
    have hvEq : (G (t, z.2)).2 = v := by
      have h1 : G z = (t, v) := hzEq
      rw [hz_eq] at h1
      exact congrArg Prod.snd h1
    exact ⟨z.2, hcrit, hvEq⟩
  have hnull : ∀ t : ℝ, μ' (Prod.mk t ⁻¹'
      (G '' (Q ∩ {z | ¬ Function.Surjective (fderiv ℝ G z)}))) = 0 := by
    intro t
    exact measure_mono_null (hsub t) (hslice t)
  rw [Measure.measure_prod_null hSmeas]
  exact Filter.Eventually.of_forall hnull

-- Helper N12: very flat points have null image via a Hölder estimate.
private theorem sard_step_very_flat
    {E12 : Type*} [NormedAddCommGroup E12] [NormedSpace ℝ E12]
    [FiniteDimensional ℝ E12]
    {F12 : Type*} [NormedAddCommGroup F12] [NormedSpace ℝ F12]
    [FiniteDimensional ℝ F12]
    [MeasurableSpace F12] [BorelSpace F12]
    (μ : Measure F12) [μ.IsAddHaarMeasure]
    (U : Set E12) (hU : IsOpen U) (g : E12 → F12) (hg : ContDiffOn ℝ ∞ g U)
    (K : ℕ)
    (hK : (Module.finrank ℝ E12 : ℝ) < ((K + 1 : ℕ) : ℝ) * Module.finrank ℝ F12)
    (xbar : E12) (hxbar : xbar ∈ flatPtsOn g U K) :
    ∃ V ∈ 𝓝 xbar, μ (g '' (V ∩ flatPtsOn g U K)) = 0 := by
  have hxU : xbar ∈ U := ((mem_flatPtsOn g U K xbar).mp hxbar).1
  obtain ⟨r, hrpos, hrball⟩ := Metric.isOpen_iff.mp hU xbar hxU
  set r2 : ℝ := r / 2 with hr2def
  have hr2pos : 0 < r2 := by linarith
  have hsub : Metric.closedBall xbar r2 ⊆ U := by
    intro z hz
    have hz' : dist z xbar ≤ r2 := hz
    have hlt : dist z xbar < r := lt_of_le_of_lt hz' (by linarith)
    exact hrball hlt
  have hQconv : Convex ℝ (Metric.closedBall xbar r2) :=
    convex_closedBall xbar r2
  have hcont : ContinuousOn (iteratedFDeriv ℝ (K + 1) g)
      (Metric.closedBall xbar r2) := by
    intro z hz
    have hzU : U ∈ 𝓝 z := hU.mem_nhds (hsub hz)
    have hcd : ContDiffAt ℝ ∞ g z := hg.contDiffAt hzU
    have hle : ((K + 1 : ℕ) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
      norm_cast
      exact le_top
    have hca := hcd.continuousAt_iteratedFDeriv hle
    exact hca.continuousWithinAt
  obtain ⟨B, hB⟩ :=
    (isCompact_closedBall xbar r2).exists_bound_of_continuousOn hcont
  have hxQ : xbar ∈ Metric.closedBall xbar r2 :=
    Metric.mem_closedBall_self (le_of_lt hr2pos)
  have hBnonneg : 0 ≤ B := le_trans (norm_nonneg _) (hB xbar hxQ)
  have hgK : ContDiffOn ℝ ((K + 1 : ℕ) : WithTop ℕ∞) g U :=
    hg.of_le (by norm_cast; exact le_top)
  have hHold : HolderOnWith (Real.toNNReal B) ((K + 1 : ℕ) : NNReal) g
      (Metric.closedBall xbar r2 ∩ flatPtsOn g U K) := by
    intro x hx y hy
    obtain ⟨hxQ, hxf⟩ := hx
    obtain ⟨hyQ, hyf⟩ := hy
    have hxflat : ∀ j, 1 ≤ j → j ≤ K → iteratedFDeriv ℝ j g x = 0 :=
      ((mem_flatPtsOn g U K x).mp hxf).2
    have hN4 := norm_sub_le_of_iteratedFDeriv_eq_zero U hU g K hgK
      (Metric.closedBall xbar r2) hQconv hsub B hB x hxQ hxflat y hyQ
    rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm,
      norm_sub_rev (g x) (g y)]
    have hle : ENNReal.ofReal ‖g y - g x‖ ≤
        ENNReal.ofReal (B * ‖y - x‖ ^ (K + 1)) :=
      ENNReal.ofReal_le_ofReal hN4
    rw [ENNReal.ofReal_mul hBnonneg] at hle
    have h1 : ((((K + 1 : ℕ) : NNReal)) : ℝ) = ((K + 1 : ℕ) : ℝ) := by simp
    rw [h1, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by positivity),
      Real.rpow_natCast, norm_sub_rev x y]
    exact hle
  have hr : 0 < ((K + 1 : ℕ) : NNReal) := by positivity
  have hdim : (Module.finrank ℝ E12 : ℝ) <
      (((K + 1 : ℕ) : NNReal) : ℝ) * Module.finrank ℝ F12 := by
    simpa using hK
  have hN3 := addHaar_image_null_of_holderOnWith μ g
    (Metric.closedBall xbar r2 ∩ flatPtsOn g U K)
    (Real.toNNReal B) ((K + 1 : ℕ) : NNReal) hr hHold hdim
  exact ⟨Metric.closedBall xbar r2, Metric.closedBall_mem_nhds xbar hr2pos, hN3⟩

-- Helper N14a: chart targets are open and the chart representative is smooth.
omit [FiniteDimensional ℝ E] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace (EuclideanSpace ℝ (Fin n))] [BorelSpace (EuclideanSpace ℝ (Fin n))] in
private theorem chart_target_open_smooth (x0 : M) (f : M → EuclideanSpace ℝ (Fin n))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (⊤ : ℕ∞) f) :
    IsOpen (extChartAt I x0).target ∧
      ContDiffOn ℝ ∞ (f ∘ ⇑(extChartAt I x0).symm) (extChartAt I x0).target := by
  refine ⟨isOpen_extChartAt_target x0, ?_⟩
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (↑(⊤ : ℕ∞))
      (f ∘ ⇑(extChartAt I x0).symm) (extChartAt I x0).target :=
    ContMDiffOn.comp hf.contMDiffOn (contMDiffOn_extChartAt_symm x0)
      (fun x _ => Set.mem_preimage.mpr (Set.mem_univ _))
  exact contMDiffOn_iff_contDiffOn.mp hcomp

-- Helper N14b: critical values in a chart come from Euclidean critical points.
omit [FiniteDimensional ℝ E] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace (EuclideanSpace ℝ (Fin n))] [BorelSpace (EuclideanSpace ℝ (Fin n))] in
private theorem image_criticalSet_inter_chart_subset (x0 : M)
    (f : M → EuclideanSpace ℝ (Fin n))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (⊤ : ℕ∞) f) :
    f '' (criticalSet (I := I) (M := M) (n := n) f ∩ (extChartAt I x0).source) ⊆
      (f ∘ ⇑(extChartAt I x0).symm) ''
        critPtsOn (f ∘ ⇑(extChartAt I x0).symm) (extChartAt I x0).target := by
  intro z hz
  obtain ⟨x, ⟨hxcrit, hxsrc⟩, rfl⟩ := hz
  have hxcrit' : ¬ Function.Surjective
      (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) f x) := hxcrit
  have hytgt : ⇑(extChartAt I x0) x ∈ (extChartAt I x0).target :=
    (extChartAt I x0).map_source hxsrc
  refine ⟨⇑(extChartAt I x0) x, ?_, ?_⟩
  · rw [mem_critPtsOn]
    refine ⟨hytgt, ?_⟩
    intro hsurj
    apply hxcrit'
    have hxsrc' : x ∈ (chartAt H x0).source := by
      rw [← extChartAt_source I x0]
      exact hxsrc
    have he_mdiff : MDiffAt (⇑(extChartAt I x0)) x :=
      mdifferentiableAt_extChartAt hxsrc'
    have he_has : HasMFDerivAt I 𝓘(ℝ, E) (⇑(extChartAt I x0)) x
        (mfderiv I 𝓘(ℝ, E) (⇑(extChartAt I x0)) x) :=
      MDifferentiableAt.hasMFDerivAt he_mdiff
    have hgsmooth := (chart_target_open_smooth x0 f hf).2
    have hg_diff : DifferentiableAt ℝ (f ∘ ⇑(extChartAt I x0).symm)
        (⇑(extChartAt I x0) x) :=
      (hgsmooth.contDiffAt ((isOpen_extChartAt_target x0).mem_nhds hytgt)).differentiableAt
        (by simp)
    have hg_has : HasFDerivAt (f ∘ ⇑(extChartAt I x0).symm)
        (fderiv ℝ (f ∘ ⇑(extChartAt I x0).symm) (⇑(extChartAt I x0) x))
        (⇑(extChartAt I x0) x) :=
      hg_diff.hasFDerivAt
    have hg_mf : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (f ∘ ⇑(extChartAt I x0).symm)
        (⇑(extChartAt I x0) x)
        (fderiv ℝ (f ∘ ⇑(extChartAt I x0).symm) (⇑(extChartAt I x0) x)) :=
      HasFDerivAt.hasMFDerivAt hg_has
    have hcomp : HasMFDerivAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        ((f ∘ ⇑(extChartAt I x0).symm) ∘ ⇑(extChartAt I x0)) x _ :=
      hg_mf.comp x he_has
    have heq : f =ᶠ[𝓝 x] (f ∘ ⇑(extChartAt I x0).symm) ∘ ⇑(extChartAt I x0) := by
      filter_upwards [(isOpen_extChartAt_source x0).mem_nhds hxsrc] with x' hx'
      exact congrArg f ((extChartAt I x0).left_inv hx').symm
    have hf_has := hcomp.congr_of_eventuallyEq_abuse heq
    have hmf := hf_has.mfderiv
    rw [hmf]
    have he_inv : (mfderiv I 𝓘(ℝ, E) (⇑(extChartAt I x0)) x).IsInvertible :=
      isInvertible_mfderiv_extChartAt hxsrc
    exact hsurj.comp he_inv.surjective
  · change f (⇑(extChartAt I x0).symm (⇑(extChartAt I x0) x)) = f x
    rw [(extChartAt I x0).left_inv hxsrc]

-- Bridge: first iterated derivative vanishes iff `fderiv` vanishes.
private theorem iteratedFDeriv_one_eq_zero_iff
    {E6 : Type*} [NormedAddCommGroup E6] [NormedSpace ℝ E6]
    {F6 : Type*} [NormedAddCommGroup F6] [NormedSpace ℝ F6]
    (g : E6 → F6) (x : E6) :
    iteratedFDeriv ℝ 1 g x = 0 ↔ fderiv ℝ g x = 0 := by
  constructor
  · intro h
    ext v
    have h1 : iteratedFDeriv ℝ 1 g x (fun _ => v) = 0 := by
      rw [h]
      rfl
    rw [iteratedFDeriv_one_apply] at h1
    exact h1
  · intro h
    ext m
    rw [iteratedFDeriv_one_apply]
    rw [h]
    rfl

-- Bridge: flat points of order `k ≥ 1` have vanishing `fderiv`.
private theorem fderiv_eq_zero_of_mem_flatPtsOn
    {E6 : Type*} [NormedAddCommGroup E6] [NormedSpace ℝ E6]
    {F6 : Type*} [NormedAddCommGroup F6] [NormedSpace ℝ F6]
    (g : E6 → F6) (U : Set E6) (k : ℕ) (hk : 1 ≤ k)
    (x : E6) (hx : x ∈ flatPtsOn g U k) :
    fderiv ℝ g x = 0 := by
  have h1 : iteratedFDeriv ℝ 1 g x = 0 :=
    ((mem_flatPtsOn g U k x).mp hx).2 1 le_rfl hk
  exact (iteratedFDeriv_one_eq_zero_iff g x).mp h1

-- Bridge: zero map is not surjective when target has positive finrank.
private theorem not_surjective_zero_of_finrank_pos
    (E7 : Type*) [NormedAddCommGroup E7] [NormedSpace ℝ E7]
    (F7 : Type*) [NormedAddCommGroup F7] [NormedSpace ℝ F7]
    [FiniteDimensional ℝ F7]
    (hpos : 0 < Module.finrank ℝ F7) :
    ¬ Function.Surjective (0 : E7 →L[ℝ] F7) := by
  have := Module.nontrivial_of_finrank_pos (R := ℝ) (M := F7) hpos
  obtain ⟨a, b, hab⟩ := exists_pair_ne F7
  have hex : ∃ y : F7, y ≠ 0 := by
    by_cases ha : a = 0
    · exact ⟨b, by rw [ha] at hab; exact Ne.symm hab⟩
    · exact ⟨a, ha⟩
  obtain ⟨y, hy⟩ := hex
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj y
  have h0 : (0 : E7 →L[ℝ] F7) x = 0 := rfl
  rw [h0] at hx
  exact hy hx.symm

-- Euclidean Sard predicate for a fixed domain `E`.
private def SardProp (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : Prop :=
  ∀ (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]
    (U : Set E), IsOpen U → ∀ (g : E → F), ContDiffOn ℝ ∞ g U →
    μ (g '' critPtsOn g U) = 0

-- Step 3: very flat points have null image (no induction hypothesis needed).
private theorem sard_step_flat_very_flat_null
    {E12 : Type*} [NormedAddCommGroup E12] [NormedSpace ℝ E12]
    [FiniteDimensional ℝ E12]
    {F12 : Type*} [NormedAddCommGroup F12] [NormedSpace ℝ F12]
    [FiniteDimensional ℝ F12]
    [MeasurableSpace F12] [BorelSpace F12]
    (μ : Measure F12) [μ.IsAddHaarMeasure]
    (U : Set E12) (hU : IsOpen U) (g : E12 → F12) (hg : ContDiffOn ℝ ∞ g U)
    (K : ℕ)
    (hK : (Module.finrank ℝ E12 : ℝ) < ((K + 1 : ℕ) : ℝ) * Module.finrank ℝ F12) :
    μ (g '' flatPtsOn g U K) = 0 := by
  have hloc : ∀ x ∈ flatPtsOn g U K, ∃ V ∈ 𝓝 x,
      μ (g '' (V ∩ flatPtsOn g U K)) = 0 :=
    fun x hx => sard_step_very_flat μ U hU g hg K hK x hx
  exact MathlibExt.MeasureTheory.measure_image_null_of_locally_null hloc

-- Step 1 (statement): non-flat critical points have null image, assuming Sard
-- for all strictly smaller domains.
private theorem sard_step_one_aux
    {E13 : Type u} [NormedAddCommGroup E13] [NormedSpace ℝ E13]
    [FiniteDimensional ℝ E13]
    (IH : ∀ (K : Type u) [NormedAddCommGroup K] [NormedSpace ℝ K]
      [FiniteDimensional ℝ K], Module.finrank ℝ K < Module.finrank ℝ E13 →
      SardProp.{u, v} K)
    {F13 : Type v} [NormedAddCommGroup F13] [NormedSpace ℝ F13]
    [FiniteDimensional ℝ F13]
    [MeasurableSpace F13] [BorelSpace F13]
    (μ : Measure F13) [μ.IsAddHaarMeasure]
    (U : Set E13) (hU : IsOpen U) (g : E13 → F13) (hg : ContDiffOn ℝ ∞ g U) :
    μ (g '' (critPtsOn g U \ flatPtsOn g U 1)) = 0 := by
  by_cases hF0 : Module.finrank ℝ F13 = 0
  · have hsub : Subsingleton F13 := Module.finrank_zero_iff.mp hF0
    have hemptyCrit : critPtsOn g U = ∅ := by
      ext x
      simp only [mem_critPtsOn, Set.mem_empty_iff_false, iff_false]
      intro hx
      have hsurj : Function.Surjective (fderiv ℝ g x) := by
        intro y
        have hy0 : y = 0 := Subsingleton.elim y 0
        refine ⟨0, ?_⟩
        simp only [hy0, map_zero]
      exact hx.2 hsurj
    have hempty : critPtsOn g U \ flatPtsOn g U 1 = ∅ := by
      rw [hemptyCrit, Set.empty_sdiff]
    rw [hempty, Set.image_empty]
    exact measure_empty
  · have hloc : ∀ x ∈ critPtsOn g U \ flatPtsOn g U 1, ∃ V ∈ 𝓝 x,
        μ (g '' (V ∩ (critPtsOn g U \ flatPtsOn g U 1))) = 0 := by
      intro x hx
      obtain ⟨hxcrit, hxnonflat⟩ := hx
      obtain ⟨hxU, hxcrit_ne⟩ := (mem_critPtsOn g U x).mp hxcrit
      have hD1ne : iteratedFDeriv ℝ 1 g x ≠ 0 := by
        intro hcon
        apply hxnonflat
        rw [mem_flatPtsOn]
        refine ⟨hxU, fun j h1 hj => ?_⟩
        have hj1 : j = 1 := by omega
        rw [hj1]
        exact hcon
      have hfderiv_ne : fderiv ℝ g x ≠ 0 := by
        intro hcon
        apply hD1ne
        exact (iteratedFDeriv_one_eq_zero_iff g x).mpr hcon
      obtain ⟨v, hv⟩ : ∃ v, fderiv ℝ g x v ≠ 0 := by
        by_contra hcon
        push Not at hcon
        apply hfderiv_ne
        ext w
        simpa using hcon w
      obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_ne_zero (R := ℝ) hv
      set w : E13 → ℝ := fun y => ℓ (g y) with hw_def
      have hw : ContDiffOn ℝ ∞ w U := ℓ.contDiff.fun_comp_contDiffOn hg
      have hg_diff : DifferentiableAt ℝ g x :=
        (hg.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
      have hℓ_diff : DifferentiableAt ℝ (⇑ℓ) (g x) := ℓ.differentiableAt
      have hder : fderiv ℝ w x = ℓ.comp (fderiv ℝ g x) := by
        simp only [hw_def, fderiv_fun_comp x hℓ_diff hg_diff, ℓ.fderiv]
      have hne : fderiv ℝ w x ≠ 0 := by
        intro hcon
        apply hℓ
        have h0 : fderiv ℝ w x v = 0 := by
          rw [hcon]
          rfl
        rw [hder] at h0
        simpa using h0
      obtain ⟨h, hxsrc, hsrcU, hfst, hsymm_smooth, hsymm_deriv, hfin⟩ :=
        exists_straightening_chart U hU w hw x hxU hne
      let K := LinearMap.ker (fderiv ℝ w x : E13 →ₗ[ℝ] ℝ)
      have hℓne : ℓ ≠ 0 := by
        intro hcon
        apply hℓ
        rw [hcon]
        rfl
      obtain ⟨A, hA1, -⟩ := exists_equiv_prod_ker_of_ne_zero F13 ℓ hℓne
      let L := LinearMap.ker (ℓ : F13 →ₗ[ℝ] ℝ)
      set W := h.target with hW_def
      have hW : IsOpen W := h.open_target
      set G := fun z : ℝ × ↥K => A (g (h.symm z)) with hG_def
      have hmaps : Set.MapsTo (⇑h.symm) W U := fun z hz => hsrcU (h.map_target hz)
      have hcomp1 : ContDiffOn ℝ ∞ (fun z : ℝ × ↥K => g (h.symm z)) W :=
        hg.comp hsymm_smooth hmaps
      have hG : ContDiffOn ℝ ∞ G W := A.contDiff.fun_comp_contDiffOn hcomp1
      have hGfst : ∀ z ∈ W, (G z).1 = z.1 := by
        intro z hz
        change (A (g (h.symm z))).1 = z.1
        rw [hA1]
        have hsymm_src : h.symm z ∈ h.source := h.map_target hz
        have h1 : (h (h.symm z)).1 = w (h.symm z) := hfst _ hsymm_src
        have h2 : h (h.symm z) = z := h.right_inv hz
        rw [h2] at h1
        simp only [hw_def] at h1
        exact h1.symm
      have hltK : Module.finrank ℝ ↥K < Module.finrank ℝ E13 := by
        have hfin' : Module.finrank ℝ ↥K + 1 = Module.finrank ℝ E13 := hfin
        omega
      have hSardK : SardProp.{u, v} (↥K) := IH _ hltK
      borelize ↥L
      have hslice : ∀ t : ℝ, (Measure.addHaar : Measure ↥L)
          ((fun y : ↥K => (G (t, y)).2) ''
            critPtsOn (fun y : ↥K => (G (t, y)).2) {y | (t, y) ∈ W}) = 0 := by
        intro t
        have hOt_open : IsOpen {y : ↥K | (t, y) ∈ W} :=
          hW.preimage (continuous_const.prodMk continuous_id)
        have hmaps_t : Set.MapsTo (fun y : ↥K => (t, y)) {y | (t, y) ∈ W} W :=
          fun y hy => hy
        have hcomp_t : ContDiffOn ℝ ∞ (fun y : ↥K => G (t, y)) {y | (t, y) ∈ W} :=
          hG.comp (contDiff_prodMk_right t).contDiffOn hmaps_t
        have hGt_smooth : ContDiffOn ℝ ∞ (fun y : ↥K => (G (t, y)).2)
            {y | (t, y) ∈ W} :=
          (ContinuousLinearMap.snd ℝ ℝ ↥L).contDiff.fun_comp_contDiffOn hcomp_t
        exact hSardK ↥L (Measure.addHaar : Measure ↥L) _ hOt_open _ hGt_smooth
      have hhxW : h x ∈ W := h.map_source hxsrc
      obtain ⟨r, hrpos, hrball⟩ := Metric.isOpen_iff.mp hW _ hhxW
      set r2 := r / 2 with hr2_def
      have hr2pos : 0 < r2 := by linarith
      have hQW : Metric.closedBall (h x) r2 ⊆ W :=
        (Metric.closedBall_subset_ball (by linarith)).trans hrball
      have hQcompact : IsCompact (Metric.closedBall (h x) r2) :=
        isCompact_closedBall _ _
      have hnull_prod : (volume.prod (Measure.addHaar : Measure ↥L))
          (G '' (Metric.closedBall (h x) r2 ∩
            {z | ¬ Function.Surjective (fderiv ℝ G z)})) = 0 :=
        prod_null_image_critPts_of_slices (Measure.addHaar : Measure ↥L) W hW G hG
          hGfst hslice _ hQcompact hQW
      have hQmem : Metric.closedBall (h x) r2 ∈ 𝓝 (h x) :=
        Metric.closedBall_mem_nhds _ hr2pos
      have hhx_interior : h x ∈ interior (Metric.closedBall (h x) r2) :=
        mem_interior_iff_mem_nhds.mpr hQmem
      have hVmem : h.source ∩ h ⁻¹' (interior (Metric.closedBall (h x) r2)) ∈ 𝓝 x :=
        Filter.inter_mem (h.open_source.mem_nhds hxsrc)
          ((h.continuousAt hxsrc).preimage_mem_nhds
            (isOpen_interior.mem_nhds hhx_interior))
      refine ⟨h.source ∩ h ⁻¹' (interior (Metric.closedBall (h x) r2)), hVmem, ?_⟩
      have hsub : (⇑A) '' (g '' ((h.source ∩ h ⁻¹' (interior (Metric.closedBall (h x) r2))) ∩
          (critPtsOn g U \ flatPtsOn g U 1))) ⊆
          G '' (Metric.closedBall (h x) r2 ∩
            {z | ¬ Function.Surjective (fderiv ℝ G z)}) := by
        intro w hw
        simp only [Set.mem_image] at hw ⊢
        obtain ⟨u, hu, rfl⟩ := hw
        obtain ⟨y, hy, rfl⟩ := hu
        obtain ⟨⟨hy_src, hy_pre⟩, hy_crit, -⟩ := hy
        have hyQ : h y ∈ Metric.closedBall (h x) r2 := interior_subset hy_pre
        have hyW : h y ∈ W := hQW hyQ
        obtain ⟨_, hy_nsurj⟩ := (mem_critPtsOn g U y).mp hy_crit
        refine ⟨h y, ⟨hyQ, ?_⟩, ?_⟩
        · intro hsurj
          apply hy_nsurj
          have hzW : (h y : ℝ × ↥K) ∈ W := h.map_source hy_src
          obtain ⟨e, he⟩ := hsymm_deriv _ hzW
          have hyU : y ∈ U := hsrcU hy_src
          have hg_diff_y : DifferentiableAt ℝ g y :=
            (hg.contDiffAt (hU.mem_nhds hyU)).differentiableAt (by simp)
          have hsymm_y : h.symm (h y) = y := h.left_inv hy_src
          have hg2 : DifferentiableAt ℝ g (h.symm (h y)) := by
            rw [hsymm_y]
            exact hg_diff_y
          have hiff := surjective_fderiv_equiv_comp_comp_iff _ _ _ _ (⇑h.symm) (h y)
            e he g hg2 A
          have hGeq : (⇑A ∘ g ∘ ⇑h.symm : ℝ × ↥K → ℝ × ↥L) = G := rfl
          rw [hGeq, hsymm_y] at hiff
          exact hiff.mp hsurj
        · show G (h y) = A (g y)
          have hleft : h.symm (h y) = y := h.left_inv hy_src
          simp only [hG_def, hleft]
      have hnull_A : (volume.prod (Measure.addHaar : Measure ↥L))
          ((⇑A) '' (g '' ((h.source ∩ h ⁻¹' (interior (Metric.closedBall (h x) r2))) ∩
            (critPtsOn g U \ flatPtsOn g U 1)))) = 0 :=
        measure_mono_null hsub hnull_prod
      have hiff := addHaar_image_equiv_null_iff F13 (ℝ × ↥L) μ
        (volume.prod (Measure.addHaar : Measure ↥L)) A
        (g '' ((h.source ∩ h ⁻¹' (interior (Metric.closedBall (h x) r2))) ∩
          (critPtsOn g U \ flatPtsOn g U 1)))
      exact hiff.mp hnull_A
    exact MathlibExt.MeasureTheory.measure_image_null_of_locally_null hloc

-- Step 2 (statement): flat differences have null image, assuming Sard
-- for all strictly smaller domains.
private theorem sard_step_two_aux
    {E13 : Type u} [NormedAddCommGroup E13] [NormedSpace ℝ E13]
    [FiniteDimensional ℝ E13]
    (IH : ∀ (K : Type u) [NormedAddCommGroup K] [NormedSpace ℝ K]
      [FiniteDimensional ℝ K], Module.finrank ℝ K < Module.finrank ℝ E13 →
      SardProp.{u, v} K)
    {F13 : Type v} [NormedAddCommGroup F13] [NormedSpace ℝ F13]
    [FiniteDimensional ℝ F13]
    [MeasurableSpace F13] [BorelSpace F13]
    (μ : Measure F13) [μ.IsAddHaarMeasure]
    (U : Set E13) (hU : IsOpen U) (g : E13 → F13) (hg : ContDiffOn ℝ ∞ g U)
    (k : ℕ) (hk : 1 ≤ k) :
    μ (g '' (flatPtsOn g U k \ flatPtsOn g U (k + 1))) = 0 := by
  by_cases hF0 : Module.finrank ℝ F13 = 0
  · have hsub : Subsingleton F13 := Module.finrank_zero_iff.mp hF0
    have hss : flatPtsOn g U k ⊆ flatPtsOn g U (k + 1) := by
      intro x hx
      obtain ⟨hxU, -⟩ := (mem_flatPtsOn g U k x).mp hx
      rw [mem_flatPtsOn]
      refine ⟨hxU, fun j _ _ => ?_⟩
      ext m
      exact Subsingleton.elim _ _
    have hempty : flatPtsOn g U k \ flatPtsOn g U (k + 1) = ∅ :=
      Set.sdiff_eq_empty.mpr hss
    rw [hempty, Set.image_empty]
    exact measure_empty
  · have hFpos : 0 < Module.finrank ℝ F13 := Nat.pos_of_ne_zero hF0
    have hloc : ∀ x ∈ flatPtsOn g U k \ flatPtsOn g U (k + 1), ∃ V ∈ 𝓝 x,
        μ (g '' (V ∩ (flatPtsOn g U k \ flatPtsOn g U (k + 1)))) = 0 := by
      intro x hx
      obtain ⟨hxflat, hxnonflat⟩ := hx
      obtain ⟨hxU, hflat⟩ := (mem_flatPtsOn g U k x).mp hxflat
      have hDk1ne : iteratedFDeriv ℝ (k + 1) g x ≠ 0 := by
        intro hcon
        apply hxnonflat
        rw [mem_flatPtsOn]
        refine ⟨hxU, fun j h1 hj => ?_⟩
        by_cases hjk : j ≤ k
        · exact hflat j h1 hjk
        · have hjk1 : j = k + 1 := by omega
          rw [hjk1]
          exact hcon
      obtain ⟨m, hm⟩ : ∃ m : Fin (k + 1) → E13,
          iteratedFDeriv ℝ (k + 1) g x m ≠ 0 := by
        by_contra hcon
        apply hDk1ne
        ext m
        have h2 : iteratedFDeriv ℝ (k + 1) g x m = 0 := by
          by_contra h
          exact hcon ⟨m, h⟩
        simpa using h2
      obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_ne_zero (R := ℝ) hm
      have hW : ContDiffOn ℝ ∞ (iteratedFDerivWithin ℝ k g U) U := by
        intro y hy
        exact ((hg y hy).iteratedFDerivWithin_right hU.uniqueDiffOn (by simp) hy)
      have heq : Set.EqOn (iteratedFDerivWithin ℝ k g U)
          (iteratedFDeriv ℝ k g) U :=
        iteratedFDerivWithin_of_isOpen k hU
      have hDk : ContDiffOn ℝ ∞ (iteratedFDeriv ℝ k g) U :=
        hW.congr (fun x hx => (heq hx).symm)
      set L : ContinuousMultilinearMap ℝ (fun _ : Fin k => E13) F13 →L[ℝ] ℝ :=
        ℓ.comp (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E13) F13
          (Fin.tail m)) with hL_def
      set w : E13 → ℝ := fun y => L (iteratedFDeriv ℝ k g y) with hw_def
      have hw : ContDiffOn ℝ ∞ w U := L.contDiff.fun_comp_contDiffOn hDk
      have hwflat : ∀ y ∈ flatPtsOn g U k, w y = 0 := by
        intro y hy
        have hDk0 : iteratedFDeriv ℝ k g y = 0 :=
          ((mem_flatPtsOn g U k y).mp hy).2 k hk le_rfl
        simp only [hw_def, hDk0, L.map_zero]
      have hDk_diff : DifferentiableAt ℝ (iteratedFDeriv ℝ k g) x :=
        (hDk.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
      have hL_diff : DifferentiableAt ℝ (⇑L) ((iteratedFDeriv ℝ k g) x) :=
        L.differentiableAt
      have hder : fderiv ℝ w x =
          L.comp (fderiv ℝ (iteratedFDeriv ℝ k g) x) := by
        simp only [hw_def, fderiv_fun_comp x hL_diff hDk_diff, L.fderiv]
      have hval : fderiv ℝ w x (m 0) =
          ℓ (iteratedFDeriv ℝ (k + 1) g x m) := by
        have hrr : (fderiv ℝ (iteratedFDeriv ℝ k g) x) (m 0) (Fin.tail m) =
            iteratedFDeriv ℝ (k + 1) g x m :=
          (iteratedFDeriv_succ_apply_left m).symm
        rw [hder, hL_def]
        simp only [ContinuousLinearMap.comp_apply,
          ContinuousMultilinearMap.apply_apply]
        exact congrArg ℓ hrr
      have hne : fderiv ℝ w x ≠ 0 := by
        intro hcon
        apply hℓ
        have h0 : fderiv ℝ w x (m 0) = 0 := by
          rw [hcon]
          rfl
        rw [hval] at h0
        exact h0
      obtain ⟨h, hxsrc, hsrcU, hfst, hsymm_smooth, -, hfin⟩ :=
        exists_straightening_chart U hU w hw x hxU hne
      let K := LinearMap.ker (fderiv ℝ w x : E13 →ₗ[ℝ] ℝ)
      have hltK : Module.finrank ℝ ↥K < Module.finrank ℝ E13 := by
        have hfin' : Module.finrank ℝ ↥K + 1 = Module.finrank ℝ E13 := hfin
        omega
      have hSardK : SardProp.{u, v} (↥K) := IH _ hltK
      set O : Set ↥K := {y | (0, y) ∈ h.target}
      have hO : IsOpen O :=
        h.open_target.preimage (continuous_const.prodMk continuous_id)
      set φ : ↥K → E13 := fun y => h.symm (0, y) with hφ_def
      have hmaps_slice : Set.MapsTo (fun y : ↥K => (0, y)) O h.target :=
        fun y hy => hy
      have hφ_smooth : ContDiffOn ℝ ∞ φ O :=
        hsymm_smooth.comp (contDiff_prodMk_right (0 : ℝ)).contDiffOn hmaps_slice
      have hmaps_φ : Set.MapsTo φ O U := fun y hy => hsrcU (h.map_target hy)
      set s : ↥K → F13 := fun y => g (φ y) with hs_def
      have hs_smooth : ContDiffOn ℝ ∞ s O := hg.comp hφ_smooth hmaps_φ
      have hnull : μ (s '' critPtsOn s O) = 0 :=
        hSardK F13 μ O hO s hs_smooth
      have hsub : g '' (h.source ∩ (flatPtsOn g U k \ flatPtsOn g U (k + 1))) ⊆
          s '' critPtsOn s O := by
        intro z hz
        obtain ⟨y0, ⟨hy0src, hy0flat, -⟩, rfl⟩ := hz
        have hwy0 : w y0 = 0 := hwflat y0 hy0flat
        have h1y0 : (h y0).1 = 0 := (hfst y0 hy0src).trans hwy0
        have hhy0 : h y0 = (0, (h y0).2) := Prod.ext h1y0 rfl
        have hy2O : (h y0).2 ∈ O := by
          change (0, (h y0).2) ∈ h.target
          rw [← hhy0]
          exact h.map_source hy0src
        have hφy2 : φ (h y0).2 = y0 := by
          simp only [hφ_def]
          rw [← hhy0]
          exact h.left_inv hy0src
        have hφ_diff : DifferentiableAt ℝ φ (h y0).2 :=
          (hφ_smooth.contDiffAt (hO.mem_nhds hy2O)).differentiableAt (by simp)
        have hg_diff : DifferentiableAt ℝ g (φ (h y0).2) :=
          (hg.contDiffAt (hU.mem_nhds (hmaps_φ hy2O))).differentiableAt (by simp)
        have hder_s : fderiv ℝ s (h y0).2 =
            (fderiv ℝ g (φ (h y0).2)).comp (fderiv ℝ φ (h y0).2) :=
          fderiv_comp (f := φ) (g := g) ((h y0).2) hg_diff hφ_diff
        have hg0 : fderiv ℝ g (φ (h y0).2) = 0 := by
          rw [hφy2]
          exact fderiv_eq_zero_of_mem_flatPtsOn g U k hk y0 hy0flat
        have hfs0 : fderiv ℝ s (h y0).2 = 0 := by
          rw [hder_s, hg0]
          exact ContinuousLinearMap.zero_comp _
        have hnsurj : ¬ Function.Surjective (fderiv ℝ s (h y0).2) := by
          rw [hfs0]
          exact not_surjective_zero_of_finrank_pos _ _ hFpos
        have hmem : (h y0).2 ∈ critPtsOn s O := by
          rw [mem_critPtsOn]
          exact ⟨hy2O, hnsurj⟩
        have hsy2 : s (h y0).2 = g y0 := by
          simp only [hs_def, hφy2]
        exact ⟨(h y0).2, hmem, hsy2⟩
      refine ⟨h.source, h.open_source.mem_nhds hxsrc, ?_⟩
      exact measure_mono_null hsub hnull
    exact MathlibExt.MeasureTheory.measure_image_null_of_locally_null hloc

-- Node N13 induction: Sard holds for domains of finrank `m`.
private theorem sard_euclidean_aux : ∀ (m : ℕ)
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
    Module.finrank ℝ E = m → SardProp E := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro E _ _ _ hrank F _ _ _ _ _ μ _ U hU g hg
    have IH : ∀ (K : Type u) [NormedAddCommGroup K] [NormedSpace ℝ K]
        [FiniteDimensional ℝ K],
        Module.finrank ℝ K < Module.finrank ℝ E → SardProp K := by
      intro K _ _ _ hlt
      have hlt' : Module.finrank ℝ K < m := by
        rw [← hrank]
        exact hlt
      exact ih (Module.finrank ℝ K) hlt' K rfl
    by_cases hF0 : Module.finrank ℝ F = 0
    · have _hsub : Subsingleton F := Module.finrank_zero_iff.mp hF0
      have hempty : critPtsOn g U = ∅ := by
        ext x
        simp only [mem_critPtsOn, Set.mem_empty_iff_false, iff_false]
        intro hx
        have hsurj : Function.Surjective (fderiv ℝ g x) := by
          intro y
          have hy0 : y = 0 := Subsingleton.elim y 0
          refine ⟨0, ?_⟩
          simp only [hy0, map_zero]
        exact hx.2 hsurj
      rw [hempty, Set.image_empty]
      exact measure_empty
    · have hpos : 0 < Module.finrank ℝ F := Nat.pos_of_ne_zero hF0
      have hKineq : (Module.finrank ℝ E : ℝ) <
          ((Module.finrank ℝ E + 1 : ℕ) : ℝ) * Module.finrank ℝ F := by
        have hn : (1 : ℝ) ≤ (Module.finrank ℝ F : ℝ) := by exact_mod_cast hpos
        have hcast : ((Module.finrank ℝ E + 1 : ℕ) : ℝ) =
            (Module.finrank ℝ E : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        have hnonneg : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) + 1 := by positivity
        have hle : ((Module.finrank ℝ E : ℝ) + 1) * 1 ≤
            ((Module.finrank ℝ E : ℝ) + 1) * (Module.finrank ℝ F : ℝ) :=
          mul_le_mul_of_nonneg_left hn hnonneg
        have hlt : (Module.finrank ℝ E : ℝ) < (Module.finrank ℝ E : ℝ) + 1 := by
          linarith
        calc (Module.finrank ℝ E : ℝ) < ((Module.finrank ℝ E : ℝ) + 1) * 1 := by
              simp only [mul_one]
              exact hlt
          _ ≤ ((Module.finrank ℝ E : ℝ) + 1) * (Module.finrank ℝ F : ℝ) := hle
      have hStep3 := sard_step_flat_very_flat_null μ U hU g hg
        (Module.finrank ℝ E) hKineq
      by_cases hE0 : Module.finrank ℝ E = 0
      · have hsub : critPtsOn g U ⊆ flatPtsOn g U (Module.finrank ℝ E) := by
          rw [hE0, flatPtsOn_zero]
          intro x hx
          exact ((mem_critPtsOn g U x).mp hx).1
        have himg : g '' critPtsOn g U ⊆
            g '' flatPtsOn g U (Module.finrank ℝ E) :=
          Set.image_mono hsub
        exact measure_mono_null himg hStep3
      · have hKpos : 1 ≤ Module.finrank ℝ E := Nat.one_le_iff_ne_zero.mpr hE0
        have hdesc : ∀ d k, 1 ≤ k → k + d = Module.finrank ℝ E →
            μ (g '' flatPtsOn g U k) = 0 := by
          intro d
          induction d with
          | zero =>
            intro k _ hkd
            have hkK : k = Module.finrank ℝ E := by omega
            rw [hkK]
            exact hStep3
          | succ d ihd =>
            intro k hk1 hkd
            have hk1' : 1 ≤ k + 1 := by omega
            have hkd' : (k + 1) + d = Module.finrank ℝ E := by omega
            have hnext := ihd (k + 1) hk1' hkd'
            have hdiff := sard_step_two_aux (E13 := E) IH μ U hU g hg k hk1
            have hsub : flatPtsOn g U k ⊆
                (flatPtsOn g U k \ flatPtsOn g U (k + 1)) ∪
                  flatPtsOn g U (k + 1) :=
              Set.subset_sdiff_union _ _
            have himg : g '' flatPtsOn g U k ⊆
                g '' (flatPtsOn g U k \ flatPtsOn g U (k + 1)) ∪
                  g '' flatPtsOn g U (k + 1) := by
              rw [← Set.image_union]
              exact Set.image_mono hsub
            have hunion : μ (g '' (flatPtsOn g U k \ flatPtsOn g U (k + 1)) ∪
                g '' flatPtsOn g U (k + 1)) = 0 :=
              measure_union_null hdiff hnext
            exact measure_mono_null himg hunion
        have hflat1 : μ (g '' flatPtsOn g U 1) = 0 := by
          have h : 1 + (Module.finrank ℝ E - 1) = Module.finrank ℝ E := by omega
          exact hdesc (Module.finrank ℝ E - 1) 1 le_rfl h
        have hStep1 := sard_step_one_aux (E13 := E) IH μ U hU g hg
        have hsub : critPtsOn g U ⊆
            (critPtsOn g U \ flatPtsOn g U 1) ∪ flatPtsOn g U 1 :=
          Set.subset_sdiff_union _ _
        have himg : g '' critPtsOn g U ⊆
            g '' (critPtsOn g U \ flatPtsOn g U 1) ∪ g '' flatPtsOn g U 1 := by
          rw [← Set.image_union]
          exact Set.image_mono hsub
        have hunion : μ (g '' (critPtsOn g U \ flatPtsOn g U 1) ∪
            g '' flatPtsOn g U 1) = 0 :=
          measure_union_null hStep1 hflat1
        exact measure_mono_null himg hunion

-- Node N13: Euclidean Sard theorem.
private theorem sard_euclidean
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (U : Set E) (hU : IsOpen U) (g : E → F) (hg : ContDiffOn ℝ ∞ g U) :
    μ (g '' critPtsOn g U) = 0 := by
  have h := sard_euclidean_aux (Module.finrank ℝ E) E rfl F μ U hU g hg
  exact h

/-- **Sard's theorem on open subsets of finite-dimensional spaces.** Let $E$ and $F$ be
finite-dimensional real normed spaces, let $\mu$ be an additive Haar measure on $F$ with its Borel
$\sigma$-algebra, let $U \subseteq E$ be open, and let $g : E \to F$ be $C^\infty$ on $U$. Then the
image under $g$ of the set of points $x \in U$ at which the derivative of $g$ is not surjective has
$\mu$-measure zero. -/
theorem sard_euclidean_open
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (U : Set E) (hU : IsOpen U) (g : E → F) (hg : ContDiffOn ℝ ∞ g U) :
    μ (g '' {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ g x)}) = 0 := by
  have h := sard_euclidean E F μ U hU g hg
  have heq : critPtsOn g U = {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ g x)} := rfl
  rw [heq] at h
  exact h

/--
**Sard's theorem for maps into Euclidean space.** Let $M$ be a Hausdorff, second-countable smooth
manifold without boundary modelled on a finite-dimensional real normed space, and let
$f : M \to \mathbb{R}^n$ be a $C^\infty$ map. Then the set of critical values of $f$, the image
under $f$ of the points of $M$ at which the manifold derivative of $f$ is not surjective, has
Lebesgue measure zero.

Proves `Wanted` entry `sard_theorem`.

Source: A. Sard, Bull. Amer. Math. Soc.
48 (1942) 883–890 measure of critical values; J. Lee, Introduction to Smooth Manifolds, 2nd ed.;
Guillemin-Pollack, Differential Topology; Lean states finite-dimensional manifold to
`EuclideanSpace ℝ (Fin n)` specialization.
-/
theorem sard_theorem
    (f : M → EuclideanSpace ℝ (Fin n))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (⊤ : ℕ∞) f) :
    volume (criticalValues (I := I) (M := M) (n := n) f) = 0 := by
  have := (inferInstance : T2Space M)
  unfold criticalValues
  refine MathlibExt.MeasureTheory.measure_image_null_of_locally_null ?_
  intro x0 _hx0
  refine ⟨(extChartAt I x0).source, extChartAt_source_mem_nhds (I := I) x0, ?_⟩
  have hsub : f '' ((extChartAt I x0).source ∩ criticalSet (I := I) (M := M) (n := n) f) ⊆
      (f ∘ ⇑(extChartAt I x0).symm) ''
        critPtsOn (f ∘ ⇑(extChartAt I x0).symm) (extChartAt I x0).target := by
    rw [Set.inter_comm]
    exact image_criticalSet_inter_chart_subset x0 f hf
  have hopen : IsOpen (extChartAt I x0).target :=
    (chart_target_open_smooth x0 f hf).1
  have hsmooth : ContDiffOn ℝ ∞ (f ∘ ⇑(extChartAt I x0).symm)
      (extChartAt I x0).target :=
    (chart_target_open_smooth x0 f hf).2
  have hnull : volume ((f ∘ ⇑(extChartAt I x0).symm) ''
      critPtsOn (f ∘ ⇑(extChartAt I x0).symm) (extChartAt I x0).target) = 0 :=
    sard_euclidean E (EuclideanSpace ℝ (Fin n)) volume _ hopen _ hsmooth
  exact measure_mono_null hsub hnull

end MathlibExt.Geometry.Manifold.SardWanted
end
end
