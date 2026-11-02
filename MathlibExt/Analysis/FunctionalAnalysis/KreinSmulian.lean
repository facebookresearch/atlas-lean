/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Data.List.GetD
import Mathlib.Basic.Real.Sign
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.BanachSpaceWanted

open Set Metric

open scoped ComplexConjugate ZeroAtInfty

/-! # Krein–Šmulian theorem -/

/-- Real polar of a set `F ⊆ E`: functionals whose real part is at most `1` on `F`. -/
private def ks_rpol {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (F : Set E) : Set (WeakDual 𝕜 E) :=
  {φ | ∀ x ∈ F, RCLike.re (φ x) ≤ 1}

/-- Real polar of a ball: control of real parts on a ball bounds the dual norm. -/
private lemma ks_norm_le_of_rpol {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {ρ : ℝ} (hρ : 0 < ρ) {φ : WeakDual 𝕜 E}
    (h : ∀ x : E, ‖x‖ ≤ ρ → RCLike.re (φ x) ≤ 1) :
    ‖WeakDual.toStrongDual φ‖ ≤ ρ⁻¹ := by
  have hnorm : ∀ x : E, x ∈ closedBall (0 : E) ρ → ‖φ x‖ ≤ 1 := by
    intro x hx
    rw [mem_closedBall_zero_iff] at hx
    by_cases hzx : φ x = 0
    · rw [hzx, norm_zero]
      exact zero_le_one
    · have hnpos : 0 < ‖φ x‖ := norm_pos_iff.mpr hzx
      have hne : ((‖φ x‖ : ℝ) : 𝕜) ≠ 0 :=
        RCLike.ofReal_ne_zero.mpr (ne_of_gt hnpos)
      have hrot : φ ((conj (φ x) / ((‖φ x‖ : ℝ) : 𝕜)) • x) = ((‖φ x‖ : ℝ) : 𝕜) := by
        have e1 : φ ((conj (φ x) / ((‖φ x‖ : ℝ) : 𝕜)) • x)
            = (conj (φ x) / ((‖φ x‖ : ℝ) : 𝕜)) * φ x := by
          rw [map_smul, smul_eq_mul]
        rw [e1, div_mul_eq_mul_div, RCLike.conj_mul, sq, mul_div_cancel_left₀ _ hne]
      have hmem : (conj (φ x) / ((‖φ x‖ : ℝ) : 𝕜)) • x ∈ closedBall (0 : E) ρ := by
        rw [mem_closedBall_zero_iff, norm_smul]
        have hcnorm : ‖conj (φ x) / ((‖φ x‖ : ℝ) : 𝕜)‖ = 1 := by
          rw [norm_div, RCLike.norm_conj, RCLike.norm_ofReal, abs_of_pos hnpos,
            div_self (ne_of_gt hnpos)]
        rw [hcnorm, one_mul]
        exact hx
      have hre := h _ (mem_closedBall_zero_iff.mp hmem)
      rw [hrot, RCLike.ofReal_re] at hre
      exact hre
  have hmem : WeakDual.toStrongDual φ ∈ StrongDual.polar 𝕜 (closedBall (0 : E) ρ) := by
    rw [StrongDual.mem_polar_iff]
    intro z hz
    rw [WeakDual.toStrongDual_apply]
    exact hnorm z hz
  rw [NormedSpace.polar_closedBall hρ] at hmem
  exact mem_closedBall_zero_iff.mp hmem

/-- Sublevel sets of real parts of evaluations are weak-* closed. -/
private lemma ks_isClosed_re_le {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (x : E) (c : ℝ) :
    IsClosed {φ : WeakDual 𝕜 E | RCLike.re (φ x) ≤ c} :=
  isClosed_le (RCLike.continuous_re.comp (WeakDual.eval_continuous x)) continuous_const

/-- Superlevel sets of real parts of evaluations are weak-* closed. -/
private lemma ks_isClosed_le_re {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (x : E) (c : ℝ) :
    IsClosed {φ : WeakDual 𝕜 E | c ≤ RCLike.re (φ x)} :=
  isClosed_le continuous_const (RCLike.continuous_re.comp (WeakDual.eval_continuous x))

/-- Real polars are weak-* closed. -/
private lemma ks_isClosed_rpol {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (F : Set E) : IsClosed (ks_rpol (𝕜 := 𝕜) F) := by
  have heq : ks_rpol (𝕜 := 𝕜) F
      = ⋂ x ∈ F, {φ : WeakDual 𝕜 E | RCLike.re (φ x) ≤ 1} := by
    ext φ
    simp [ks_rpol]
  rw [heq]
  exact isClosed_biInter fun x _ => ks_isClosed_re_le x 1

/-- Dual norm balls are weak-* closed. -/
private lemma ks_isClosed_ball {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (r : ℝ) :
    IsClosed (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) r) :=
  WeakDual.isClosed_closedBall 0 r

/-- Dual norm balls are weak-* compact. -/
private lemma ks_isCompact_ball {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (r : ℝ) :
    IsCompact (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) r) :=
  WeakDual.isCompact_closedBall 0 r

/-- A norm gap: if `0 ∉ K` and `K ∩ B 1` is closed, dual norms on `K` stay above
some positive `δ ≤ 1`. -/
private lemma ks_norm_gap {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {K : Set (WeakDual 𝕜 E)} (h0 : (0 : WeakDual 𝕜 E) ∉ K)
    (hcl : IsClosed (K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ φ : WeakDual 𝕜 E, φ ∈ K → δ < ‖WeakDual.toStrongDual φ‖ := by
  have hUopen :
      IsOpen (K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1)ᶜ :=
    hcl.isOpen_compl
  have h0U : (0 : WeakDual 𝕜 E)
      ∈ (K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1)ᶜ :=
    fun h => h0 h.1
  have hcont : Continuous fun x' : StrongDual 𝕜 E => StrongDual.toWeakDual x' :=
    NormedSpace.Dual.toWeakDual_continuous
  have hVopen : IsOpen ((fun x' : StrongDual 𝕜 E => StrongDual.toWeakDual x') ⁻¹'
      (K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1)ᶜ) :=
    hUopen.preimage hcont
  have h0V : (0 : StrongDual 𝕜 E) ∈ (fun x' : StrongDual 𝕜 E => StrongDual.toWeakDual x') ⁻¹'
      (K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1)ᶜ := by
    change StrongDual.toWeakDual 0 ∈
      (K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1)ᶜ
    rw [map_zero]
    exact h0U
  rw [Metric.isOpen_iff] at hVopen
  obtain ⟨ε, hε, hball⟩ := hVopen 0 h0V
  refine ⟨min (ε / 2) 1, lt_min (by linarith) zero_lt_one, min_le_right _ _, fun φ hφ => ?_⟩
  by_contra hcon
  have hle : ‖WeakDual.toStrongDual φ‖ ≤ min (ε / 2) 1 := le_of_not_gt hcon
  have hB : φ ∈ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1 := by
    change WeakDual.toStrongDual φ ∈ closedBall (0 : StrongDual 𝕜 E) 1
    rw [mem_closedBall_zero_iff]
    exact le_trans hle (min_le_right _ _)
  have hball' : WeakDual.toStrongDual φ ∈ ball (0 : StrongDual 𝕜 E) ε := by
    rw [mem_ball_zero_iff]
    exact lt_of_le_of_lt hle (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε))
  have hmem : StrongDual.toWeakDual (WeakDual.toStrongDual φ) ∈
      (K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1)ᶜ :=
    hball hball'
  rw [WeakDual.toWeakDual_toStrongDual] at hmem
  exact hmem ⟨hφ, hB⟩

/-- One step of the Banach–Dieudonné construction: enlarge `G` by finitely many
small vectors so the next ball intersection becomes empty. -/
private lemma ks_step {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {K : Set (WeakDual 𝕜 E)}
    (hK : ∀ r : ℝ, 0 < r →
      IsClosed (K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) r))
    {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 1 ≤ n) {G : Finset E}
    (hempty : K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) (δ * (n : ℝ))
      ∩ ks_rpol (𝕜 := 𝕜) ↑G = ∅) :
    ∃ F : Finset E, (∀ x ∈ F, ‖x‖ ≤ (δ * (n : ℝ))⁻¹) ∧
      K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) (δ * ((n : ℝ) + 1))
        ∩ ks_rpol (𝕜 := 𝕜) (↑G ∪ ↑F) = ∅ := by
  classical
  have hn0 : 0 < n := by omega
  have hδn : 0 < δ * (n : ℝ) := mul_pos hδ (Nat.cast_pos.mpr hn0)
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hRpos : 0 < δ * ((n : ℝ) + 1) := mul_pos hδ (by linarith)
  have hQclosed : IsClosed (K ∩ WeakDual.toStrongDual ⁻¹'
      closedBall (0 : StrongDual 𝕜 E) (δ * ((n : ℝ) + 1)) ∩ ks_rpol (𝕜 := 𝕜) ↑G) :=
    (hK _ hRpos).inter (ks_isClosed_rpol _)
  have hQsub : (K ∩ WeakDual.toStrongDual ⁻¹'
      closedBall (0 : StrongDual 𝕜 E) (δ * ((n : ℝ) + 1)) ∩ ks_rpol (𝕜 := 𝕜) ↑G)
      ⊆ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) (δ * ((n : ℝ) + 1)) :=
    fun φ h => h.1.2
  have hQcompact : IsCompact (K ∩ WeakDual.toStrongDual ⁻¹'
      closedBall (0 : StrongDual 𝕜 E) (δ * ((n : ℝ) + 1)) ∩ ks_rpol (𝕜 := 𝕜) ↑G) :=
    (ks_isCompact_ball _).of_isClosed_subset hQclosed hQsub
  have hdisj : Disjoint (K ∩ WeakDual.toStrongDual ⁻¹'
        closedBall (0 : StrongDual 𝕜 E) (δ * ((n : ℝ) + 1)) ∩ ks_rpol (𝕜 := 𝕜) ↑G)
      (⋂ v : ↥(closedBall (0 : E) (δ * (n : ℝ))⁻¹),
        {φ : WeakDual 𝕜 E | RCLike.re (φ v.val) ≤ 1}) := by
    rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
    intro φ hφ
    rw [Set.mem_inter_iff] at hφ
    obtain ⟨⟨⟨hKφ, hBφ⟩, hrpol⟩, hmem⟩ := hφ
    have hball : ∀ x : E, ‖x‖ ≤ (δ * (n : ℝ))⁻¹ → RCLike.re (φ x) ≤ 1 := by
      intro x hx
      exact (Set.mem_iInter.mp hmem) ⟨x, mem_closedBall_zero_iff.mpr hx⟩
    have hnorm := ks_norm_le_of_rpol (inv_pos.mpr hδn) hball
    rw [inv_inv] at hnorm
    have hmem2 : φ ∈ K ∩ WeakDual.toStrongDual ⁻¹'
        closedBall (0 : StrongDual 𝕜 E) (δ * (n : ℝ)) ∩ ks_rpol (𝕜 := 𝕜) ↑G := by
      refine ⟨⟨hKφ, ?_⟩, hrpol⟩
      change WeakDual.toStrongDual φ ∈ closedBall (0 : StrongDual 𝕜 E) (δ * (n : ℝ))
      rw [mem_closedBall_zero_iff]
      exact hnorm
    rw [hempty] at hmem2
    exact notMem_empty φ hmem2
  obtain ⟨u, hu⟩ := hQcompact.elim_finite_subfamily_closed
    (fun v : ↥(closedBall (0 : E) (δ * (n : ℝ))⁻¹) =>
      {φ : WeakDual 𝕜 E | RCLike.re (φ v.val) ≤ 1})
    (fun v => ks_isClosed_re_le v.val 1) hdisj
  refine ⟨u.image Subtype.val, fun x hx => ?_, ?_⟩
  · obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact mem_closedBall_zero_iff.mp v.property
  · apply Set.eq_empty_iff_forall_notMem.mpr
    rintro φ ⟨⟨hKφ, hBφ⟩, hrpol⟩
    have hrpol' : ∀ x ∈ (↑G ∪ ↑(u.image Subtype.val) : Set E), RCLike.re (φ x) ≤ 1 :=
      hrpol
    have hQu : φ ∈ K ∩ WeakDual.toStrongDual ⁻¹'
        closedBall (0 : StrongDual 𝕜 E) (δ * ((n : ℝ) + 1)) ∩ ks_rpol (𝕜 := 𝕜) ↑G := by
      refine ⟨⟨hKφ, hBφ⟩, fun x hx => hrpol' x (Set.mem_union_left _ hx)⟩
    have hI : φ ∈ ⋂ v ∈ u,
        {φ' : WeakDual 𝕜 E | RCLike.re (φ' v.val) ≤ 1} := by
      simp only [Set.mem_iInter]
      intro v hv
      have hFv : (v.val : E) ∈ u.image Subtype.val :=
        Finset.mem_image.mpr ⟨v, Finset.mem_coe.mp hv, rfl⟩
      exact hrpol' _ (Set.mem_union_right _ (Finset.mem_coe.mpr hFv))
    exact Set.disjoint_left.mp hu hQu hI

/-- The null family: countably many small vectors detecting every `φ ∈ K`. -/
private lemma ks_null_family {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {K : Set (WeakDual 𝕜 E)}
    (hK : ∀ r : ℝ, 0 < r →
      IsClosed (K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) r))
    {δ : ℝ} (hδ : 0 < δ)
    (hKδ : K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) δ = ∅) :
    ∃ x : ℕ × ℕ → E, Filter.Tendsto x Filter.cofinite (nhds 0) ∧
      (∀ p, ‖x p‖ ≤ δ⁻¹) ∧
      (∀ φ : WeakDual 𝕜 E, φ ∈ K → ∃ p, 1 < RCLike.re (φ (x p))) := by
  classical
  have key : ∀ m : ℕ, ∀ G : Finset E,
      K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) (δ * ((m : ℝ) + 1))
        ∩ ks_rpol (𝕜 := 𝕜) ↑G = ∅ →
      ∃ F : Finset E, (∀ x ∈ F, ‖x‖ ≤ (δ * ((m : ℝ) + 1))⁻¹) ∧
        K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) (δ * ((m : ℝ) + 2))
          ∩ ks_rpol (𝕜 := 𝕜) (↑G ∪ ↑F) = ∅ := by
    intro m G h
    have e1 : ((m : ℝ) + 1) = ((((m + 1 : ℕ)) : ℝ)) := by
      rw [Nat.cast_add_one]
    have e2 : ((m : ℝ) + 2) = (((((m + 1 : ℕ)) : ℝ)) + 1) := by
      rw [Nat.cast_add_one]; ring
    rw [e1] at h
    obtain ⟨F, hFb, hFe⟩ := ks_step hK hδ (n := m + 1) (by omega) (G := G) h
    rw [← e1] at hFb
    rw [← e2] at hFe
    exact ⟨F, hFb, hFe⟩
  have keyT : ∀ m : ℕ, ∀ G : Finset E, ∃ F : Finset E,
      (K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) (δ * ((m : ℝ) + 1))
        ∩ ks_rpol (𝕜 := 𝕜) ↑G = ∅) →
        ((∀ x ∈ F, ‖x‖ ≤ (δ * ((m : ℝ) + 1))⁻¹) ∧
          K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) (δ * ((m : ℝ) + 2))
            ∩ ks_rpol (𝕜 := 𝕜) (↑G ∪ ↑F) = ∅) := by
    intro m G
    by_cases h : K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E)
        (δ * ((m : ℝ) + 1)) ∩ ks_rpol (𝕜 := 𝕜) ↑G = ∅
    · obtain ⟨F, hFb, hFe⟩ := key m G h
      exact ⟨F, fun _ => ⟨hFb, hFe⟩⟩
    · exact ⟨∅, fun h' => (h h').elim⟩
  have hFchoice : ∃ Fchoice : ℕ → Finset E → Finset E, ∀ m : ℕ, ∀ G : Finset E,
      (K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) (δ * ((m : ℝ) + 1))
        ∩ ks_rpol (𝕜 := 𝕜) ↑G = ∅) →
        ((∀ x ∈ Fchoice m G, ‖x‖ ≤ (δ * ((m : ℝ) + 1))⁻¹) ∧
          K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) (δ * ((m : ℝ) + 2))
            ∩ ks_rpol (𝕜 := 𝕜) (↑G ∪ ↑(Fchoice m G)) = ∅) :=
    ⟨fun m G => Classical.choose (keyT m G), fun m G => Classical.choose_spec (keyT m G)⟩
  obtain ⟨Fchoice, hFspec⟩ := hFchoice
  have hGseq : ∃ Gseq : ℕ → Finset E, Gseq 0 = ∅ ∧
      ∀ m, Gseq (m + 1) = Gseq m ∪ Fchoice m (Gseq m) :=
    ⟨fun m => Nat.rec (motive := fun _ => Finset E) ∅ (fun m Gm => Gm ∪ Fchoice m Gm) m,
      rfl, fun m => rfl⟩
  obtain ⟨Gseq, hG0, hGS⟩ := hGseq
  have hinv : ∀ m : ℕ, K ∩ WeakDual.toStrongDual ⁻¹'
      closedBall (0 : StrongDual 𝕜 E) (δ * ((m : ℝ) + 1))
        ∩ ks_rpol (𝕜 := 𝕜) ↑(Gseq m) = ∅ := by
    intro m
    induction m with
    | zero =>
      have hrpol_empty : ks_rpol (𝕜 := 𝕜) (∅ : Set E) = Set.univ := by
        ext φ
        simp [ks_rpol]
      rw [hG0, Finset.coe_empty, hrpol_empty, Set.inter_univ]
      simp only [Nat.cast_zero, zero_add, mul_one]
      exact hKδ
    | succ m ihm =>
      have hnext := (hFspec m (Gseq m)) ihm
      obtain ⟨_, hFe⟩ := hnext
      have e2 : ((m : ℝ) + 2) = ((((m + 1 : ℕ)) : ℝ) + 1) := by
        rw [Nat.cast_add_one]; ring
      rw [e2] at hFe
      rw [hGS m, Finset.coe_union]
      exact hFe
  have hFb : ∀ m : ℕ, ∀ x ∈ Fchoice m (Gseq m), ‖x‖ ≤ (δ * ((m : ℝ) + 1))⁻¹ := by
    intro m x hx
    exact ((hFspec m (Gseq m) (hinv m)).1) x hx
  have hmemU : ∀ m : ℕ, ∀ y ∈ Gseq m, ∃ i, i < m ∧ y ∈ Fchoice i (Gseq i) := by
    intro m
    induction m with
    | zero =>
      intro y hy
      rw [hG0] at hy
      exact absurd hy (Finset.notMem_empty y)
    | succ m ihm =>
      intro y hy
      rw [hGS m, Finset.mem_union] at hy
      cases hy with
      | inl h =>
        obtain ⟨i, hi, hiy⟩ := ihm y h
        exact ⟨i, by omega, hiy⟩
      | inr h => exact ⟨m, by omega, h⟩
  have hmemL : ∀ m : ℕ, ∀ j : ℕ, j < ((Fchoice m (Gseq m)).toList).length →
      ((Fchoice m (Gseq m)).toList).getD j 0 ∈ Fchoice m (Gseq m) := by
    intro m j hj
    rw [List.getD_eq_getElem _ _ hj]
    exact Finset.mem_toList.mp (List.getElem_mem hj)
  refine ⟨fun p : ℕ × ℕ => ((Fchoice p.1 (Gseq p.1)).toList.getD p.2 0), ?_, ?_, ?_⟩
  · rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (δ⁻¹ / ε)
    have hNε : δ⁻¹ < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN
    have hM : (0 : ℝ) < ((((N + 1 : ℕ)) : ℝ)) := by exact_mod_cast Nat.succ_pos N
    have hδM : 0 < δ * ((((N + 1 : ℕ)) : ℝ)) := mul_pos hδ hM
    have hNN : (N : ℝ) ≤ ((((N + 1 : ℕ)) : ℝ)) := by
      rw [Nat.cast_add_one]
      have h0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
    have hbound : (δ * ((((N + 1 : ℕ)) : ℝ)))⁻¹ < ε := by
      rw [inv_lt_iff_one_lt_mul₀' hδM]
      calc (1 : ℝ) = δ * δ⁻¹ := (mul_inv_cancel₀ hδ.ne').symm
        _ < δ * ((N : ℝ) * ε) := mul_lt_mul_of_pos_left hNε hδ
        _ ≤ (δ * ((((N + 1 : ℕ)) : ℝ))) * ε := by
          calc δ * ((N : ℝ) * ε) = (δ * ε) * (N : ℝ) := by ring
            _ ≤ (δ * ε) * ((((N + 1 : ℕ)) : ℝ)) :=
              mul_le_mul_of_nonneg_left hNN (mul_nonneg hδ.le hε.le)
            _ = (δ * ((((N + 1 : ℕ)) : ℝ))) * ε := by ring
    have hfin : {p : ℕ × ℕ | ¬ dist (((Fchoice p.1 (Gseq p.1)).toList.getD p.2 0)) 0
        < ε}.Finite := by
      set S : Finset (ℕ × ℕ) := (Finset.range (N + 1)).biUnion
        (fun m => (Finset.range ((Fchoice m (Gseq m)).card)).image
          (fun j => (m, j))) with hS
      have hsub : {p : ℕ × ℕ | ¬ dist (((Fchoice p.1 (Gseq p.1)).toList.getD p.2 0)) 0
          < ε} ⊆ ↑S := by
        rintro ⟨m, j⟩ hj
        simp only [Set.mem_ofPred_eq, dist_zero_right] at hj
        have hj' : ε ≤ ‖((Fchoice m (Gseq m)).toList.getD j 0)‖ := not_lt.mp hj
        have hm : m < N + 1 := by
          by_contra hcon
          have hNm : N + 1 ≤ m := not_lt.mp hcon
          have hlt : ‖((Fchoice m (Gseq m)).toList.getD j 0)‖ < ε := by
            by_cases hjlen : j < ((Fchoice m (Gseq m)).toList).length
            · have hb := hFb m _ (hmemL m j hjlen)
              have hmono : (δ * ((m : ℝ) + 1))⁻¹ ≤ (δ * ((((N + 1 : ℕ)) : ℝ)))⁻¹ := by
                apply inv_anti₀ hδM
                apply mul_le_mul_of_nonneg_left _ hδ.le
                have hNm2 : N + 1 ≤ m + 1 := le_trans hNm (Nat.le_add_right m 1)
                exact_mod_cast hNm2
              exact lt_of_le_of_lt (le_trans hb hmono) hbound
            · have hx0 : ((Fchoice m (Gseq m)).toList.getD j 0) = 0 :=
                List.getD_eq_default _ _ (not_lt.mp hjlen)
              rw [hx0, norm_zero]
              exact hε
          exact absurd hj' (not_le.mpr hlt)
        have hjm : j < (Fchoice m (Gseq m)).card := by
          by_contra hcon
          have hjmle : (Fchoice m (Gseq m)).card ≤ j := not_lt.mp hcon
          have hx0 : ((Fchoice m (Gseq m)).toList.getD j 0) = 0 := by
            apply List.getD_eq_default _ _
            rw [Finset.length_toList]
            exact hjmle
          rw [hx0, norm_zero] at hj'
          exact absurd hj' (not_le.mpr hε)
        rw [Finset.mem_coe, hS, Finset.mem_biUnion]
        exact ⟨m, Finset.mem_range.mpr hm,
          Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hjm, rfl⟩⟩
      exact Set.Finite.subset (Finset.finite_toSet S) hsub
    exact Filter.eventually_cofinite.mpr hfin
  · intro p
    obtain ⟨m, j⟩ := p
    change ‖((Fchoice m (Gseq m)).toList.getD j 0)‖ ≤ δ⁻¹
    by_cases hjlen : j < ((Fchoice m (Gseq m)).toList).length
    · have hb := hFb m _ (hmemL m j hjlen)
      have hle1 : (1 : ℝ) ≤ ((((m + 1 : ℕ)) : ℝ)) := by
        rw [Nat.cast_add_one]
        have h0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        linarith
      have hδle : δ ≤ δ * ((((m + 1 : ℕ)) : ℝ)) :=
        le_mul_of_one_le_right hδ.le hle1
      have hback : (δ * ((((m + 1 : ℕ)) : ℝ)))⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ hδle
      have hb' : ‖((Fchoice m (Gseq m)).toList.getD j 0)‖ ≤ (δ * ((m : ℝ) + 1))⁻¹ :=
        hb
      have hfw : (δ * ((m : ℝ) + 1))⁻¹ = (δ * ((((m + 1 : ℕ)) : ℝ)))⁻¹ := by
        rw [Nat.cast_add_one]
      rw [hfw] at hb'
      exact le_trans hb' hback
    · have hx0 : ((Fchoice m (Gseq m)).toList.getD j 0) = 0 :=
        List.getD_eq_default _ _ (not_lt.mp hjlen)
      rw [hx0, norm_zero]
      exact inv_nonneg.mpr hδ.le
  · intro φ hφ
    obtain ⟨N, hN⟩ := exists_nat_ge (‖WeakDual.toStrongDual φ‖ / δ)
    have hleN : ‖WeakDual.toStrongDual φ‖ ≤ δ * ((N : ℝ) + 1) := by
      have hle : ‖WeakDual.toStrongDual φ‖ ≤ δ * (N : ℝ) := by
        have h1 : ‖WeakDual.toStrongDual φ‖ / δ ≤ (N : ℝ) := hN
        rw [div_le_iff₀ hδ] at h1
        calc ‖WeakDual.toStrongDual φ‖ ≤ (N : ℝ) * δ := h1
          _ = δ * (N : ℝ) := by ring
      calc ‖WeakDual.toStrongDual φ‖ ≤ δ * (N : ℝ) := hle
        _ ≤ δ * ((N : ℝ) + 1) := by
          apply mul_le_mul_of_nonneg_left _ hδ.le
          have h0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
          linarith
    have hB : φ ∈ WeakDual.toStrongDual ⁻¹'
        closedBall (0 : StrongDual 𝕜 E) (δ * ((N : ℝ) + 1)) := by
      change WeakDual.toStrongDual φ ∈
        closedBall (0 : StrongDual 𝕜 E) (δ * ((N : ℝ) + 1))
      rw [mem_closedBall_zero_iff]
      exact hleN
    have hnotin : φ ∉ ks_rpol (𝕜 := 𝕜) ↑(Gseq N) := by
      intro hr
      have hmem : φ ∈ K ∩ WeakDual.toStrongDual ⁻¹'
          closedBall (0 : StrongDual 𝕜 E) (δ * ((N : ℝ) + 1))
            ∩ ks_rpol (𝕜 := 𝕜) ↑(Gseq N) :=
        ⟨⟨hφ, hB⟩, hr⟩
      rw [hinv N] at hmem
      exact notMem_empty φ hmem
    obtain ⟨y, hyG, hy1⟩ : ∃ y ∈ (↑(Gseq N) : Set E), 1 < RCLike.re (φ y) := by
      by_contra hcon
      apply hnotin
      change ∀ y ∈ (↑(Gseq N) : Set E), RCLike.re (φ y) ≤ 1
      intro y hy
      by_contra hle'
      have hlt : 1 < RCLike.re (φ y) := lt_of_not_ge hle'
      exact hcon ⟨y, hy, hlt⟩
    obtain ⟨i, _, hyF⟩ := hmemU N y (Finset.mem_coe.mp hyG)
    have hyL : y ∈ (Fchoice i (Gseq i)).toList := Finset.mem_toList.mpr hyF
    obtain ⟨j, hjlen, hjeq⟩ := List.mem_iff_getElem.mp hyL
    refine ⟨(i, j), ?_⟩
    change 1 < RCLike.re (φ (((Fchoice i (Gseq i)).toList.getD j 0)))
    have hxy : ((Fchoice i (Gseq i)).toList.getD j 0) = y := by
      rw [List.getD_eq_getElem _ _ hjlen]
      exact hjeq
    rw [hxy]
    exact hy1

/-- Real parts distribute over addition. -/
private lemma ks_re_add {𝕜 : Type*} [RCLike 𝕜] (z w : 𝕜) :
    RCLike.re (z + w) = RCLike.re z + RCLike.re w := by
  have h := map_add (RCLike.reCLM (K := 𝕜)) z w
  rwa [RCLike.reCLM_apply] at h

/-- The coordinate map into `C₀(ℕ × ℕ, ℝ)`. -/
private noncomputable def ks_c0fun {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {x : ℕ × ℕ → E}
    (hx0 : Filter.Tendsto x Filter.cofinite (nhds 0)) (φ : WeakDual 𝕜 E) : C₀(ℕ × ℕ, ℝ) :=
  ZeroAtInftyContinuousMap.mk
    ⟨fun p => RCLike.re (φ (x p)), continuous_of_discreteTopology⟩ (by
    have hcont : Continuous fun y : E => RCLike.re (φ y) :=
      RCLike.continuous_re.comp (WeakDual.toStrongDual φ).continuous
    have h0 : RCLike.re (φ 0) = 0 := by simp
    have hcomp := (hcont.tendsto 0).comp hx0
    rw [h0] at hcomp
    rw [Filter.cocompact_eq_cofinite]
    exact hcomp)

/-- Values of the coordinate map. -/
private lemma ks_c0fun_apply {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {x : ℕ × ℕ → E}
    (hx0 : Filter.Tendsto x Filter.cofinite (nhds 0)) (φ : WeakDual 𝕜 E) (p : ℕ × ℕ) :
    ks_c0fun hx0 φ p = RCLike.re (φ (x p)) :=
  rfl

/-- The coordinate map as a real linear map. -/
private noncomputable def ks_c0lin {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {x : ℕ × ℕ → E}
    (hx0 : Filter.Tendsto x Filter.cofinite (nhds 0)) : WeakDual 𝕜 E →ₗ[ℝ] C₀(ℕ × ℕ, ℝ) where
  toFun := ks_c0fun hx0
  map_add' := fun φ ψ => by
    ext p
    simp only [ks_c0fun_apply, ZeroAtInftyContinuousMap.add_apply]
    have hadd : (φ + ψ) (x p) = φ (x p) + ψ (x p) := rfl
    rw [hadd]
    exact ks_re_add _ _
  map_smul' := fun c φ => by
    ext p
    simp only [ks_c0fun_apply, ZeroAtInftyContinuousMap.smul_apply]
    have hsmul : ((c • φ) (x p)) = c • (φ (x p)) := rfl
    rw [hsmul, RCLike.smul_re]
    simp only [smul_eq_mul, RingHom.id_apply]

/-- Values of the linear coordinate map. -/
private lemma ks_c0lin_apply {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {x : ℕ × ℕ → E}
    (hx0 : Filter.Tendsto x Filter.cofinite (nhds 0)) (φ : WeakDual 𝕜 E) (p : ℕ × ℕ) :
    ks_c0lin hx0 φ p = RCLike.re (φ (x p)) :=
  rfl

/-- Pointwise norm bound for the coordinate map. -/
private lemma ks_c0norm {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {x : ℕ × ℕ → E}
    (hx0 : Filter.Tendsto x Filter.cofinite (nhds 0)) (φ : WeakDual 𝕜 E) (p : ℕ × ℕ) :
    |RCLike.re (φ (x p))| ≤ ‖ks_c0lin hx0 φ‖ := by
  have h1 := BoundedContinuousFunction.norm_coe_le_norm (ks_c0lin hx0 φ).toBCF p
  rw [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm, Real.norm_eq_abs] at h1
  exact h1

/-- Indicator of a singleton in `C₀(ℕ × ℕ, ℝ)`. -/
private noncomputable def ks_ind (p : ℕ × ℕ) : C₀(ℕ × ℕ, ℝ) :=
  ZeroAtInftyContinuousMap.mk
    ⟨Set.indicator {p} (fun _ => (1 : ℝ)), continuous_of_discreteTopology⟩ (by
    rw [Filter.cocompact_eq_cofinite]
    have hev : ∀ᶠ q : ℕ × ℕ in Filter.cofinite,
        (0 : ℝ) = Set.indicator ({p} : Set (ℕ × ℕ)) (fun _ => (1 : ℝ)) q := by
      rw [Filter.eventually_cofinite]
      apply Set.Finite.subset (Finset.finite_toSet {p})
      intro q hq
      simp only [Set.mem_ofPred_eq] at hq
      rw [Finset.mem_coe, Finset.mem_singleton]
      by_contra hcon
      have hmem : q ∉ ({p} : Set (ℕ × ℕ)) := by
        simpa only [Set.mem_singleton_iff] using hcon
      have h0q : Set.indicator ({p} : Set (ℕ × ℕ)) (fun _ => (1 : ℝ)) q = 0 :=
        Set.indicator_of_notMem hmem _
      exact hq h0q.symm
    exact Filter.Tendsto.congr' hev tendsto_const_nhds)

/-- Value of the indicator at its own point. -/
private lemma ks_ind_self (p : ℕ × ℕ) : ks_ind p p = 1 := by
  change Set.indicator ({p} : Set (ℕ × ℕ)) (fun _ => (1 : ℝ)) p = 1
  exact Set.indicator_of_mem (Set.mem_singleton p) _

/-- Value of the indicator away from its point. -/
private lemma ks_ind_other (p q : ℕ × ℕ) (h : q ≠ p) : ks_ind p q = 0 := by
  change Set.indicator ({p} : Set (ℕ × ℕ)) (fun _ => (1 : ℝ)) q = 0
  exact Set.indicator_of_notMem (by simpa only [Set.mem_singleton_iff] using h) _

/-- Sign times self is absolute value. -/
private lemma ks_sign_mul_self (t : ℝ) : Real.sign t * t = |t| := by
  rcases lt_trichotomy t 0 with h | h | h
  · rw [Real.sign_of_neg h, abs_of_neg h]; ring
  · subst h; simp
  · rw [Real.sign_of_pos h, abs_of_pos h]; ring

/-- Absolute value of a sign is at most one. -/
private lemma ks_abs_sign (t : ℝ) : |Real.sign t| ≤ 1 := by
  rcases lt_trichotomy t 0 with h | h | h
  · rw [Real.sign_of_neg h, abs_neg, abs_one]
  · subst h; rw [Real.sign_zero, abs_zero]; exact zero_le_one
  · rw [Real.sign_of_pos h, abs_one]

/-- Finite sums in `C₀` evaluate pointwise. -/
private lemma ks_sum_apply (S : Finset (ℕ × ℕ)) (g : (ℕ × ℕ) → C₀(ℕ × ℕ, ℝ)) (q : ℕ × ℕ) :
    (∑ p ∈ S, g p) q = ∑ p ∈ S, g p q := by
  refine Finset.induction_on S ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty]
    rfl
  · intro a s has IH
    rw [Finset.sum_insert has, Finset.sum_insert has, ZeroAtInftyContinuousMap.add_apply,
      IH]

/-- Functionals on `C₀` give summable weights. -/
private lemma ks_summable_weights (f : C₀(ℕ × ℕ, ℝ) →L[ℝ] ℝ) :
    Summable (fun p => f (ks_ind p)) := by
  apply Summable.of_abs
  refine summable_of_sum_le (c := ‖f‖) (fun _ => abs_nonneg _) ?_
  intro S
  set z : C₀(ℕ × ℕ, ℝ) := ∑ p ∈ S, (Real.sign (f (ks_ind p))) • ks_ind p with hz
  have hznorm : ‖z‖ ≤ 1 := by
    have hq : ∀ q : ℕ × ℕ, ‖z q‖ ≤ 1 := by
      intro q
      by_cases hqS : q ∈ S
      · have hzero : ∀ p ∈ S, p ≠ q → (Real.sign (f (ks_ind p)) • ks_ind p) q = 0 := by
          intro p hp hpq
          rw [ZeroAtInftyContinuousMap.smul_apply, ks_ind_other p q (Ne.symm hpq),
            smul_zero]
        have e : z q = Real.sign (f (ks_ind q)) := by
          have e1 : z q = ∑ p ∈ S, ((Real.sign (f (ks_ind p))) • ks_ind p) q := by
            rw [hz, ks_sum_apply]
          rw [e1, Finset.sum_eq_single_of_mem q hqS hzero,
            ZeroAtInftyContinuousMap.smul_apply, ks_ind_self, smul_eq_mul, mul_one]
        rw [e, Real.norm_eq_abs]
        exact ks_abs_sign _
      · have hzero : ∀ p ∈ S, ((Real.sign (f (ks_ind p))) • ks_ind p) q = 0 := by
          intro p hp
          have hne : q ≠ p := by
            intro hcon
            subst hcon
            exact hqS hp
          rw [ZeroAtInftyContinuousMap.smul_apply, ks_ind_other p q hne, smul_zero]
        have e : z q = 0 := by
          have e1 : z q = ∑ p ∈ S, ((Real.sign (f (ks_ind p))) • ks_ind p) q := by
            rw [hz, ks_sum_apply]
          rw [e1]
          exact Finset.sum_eq_zero hzero
        rw [e, norm_zero]
        exact zero_le_one
    have hBCF : ‖z.toBCF‖ ≤ 1 := by
      rw [BoundedContinuousFunction.norm_le zero_le_one]
      intro q
      exact hq q
    rwa [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] at hBCF
  have hfz : f z = ∑ p ∈ S, |f (ks_ind p)| := by
    rw [hz, map_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [map_smul, smul_eq_mul]
    exact ks_sign_mul_self _
  calc ∑ p ∈ S, |f (ks_ind p)| = f z := hfz.symm
    _ ≤ ‖f z‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
    _ ≤ ‖f‖ * ‖z‖ := ContinuousLinearMap.le_opNorm f z
    _ ≤ ‖f‖ * 1 :=
      mul_le_mul_of_nonneg_left hznorm (ContinuousLinearMap.opNorm_nonneg f)
    _ = ‖f‖ := mul_one _

/-- Weights reconstruct the functional. -/
private lemma ks_hasSum_weights (f : C₀(ℕ × ℕ, ℝ) →L[ℝ] ℝ) (y : C₀(ℕ × ℕ, ℝ)) :
    HasSum (fun p => f (ks_ind p) * y p) (f y) := by
  have hpart : ∀ S : Finset (ℕ × ℕ), ∑ p ∈ S, f (ks_ind p) * y p
      = f (∑ p ∈ S, (y p) • ks_ind p) := by
    intro S
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [map_smul, smul_eq_mul, mul_comm]
  have hlim : Filter.Tendsto (fun S : Finset (ℕ × ℕ) => ∑ p ∈ S, (y p) • ks_ind p)
      Filter.atTop (nhds y) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε2 : (0 : ℝ) < ε / 2 := half_pos hε
    have hKfin : {p : ℕ × ℕ | ε / 2 ≤ ‖y p‖}.Finite := by
      have h0 : Filter.Tendsto (fun p : ℕ × ℕ => y p) Filter.cofinite (nhds (0 : ℝ)) := by
        have h0y := y.2
        rw [Filter.cocompact_eq_cofinite] at h0y
        exact h0y
      have hev : ∀ᶠ p : ℕ × ℕ in Filter.cofinite, dist (y p) 0 < ε / 2 :=
        h0.eventually (Metric.ball_mem_nhds 0 hε2)
      rw [Filter.eventually_cofinite] at hev
      apply Set.Finite.subset hev
      intro p hp
      simp only [Set.mem_ofPred_eq] at hp ⊢
      rw [dist_zero_right]
      exact not_lt.mpr hp
    obtain ⟨S₀, hS₀⟩ := Set.Finite.exists_finset hKfin
    rw [Filter.eventually_atTop]
    refine ⟨S₀, fun S hS => ?_⟩
    have hsub : S₀ ⊆ S := hS
    have hbound : ∀ q : ℕ × ℕ, ‖((∑ p ∈ S, (y p) • ks_ind p) - y) q‖ ≤ ε / 2 := by
      intro q
      by_cases hqS : q ∈ S
      · have hzero : ∀ p ∈ S, p ≠ q → ((y p) • ks_ind p) q = 0 := by
          intro p hp hpq
          rw [ZeroAtInftyContinuousMap.smul_apply, ks_ind_other p q (Ne.symm hpq),
            smul_zero]
        have e : (∑ p ∈ S, (y p) • ks_ind p) q = y q := by
          have e1 : (∑ p ∈ S, (y p) • ks_ind p) q
              = ∑ p ∈ S, (((y p) • ks_ind p)) q := by
            rw [ks_sum_apply]
          rw [e1, Finset.sum_eq_single_of_mem q hqS hzero,
            ZeroAtInftyContinuousMap.smul_apply, ks_ind_self, smul_eq_mul, mul_one]
        rw [ZeroAtInftyContinuousMap.sub_apply, e, sub_self, norm_zero]
        exact le_of_lt hε2
      · have hzero : ∀ p ∈ S, (((y p) • ks_ind p)) q = 0 := by
          intro p hp
          have hne : q ≠ p := by
            intro hcon
            subst hcon
            exact hqS hp
          rw [ZeroAtInftyContinuousMap.smul_apply, ks_ind_other p q hne, smul_zero]
        have e : (∑ p ∈ S, (y p) • ks_ind p) q = 0 := by
          have e1 : (∑ p ∈ S, (y p) • ks_ind p) q
              = ∑ p ∈ S, (((y p) • ks_ind p)) q := by
            rw [ks_sum_apply]
          rw [e1]
          exact Finset.sum_eq_zero hzero
        have hqK : q ∉ ({p : ℕ × ℕ | ε / 2 ≤ ‖y p‖} : Set _) := by
          intro hmem
          rw [← hS₀] at hmem
          exact hqS (hsub hmem)
        have hlt : ‖y q‖ < ε / 2 := lt_of_not_ge (fun hle => hqK hle)
        rw [ZeroAtInftyContinuousMap.sub_apply, e, zero_sub, norm_neg]
        exact le_of_lt hlt
    have hnorm : ‖(∑ p ∈ S, (y p) • ks_ind p) - y‖ ≤ ε / 2 := by
      have hBCF : ‖((∑ p ∈ S, (y p) • ks_ind p) - y).toBCF‖ ≤ ε / 2 := by
        rw [BoundedContinuousFunction.norm_le hε2.le]
        intro q
        exact hbound q
      rwa [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] at hBCF
    rw [dist_eq_norm]
    exact lt_of_le_of_lt hnorm (half_lt_self hε)
  have hlim2 : Filter.Tendsto (fun S : Finset (ℕ × ℕ) => ∑ p ∈ S, f (ks_ind p) * y p)
      Filter.atTop (nhds (f y)) := by
    have hcomp := (f.continuous.tendsto y).comp hlim
    simpa only [← hpart, Function.comp_def] using hcomp
  exact hlim2

/-- Separation: positive lower bound for real parts on `K`. -/
private lemma ks_separation {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [CompleteSpace E] {K : Set (WeakDual 𝕜 E)}
    (hKconv : Convex ℝ K) (h0 : (0 : WeakDual 𝕜 E) ∉ K)
    (hK : ∀ r : ℝ, 0 < r →
      IsClosed (K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) r)) :
    ∃ x : E, ∃ u : ℝ, 0 < u ∧ ∀ φ : WeakDual 𝕜 E, φ ∈ K → u ≤ RCLike.re (φ x) := by
  obtain ⟨δ, hδ, -, hgap⟩ := ks_norm_gap h0 (hK 1 zero_lt_one)
  have hKδ : K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) δ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro φ ⟨hφK, hφB⟩
    have hle : ‖WeakDual.toStrongDual φ‖ ≤ δ := mem_closedBall_zero_iff.mp hφB
    exact absurd hle (not_le.mpr (hgap φ hφK))
  obtain ⟨x, hx0, hxb, hxdet⟩ := ks_null_family hK hδ hKδ
  have himgconv : Convex ℝ ((ks_c0lin hx0) '' K) := by
    refine Convex.linear_image ?_ (ks_c0lin hx0)
    exact hKconv
  have hdisj : Disjoint (ball (0 : C₀(ℕ × ℕ, ℝ)) 1) ((ks_c0lin hx0) '' K) := by
    rw [Set.disjoint_left]
    rintro g hg ⟨φ, hφK, hφg⟩
    have hlt : ‖g‖ < 1 := mem_ball_zero_iff.mp hg
    obtain ⟨p, hp⟩ := hxdet φ hφK
    have hpt := ks_c0norm hx0 φ p
    rw [hφg] at hpt
    have habs : RCLike.re (φ (x p)) ≤ |RCLike.re (φ (x p))| := le_abs_self _
    linarith
  obtain ⟨f, u, hfu_ball, hfu_K⟩ := geometric_hahn_banach_open
    (convex_ball (0 : C₀(ℕ × ℕ, ℝ)) 1) isOpen_ball himgconv hdisj
  have hu : 0 < u := by
    have h0mem : (0 : C₀(ℕ × ℕ, ℝ)) ∈ ball (0 : C₀(ℕ × ℕ, ℝ)) 1 := by simp
    have hlt := hfu_ball 0 h0mem
    simpa using hlt
  have hsum_abs : Summable (fun p : ℕ × ℕ => |f (ks_ind p)|) :=
    (ks_summable_weights f).abs
  have hsum_g : Summable (fun p : ℕ × ℕ => |f (ks_ind p)| * δ⁻¹) :=
    hsum_abs.mul_right _
  have hbound : ∀ p : ℕ × ℕ,
      ‖(↑(f (ks_ind p)) : 𝕜) • x p‖ ≤ |f (ks_ind p)| * δ⁻¹ := by
    intro p
    calc ‖(↑(f (ks_ind p)) : 𝕜) • x p‖ = |f (ks_ind p)| * ‖x p‖ := by
            rw [norm_smul, RCLike.norm_ofReal]
      _ ≤ |f (ks_ind p)| * δ⁻¹ :=
            mul_le_mul_of_nonneg_left (hxb p) (abs_nonneg _)
  have hsumm : Summable (fun p : ℕ × ℕ => (↑(f (ks_ind p)) : 𝕜) • x p) :=
    Summable.of_norm_bounded hsum_g hbound
  refine ⟨∑' p : ℕ × ℕ, (↑(f (ks_ind p)) : 𝕜) • x p, u, hu, fun φ hφ => ?_⟩
  have hge : u ≤ f (ks_c0lin hx0 φ) := hfu_K _ ⟨φ, hφ, rfl⟩
  have h1 : HasSum
      (fun p : ℕ × ℕ => (WeakDual.toStrongDual φ) ((↑(f (ks_ind p)) : 𝕜) • x p))
      ((WeakDual.toStrongDual φ) (∑' p : ℕ × ℕ, (↑(f (ks_ind p)) : 𝕜) • x p)) :=
    hsumm.hasSum.mapL (WeakDual.toStrongDual φ)
  have h2 : HasSum
      (fun p : ℕ × ℕ =>
        RCLike.re ((WeakDual.toStrongDual φ) ((↑(f (ks_ind p)) : 𝕜) • x p)))
      (RCLike.re ((WeakDual.toStrongDual φ)
        (∑' p : ℕ × ℕ, (↑(f (ks_ind p)) : 𝕜) • x p))) :=
    h1.mapL (RCLike.reCLM (K := 𝕜))
  have hterm : ∀ p : ℕ × ℕ, f (ks_ind p) * ks_c0lin hx0 φ p
      = RCLike.re ((WeakDual.toStrongDual φ) ((↑(f (ks_ind p)) : 𝕜) • x p)) := by
    intro p
    rw [map_smul, smul_eq_mul, RCLike.re_ofReal_mul, ks_c0lin_apply,
      WeakDual.toStrongDual_apply]
  have h3 : HasSum (fun p : ℕ × ℕ => f (ks_ind p) * ks_c0lin hx0 φ p)
      (RCLike.re ((WeakDual.toStrongDual φ)
        (∑' p : ℕ × ℕ, (↑(f (ks_ind p)) : 𝕜) • x p))) :=
    h2.congr_fun (fun p => hterm p)
  have heq : RCLike.re ((WeakDual.toStrongDual φ)
        (∑' p : ℕ × ℕ, (↑(f (ks_ind p)) : 𝕜) • x p)) = f (ks_c0lin hx0 φ) :=
    HasSum.unique h3 (ks_hasSum_weights f (ks_c0lin hx0 φ))
  have hφx : RCLike.re (φ (∑' p : ℕ × ℕ, (↑(f (ks_ind p)) : 𝕜) • x p))
      = f (ks_c0lin hx0 φ) := heq
  rw [hφx]
  exact hge

/-- `0` is not in the weak-* closure of `K`. -/
private lemma ks_zero_notMem_closure {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {K : Set (WeakDual 𝕜 E)} (hKconv : Convex ℝ K) (h0 : (0 : WeakDual 𝕜 E) ∉ K)
    (hK : ∀ r : ℝ, 0 < r →
      IsClosed (K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) r)) :
    (0 : WeakDual 𝕜 E) ∉ closure K := by
  obtain ⟨x, u, hu, hbound⟩ := ks_separation hKconv h0 hK
  have hsub : K ⊆ {φ : WeakDual 𝕜 E | u ≤ RCLike.re (φ x)} :=
    fun φ hφ => hbound φ hφ
  have hcl : closure K ⊆ {φ : WeakDual 𝕜 E | u ≤ RCLike.re (φ x)} :=
    closure_minimal hsub (ks_isClosed_le_re x u)
  intro hmem
  have h0le : u ≤ RCLike.re ((0 : WeakDual 𝕜 E) x) := hcl hmem
  have h00 : ((0 : WeakDual 𝕜 E) x) = (0 : 𝕜) := by
    have h1 : WeakDual.toStrongDual (0 : WeakDual 𝕜 E) = 0 := map_zero _
    calc ((0 : WeakDual 𝕜 E) x) = (WeakDual.toStrongDual (0 : WeakDual 𝕜 E)) x :=
            (WeakDual.toStrongDual_apply _ _).symm
      _ = (0 : StrongDual 𝕜 E) x := by rw [h1]
      _ = 0 := by simp
  have h0r : RCLike.re (0 : 𝕜) = 0 := by simp
  rw [h00, h0r] at h0le
  linarith

/--
**Krein–Smulian theorem.** Let $E$ be a Banach space over $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$, and let $C$ be a subset of its dual $E^*$ that is convex over $\mathbb{R}$. Then $C$
is weak-star closed if and only if, for every $r > 0$, the set
$\{\varphi \in C : \|\varphi\| \le r\}$ is weak-star closed.

Proves `Wanted` entry `krein_smulian`.

Source: M. Krein
and V. Smulian, Ann. of Math. 41 (1940) 556-583; Dunford-Schwartz I; Lean states `RCLike` Banach
case with `Convex ℝ s` and closedBall intersections. -/
theorem krein_smulian
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {s : Set (WeakDual 𝕜 E)} (hs : Convex ℝ s) :
    IsClosed s ↔
      ∀ (r : ℝ) (_ : 0 < r),
        IsClosed
          (s ∩ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual 𝕜 E) r) := by
  constructor
  · intro hclosed r _hr
    exact hclosed.inter (ks_isClosed_ball r)
  · intro hball
    rw [← closure_subset_iff_isClosed]
    intro φ₀ hφ₀
    by_contra hφ₀out
    have h0K : (0 : WeakDual 𝕜 E) ∉ (fun ψ => ψ + φ₀) ⁻¹' s := by
      intro h
      simp only [Set.mem_preimage] at h
      rw [zero_add] at h
      exact hφ₀out h
    have hKconv : Convex ℝ ((fun ψ : WeakDual 𝕜 E => ψ + φ₀) ⁻¹' s) := by
      intro a ha b hb α β hα hβ hαβ
      simp only [Set.mem_preimage] at ha hb ⊢
      have h := hs ha hb hα hβ hαβ
      rw [smul_add, smul_add, add_add_add_comm] at h
      rw [← Convex.combo_self hαβ φ₀]
      exact h
    have hKball : ∀ r : ℝ, 0 < r →
        IsClosed ((fun ψ : WeakDual 𝕜 E => ψ + φ₀) ⁻¹' s ∩
          WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) r) := by
      intro r hr
      have hrr : 0 < r + ‖WeakDual.toStrongDual φ₀‖ :=
        lt_of_lt_of_le hr (le_add_of_nonneg_right (norm_nonneg _))
      have hset : (fun ψ : WeakDual 𝕜 E => ψ + φ₀) ⁻¹' s ∩
            WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) r
          = (fun ψ : WeakDual 𝕜 E => ψ + φ₀) ⁻¹'
              (s ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E)
                (r + ‖WeakDual.toStrongDual φ₀‖))
            ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) r := by
        ext ψ
        simp only [Set.mem_inter_iff, Set.mem_preimage]
        constructor
        · rintro ⟨hψs, hψr⟩
          refine ⟨⟨hψs, ?_⟩, hψr⟩
          have hle : ‖WeakDual.toStrongDual ψ‖ ≤ r := mem_closedBall_zero_iff.mp hψr
          have hadd := norm_add_le (WeakDual.toStrongDual ψ) (WeakDual.toStrongDual φ₀)
          rw [← map_add] at hadd
          rw [mem_closedBall_zero_iff]
          linarith
        · rintro ⟨⟨hψs, -⟩, hψr⟩
          exact ⟨hψs, hψr⟩
      rw [hset]
      exact ((hball (r + ‖WeakDual.toStrongDual φ₀‖) hrr).preimage
        (continuous_id.add continuous_const)).inter (ks_isClosed_ball r)
    have h0cl : (0 : WeakDual 𝕜 E) ∈ closure ((fun ψ => ψ + φ₀) ⁻¹' s) := by
      have hmem : (Homeomorph.addRight φ₀) (0 : WeakDual 𝕜 E) ∈ closure s := by
        have h00 : (Homeomorph.addRight φ₀) (0 : WeakDual 𝕜 E) = φ₀ := by simp
        rw [h00]
        exact hφ₀
      have hpre : (0 : WeakDual 𝕜 E) ∈ (Homeomorph.addRight φ₀) ⁻¹' closure s := hmem
      rw [(Homeomorph.addRight φ₀).preimage_closure] at hpre
      have hKK : (Homeomorph.addRight φ₀) ⁻¹' s = (fun ψ => ψ + φ₀) ⁻¹' s := by
        rw [Homeomorph.coe_addRight]
      rw [hKK] at hpre
      exact hpre
    exact (ks_zero_notMem_closure hKconv h0K hKball) h0cl

end MathlibExt.Analysis.FunctionalAnalysis.BanachSpaceWanted
