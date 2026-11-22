/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointDeflation
import MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointFiniteEigenvalues


public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.Sequences

@[expose] public section

open ContinuousLinearMap InnerProductSpace
open Filter Topology
open scoped ComplexConjugate

namespace MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointMaximumPrinciple

/-!
# Maximum principle for compact self-adjoint operators

The nonzero eigenvalues of a compact self-adjoint operator on a Hilbert
space admit either a finite or an infinite enumeration, counted with
multiplicity and ordered by decreasing modulus. At each step the modulus
is the maximum absolute quadratic form on unit vectors orthogonal to the
earlier eigenvectors, attained at the chosen eigenvector. In the infinite
case the moduli tend to zero. The operator vanishes on the common orthogonal
complement of the enumerated vectors, so no nonzero eigenspace is omitted.

`exists_nonzero_eigenvalue_enumeration` uses `Fin N` for the terminating
alternative (including `N = 0`) and `ℕ` for the infinite alternative. It
applies in finite-dimensional spaces too. `exists_ordered_eigenvalue_sequence`
retains the earlier zero-padded sequence on an infinite-dimensional space.

The proof uses the current public deflation and finite-eigenvalue APIs.
One private iteration permits padding only for the earlier corollary.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/targets.yaml`,
Theorem (Maximum principle), May 11, 2021. The adjacent v1 declaration
`SpectralTheory.compact_selfAdjoint_maximum_principle` is an unproved
infinite-dimensional specialization, not the full source statement.
-/

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

private theorem orthogonalComplement_invariant {T : H →L[𝕜] H} (hT : IsSelfAdjoint T)
    {E : Submodule 𝕜 H} (hE : ∀ x ∈ E, T x ∈ E) :
    ∀ v ∈ Eᗮ, T v ∈ Eᗮ := by
  have hsym : (T : H →ₗ[𝕜] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  intro v hv
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  have h0 : @inner 𝕜 H _ (T u) v = 0 := hv (T u) (hE u hu)
  have h0' : @inner 𝕜 H _ ((T : H →ₗ[𝕜] H) u) v = 0 := h0
  rw [hsym u v] at h0'
  exact h0'

private theorem exists_next_eigenvector_of_invariant_max {S : Submodule 𝕜 H}
    [S.HasOrthogonalProjection] {T : H →L[𝕜] H} (hT : IsSelfAdjoint T)
    (hc : IsCompactOperator (T : H → H)) (hS : ∀ x ∈ S, T x ∈ S)
    (hT₁ : S.starProjection ∘L T ∘L S.starProjection ≠ 0) :
    ∃ r : ℝ, ∃ v : H, ‖v‖ = 1 ∧ v ∈ S ∧ T v = (r : 𝕜) • v ∧ r ≠ 0 ∧
      (∀ x ∈ S, ‖x‖ = 1 → ‖⟪T x, x⟫_𝕜‖ ≤ |r|) := by
  obtain ⟨r, v, hv_norm, hvS, hv_eig, hr, -⟩ :=
    CompactSelfAdjointDeflation.exists_next_eigenvector_of_invariant hT hc hS hT₁
  have hr0 : r ≠ 0 := by
    intro h
    have hnorm : ‖S.starProjection ∘L T ∘L S.starProjection‖ = 0 := by
      simpa [h] using hr.symm
    exact hT₁ (norm_eq_zero.mp hnorm)
  refine ⟨r, v, hv_norm, hvS, hv_eig, hr0, ?_⟩
  intro x hxS hx1
  have hT₁x : (S.starProjection ∘L T ∘L S.starProjection) x = T x := by
    simp only [ContinuousLinearMap.comp_apply]
    rw [Submodule.starProjection_eq_self_iff.mpr hxS,
      Submodule.starProjection_eq_self_iff.mpr (hS x hxS)]
  have hle :=
    (S.starProjection ∘L T ∘L S.starProjection).rayleighQuotient_le_norm x
  have hRQ : (S.starProjection ∘L T ∘L S.starProjection).rayleighQuotient x
      = RCLike.re ⟪T x, x⟫_𝕜 := by
    show (S.starProjection ∘L T ∘L S.starProjection).reApplyInnerSelf x / ‖x‖ ^ 2 = _
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, hT₁x, hx1]
    simp
  have hnorm_inner : ‖⟪T x, x⟫_𝕜‖ = |RCLike.re ⟪T x, x⟫_𝕜| := by
    have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
    have hreal : ⟪T x, x⟫_𝕜 = (RCLike.re ⟪T x, x⟫_𝕜 : 𝕜) := by
      have h := hsym.coe_reApplyInnerSelf_apply x
      rw [ContinuousLinearMap.reApplyInnerSelf_apply] at h
      exact h.symm
    conv_lhs => rw [hreal]
    rw [RCLike.norm_ofReal]
  rw [hnorm_inner, ← hRQ, hr]
  exact hle

private def NextProps (T : H →L[𝕜] H) (pad : Bool) (f : ℕ → ℝ × H)
    (n : ℕ) (p : ℝ × H) : Prop :=
  ((p.1 ≠ 0 ∨ pad = true) → ‖p.2‖ = 1) ∧
  T p.2 = (p.1 : 𝕜) • p.2 ∧
  (∀ j < n, ⟪p.2, (f j).2⟫_𝕜 = 0) ∧
  (∀ x : H, ‖x‖ = 1 → (∀ j < n, ⟪x, (f j).2⟫_𝕜 = 0) →
    ‖⟪T x, x⟫_𝕜‖ ≤ |p.1|) ∧
  (p.1 = 0 → ∀ x : H, (∀ j < n, ⟪x, (f j).2⟫_𝕜 = 0) → T x = 0)

private def StepProps (T : H →L[𝕜] H) (pad : Bool) (f : ℕ → ℝ × H)
    (i : ℕ) : Prop := NextProps T pad f i (f i)

omit [CompleteSpace H] in
private theorem stepProps_congr {T : H →L[𝕜] H} {pad : Bool}
    {f g : ℕ → ℝ × H} {i : ℕ} (h : ∀ j ≤ i, f j = g j)
    (hf : StepProps T pad f i) : StepProps T pad g i := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hf
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← h i le_rfl]
    exact h1
  · rw [← h i le_rfl]
    exact h2
  · intro j hj
    rw [← h i le_rfl, ← h j (le_of_lt hj)]
    exact h3 j hj
  · intro x hx1 hxorth
    rw [← h i le_rfl]
    apply h4 x hx1
    intro j hj
    simpa only [h j (le_of_lt hj)] using hxorth j hj
  · intro h0 x hxorth
    rw [← h i le_rfl] at h0
    apply h5 h0 x
    intro j hj
    simpa only [h j (le_of_lt hj)] using hxorth j hj

omit [CompleteSpace H] in
private theorem stepProps_update_self {T : H →L[𝕜] H} {pad : Bool}
    {f : ℕ → ℝ × H} {n : ℕ} {p : ℝ × H} (hp : NextProps T pad f n p) :
    StepProps T pad (Function.update f n p) n := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Function.update_self] using h1
  · simpa only [Function.update_self] using h2
  · intro j hj
    rw [Function.update_self, Function.update_of_ne (ne_of_lt hj)]
    exact h3 j hj
  · intro x hx1 hxorth
    rw [Function.update_self]
    apply h4 x hx1
    intro j hj
    simpa only [Function.update_of_ne (ne_of_lt hj)] using hxorth j hj

  · intro h0 x hxorth
    rw [Function.update_self] at h0
    apply h5 h0 x
    intro j hj
    simpa only [Function.update_of_ne (ne_of_lt hj)] using hxorth j hj

omit [CompleteSpace H] in
private theorem mem_orthogonal_span_range {ι : Type*} {u : ι → H} {x : H} :
    x ∈ (Submodule.span 𝕜 (Set.range u))ᗮ ↔ ∀ i, ⟪x, u i⟫_𝕜 = 0 := by
  constructor
  · intro hx i
    exact Submodule.inner_left_of_mem_orthogonal
      (Submodule.subset_span (Set.mem_range_self i)) hx
  · intro hx
    rw [Submodule.mem_orthogonal']
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz => obtain ⟨i, rfl⟩ := hz; exact hx i
    | zero => simp
    | add y z _ _ hy hz => rw [inner_add_right, hy, hz, add_zero]
    | smul a y _ hy => rw [inner_smul_right, hy, mul_zero]

set_option linter.style.haveILetI false in
private theorem exists_next_pair {T : H →L[𝕜] H} {pad : Bool}
    (hT : IsSelfAdjoint T) (hc : IsCompactOperator (T : H → H))
    (hpad : pad = true → ¬ FiniteDimensional 𝕜 H)
    {n : ℕ} {f : ℕ → ℝ × H} (hf : ∀ i < n, StepProps T pad f i) :
    ∃ p : ℝ × H, NextProps T pad f n p := by
  classical
  let u : Fin n → H := fun i => (f i.1).2
  let K : Submodule 𝕜 H := Submodule.span 𝕜 (Set.range u)
  have hKinv : ∀ y ∈ K, T y ∈ K := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        rw [(hf i.1 i.2).2.1]
        exact Submodule.smul_mem K _ (Submodule.subset_span ⟨i, rfl⟩)
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul a y _ hy => rw [map_smul]; exact Submodule.smul_mem K _ hy
  have hSinv := orthogonalComplement_invariant hT hKinv
  have hxS : ∀ x : H, (∀ j < n, ⟪x, (f j).2⟫_𝕜 = 0) → x ∈ Kᗮ := by
    intro x hx
    exact mem_orthogonal_span_range.mpr (fun i => hx i.1 i.2)
  by_cases hne : ∃ x ∈ Kᗮ, T x ≠ 0
  · have hcomp : Kᗮ.starProjection ∘L T ∘L Kᗮ.starProjection ≠ 0 := by
      intro h0
      obtain ⟨x, hx, hTx⟩ := hne
      have h : (Kᗮ.starProjection ∘L T ∘L Kᗮ.starProjection) x = 0 := by
        rw [h0]; simp
      simp only [ContinuousLinearMap.comp_apply] at h
      rw [Submodule.starProjection_eq_self_iff.mpr hx,
        Submodule.starProjection_eq_self_iff.mpr (hSinv x hx)] at h
      exact hTx h
    obtain ⟨r, v, hv1, hvS, hvT, hr0, hmax⟩ :=
      exists_next_eigenvector_of_invariant_max hT hc hSinv hcomp
    refine ⟨(r, v), fun _ => hv1, hvT, ?_, ?_, ?_⟩
    · intro j hj
      exact mem_orthogonal_span_range.mp hvS ⟨j, hj⟩
    · intro x hx1 hxorth
      exact hmax x (hxS x hxorth) hx1
    · intro h0
      exact False.elim (hr0 h0)
  · push Not at hne
    have hstop : ∀ x : H, (∀ j < n, ⟪x, (f j).2⟫_𝕜 = 0) → T x = 0 :=
      fun x hx => hne x (hxS x hx)
    by_cases hp : pad = true
    · have hKfin : FiniteDimensional 𝕜 ↥K := by
        dsimp [K]
        exact FiniteDimensional.span_of_finite 𝕜 (Set.finite_range u)
      have hS_ne : Kᗮ ≠ ⊥ := by
        intro hS0
        have hKtop : K = ⊤ := by
          have h1 : K.topologicalClosure = ⊤ := by
            have h2 : Kᗮᗮ = (⊥ : Submodule 𝕜 H)ᗮ := by rw [hS0]
            rw [Submodule.orthogonal_orthogonal_eq_closure] at h2
            rw [h2]
            simp
          rw [← (Submodule.closed_of_finiteDimensional K).submodule_topologicalClosure_eq]
          exact h1
        have hfinH : FiniteDimensional 𝕜 H := by
          have h2 : FiniteDimensional 𝕜 ↥(⊤ : Submodule 𝕜 H) := by
            rw [← hKtop]; exact hKfin
          haveI := h2
          exact LinearEquiv.finiteDimensional Submodule.topEquiv
        exact hpad hp hfinH
      obtain ⟨w, hwS, hwne⟩ := (Submodule.ne_bot_iff _).mp hS_ne
      let v : H := ((‖w‖⁻¹ : ℝ) : 𝕜) • w
      have hvS : v ∈ Kᗮ := Submodule.smul_mem Kᗮ _ hwS
      refine ⟨(0, v), ?_, ?_, ?_, ?_, fun _ => hstop⟩
      · intro _
        dsimp [v]
        rw [norm_smul, RCLike.norm_ofReal,
          abs_of_nonneg (inv_nonneg.mpr (norm_nonneg w)),
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hwne)]
      · rw [hne v hvS]; simp
      · intro j hj
        exact mem_orthogonal_span_range.mp hvS ⟨j, hj⟩
      · intro x _ hxorth
        rw [hstop x hxorth]; simp
    · refine ⟨(0, 0), ?_, ?_, ?_, ?_, fun _ => hstop⟩
      · rintro (h | h)
        · exact False.elim (h rfl)
        · exact False.elim (hp h)
      · simp
      · simp
      · intro x _ hxorth
        rw [hstop x hxorth]; simp

omit [CompleteSpace H] in
private theorem nextPair_exists (T : H →L[𝕜] H) (pad : Bool)
    (f : ℕ → ℝ × H) (n : ℕ) :
    ∃ p : ℝ × H, NextProps T pad f n p ∨ ¬ ∃ p', NextProps T pad f n p' := by
  by_cases h : ∃ p, NextProps T pad f n p
  · obtain ⟨p, hp⟩ := h
    exact ⟨p, Or.inl hp⟩
  · exact ⟨(0, 0), Or.inr h⟩

private noncomputable def nextPair (T : H →L[𝕜] H) (pad : Bool)
    (f : ℕ → ℝ × H) (n : ℕ) : ℝ × H :=
  Classical.choose (nextPair_exists T pad f n)

private theorem nextPair_props {T : H →L[𝕜] H} {pad : Bool}
    (hT : IsSelfAdjoint T) (hc : IsCompactOperator (T : H → H))
    (hpad : pad = true → ¬ FiniteDimensional 𝕜 H)
    {n : ℕ} {f : ℕ → ℝ × H} (hf : ∀ i < n, StepProps T pad f i) :
    NextProps T pad f n (nextPair T pad f n) := by
  have hex : ∃ p, NextProps T pad f n p := exists_next_pair hT hc hpad hf
  have hspec : NextProps T pad f n (nextPair T pad f n) ∨
      ¬ ∃ p', NextProps T pad f n p' :=
    Classical.choose_spec (nextPair_exists T pad f n)
  exact hspec.resolve_right (not_not.mpr hex)

private noncomputable def seqF (T : H →L[𝕜] H) (pad : Bool) : ℕ → (ℕ → ℝ × H)
  | 0 => fun _ => (0, 0)
  | n + 1 => Function.update (seqF T pad n) n (nextPair T pad (seqF T pad n) n)

private theorem seqF_valid {T : H →L[𝕜] H} {pad : Bool}
    (hT : IsSelfAdjoint T) (hc : IsCompactOperator (T : H → H))
    (hpad : pad = true → ¬ FiniteDimensional 𝕜 H)
    (n : ℕ) : ∀ i < n, StepProps T pad (seqF T pad n) i := by
  induction n with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
      intro i hi
      by_cases hin : i = n
      · subst hin
        apply stepProps_update_self
        exact nextPair_props hT hc hpad ih
      · have hi' : i < n := by omega
        apply stepProps_congr _ (ih i hi')
        intro j hj
        have hj' : j ≠ n := by omega
        simp [seqF, Function.update_of_ne hj']

omit [CompleteSpace H] in
private theorem seqF_stable (T : H →L[𝕜] H) (pad : Bool)
    {i n m : ℕ} (hi : i < n) (hnm : n ≤ m) :
    seqF T pad m i = seqF T pad n i := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
      simp only [seqF, Function.update_of_ne (show i ≠ m from by omega)]
      exact ih

private noncomputable def eigSeq (T : H →L[𝕜] H) (pad : Bool) (n : ℕ) : ℝ :=
  (seqF T pad (n + 1) n).1

private noncomputable def eigVec (T : H →L[𝕜] H) (pad : Bool) (n : ℕ) : H :=
  (seqF T pad (n + 1) n).2

private theorem stepProps_eig {T : H →L[𝕜] H} {pad : Bool}
    (hT : IsSelfAdjoint T) (hc : IsCompactOperator (T : H → H))
    (hpad : pad = true → ¬ FiniteDimensional 𝕜 H) (i : ℕ) :
    StepProps T pad (fun j => (eigSeq T pad j, eigVec T pad j)) i := by
  apply stepProps_congr _ (seqF_valid hT hc hpad (i + 1) i (Nat.lt_succ_self i))
  intro j hj
  show seqF T pad (i + 1) j = (eigSeq T pad j, eigVec T pad j)
  rw [seqF_stable T pad (Nat.lt_succ_self j) (show j + 1 ≤ i + 1 from by omega)]
  exact Prod.mk.eta.symm

private theorem orthonormal_eigVec_comp {T : H →L[𝕜] H} {pad : Bool}
    (hT : IsSelfAdjoint T) (hc : IsCompactOperator (T : H → H))
    (hpad : pad = true → ¬ FiniteDimensional 𝕜 H)
    {ι : Type*} (e : ι → ℕ) (he : Function.Injective e)
    (hunit : ∀ i, eigSeq T pad (e i) ≠ 0 ∨ pad = true) :
    Orthonormal 𝕜 (fun i => eigVec T pad (e i)) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl, inner_self_eq_norm_sq_to_K,
      (stepProps_eig hT hc hpad (e i)).1 (hunit i)]
    simp
  · rw [ite_eq_right hij]
    have hij' : e i ≠ e j := fun h => hij (he h)
    rcases lt_or_gt_of_ne hij' with h | h
    · have h2 : ⟪eigVec T pad (e j), eigVec T pad (e i)⟫_𝕜 = 0 :=
        (stepProps_eig hT hc hpad (e j)).2.2.1 (e i) h
      rw [← inner_conj_symm, h2, map_zero]
    · exact (stepProps_eig hT hc hpad (e i)).2.2.1 (e j) h

private theorem rayleigh_at_eigVec {T : H →L[𝕜] H} {pad : Bool}
    (hT : IsSelfAdjoint T) (hc : IsCompactOperator (T : H → H))
    (hpad : pad = true → ¬ FiniteDimensional 𝕜 H) (n : ℕ) :
    ‖⟪T (eigVec T pad n), eigVec T pad n⟫_𝕜‖ = |eigSeq T pad n| := by
  have hT' : T (eigVec T pad n) = (eigSeq T pad n : 𝕜) • eigVec T pad n :=
    (stepProps_eig hT hc hpad n).2.1
  by_cases hs : eigSeq T pad n = 0
  · rw [hT', hs]
    simp
  · have hn1 := (stepProps_eig hT hc hpad n).1 (Or.inl hs)
    rw [hT', inner_smul_left, RCLike.conj_ofReal,
      inner_self_eq_norm_sq_to_K, hn1]
    simp

private theorem abs_eigSeq_antitone {T : H →L[𝕜] H} {pad : Bool}
    (hT : IsSelfAdjoint T) (hc : IsCompactOperator (T : H → H))
    (hpad : pad = true → ¬ FiniteDimensional 𝕜 H) :
    Antitone (fun n => |eigSeq T pad n|) := by
  apply antitone_nat_of_succ_le
  intro n
  by_cases hs : eigSeq T pad (n + 1) = 0
  · simp [hs]
  · rw [← rayleigh_at_eigVec hT hc hpad (n + 1)]
    apply (stepProps_eig hT hc hpad n).2.2.2.1
    · exact (stepProps_eig hT hc hpad (n + 1)).1 (Or.inl hs)
    · intro j hj
      exact (stepProps_eig hT hc hpad (n + 1)).2.2.1 j (by omega)

private theorem tendsto_abs_eigSeq {T : H →L[𝕜] H} {pad : Bool} (hT : IsSelfAdjoint T)
    (hc : IsCompactOperator (T : H → H)) (hpad : pad = true → ¬ FiniteDimensional 𝕜 H) :
    Tendsto (fun n => |eigSeq T pad n|) atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  by_contra hcon
  push Not at hcon
  have hge : ∀ n, ε ≤ |eigSeq T pad n| := by
    intro n
    obtain ⟨m, hmn, hm⟩ := hcon n
    have hm' : ε ≤ |eigSeq T pad m| := by
      have h2 := hm
      rw [dist_eq_norm] at h2
      simpa using h2
    exact le_trans hm' (abs_eigSeq_antitone hT hc hpad hmn)
  have hne : ∀ n, eigSeq T pad n ≠ 0 := by
    intro n h0
    have h := hge n
    rw [h0, abs_zero] at h
    exact (not_lt_of_ge h) hε
  have hnorm : ∀ n, ‖eigVec T pad n‖ = 1 :=
    fun n => (stepProps_eig hT hc hpad n).1 (Or.inl (hne n))
  have huorth : Orthonormal 𝕜 (eigVec T pad) :=
    orthonormal_eigVec_comp hT hc hpad id (by intro i j h; exact h)
      (fun n => Or.inl (hne n))
  have hfin := CompactSelfAdjointFiniteEigenvalues.finite_eigenvalues_of_ge hT hc hε
  set f : ℕ → 𝕜 := fun n => (eigSeq T pad n : 𝕜) with hf
  have hfA : ∀ n, f n ∈ {μ : 𝕜 | Module.End.HasEigenvalue (T : H →ₗ[𝕜] H) μ ∧
      ε ≤ ‖μ‖} := by
    intro n
    refine ⟨?_, ?_⟩
    · apply Module.End.hasEigenvalue_of_hasEigenvector
      refine ⟨Module.End.mem_eigenspace_iff.mpr (stepProps_eig hT hc hpad n).2.1, ?_⟩
      intro h0
      change eigVec T pad n = 0 at h0
      have hn1 := hnorm n
      rw [h0, norm_zero] at hn1
      exact zero_ne_one hn1
    · rw [hf, RCLike.norm_ofReal]
      exact hge n
  obtain ⟨μ, hμinf⟩ : ∃ μ, {n | f n = μ}.Infinite := by
    by_contra hnone
    push Not at hnone
    have hcover : (Set.univ : Set ℕ) =
        ⋃ μ ∈ {μ : 𝕜 | Module.End.HasEigenvalue (T : H →ₗ[𝕜] H) μ ∧ ε ≤ ‖μ‖},
          {n | f n = μ} := by
      ext x
      simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq, true_iff]
      exact ⟨f x, hfA x, rfl⟩
    have huniv : (Set.univ : Set ℕ).Finite := by
      rw [hcover]
      exact hfin.biUnion (fun μ _ => hnone μ)
    exact Set.Infinite.not_finite Set.infinite_univ huniv
  have hμ0 : μ ≠ 0 := by
    intro h0
    obtain ⟨n, hn⟩ := hμinf.nonempty
    have hmem : ε ≤ ‖μ‖ := by
      have h2 := (hfA n).2
      have hn' : f n = μ := hn
      rw [hn'] at h2
      exact h2
    rw [h0, norm_zero] at hmem
    exact not_lt_of_ge hmem hε
  have hfinEig : FiniteDimensional 𝕜
      ↥(Module.End.eigenspace (T : H →ₗ[𝕜] H) μ) :=
    ContinuousLinearMap.finite_dimensional_eigenspace hc μ hμ0
  have hmem : ∀ i : {n | f n = μ},
      eigVec T pad i.1 ∈ Module.End.eigenspace (T : H →ₗ[𝕜] H) μ := by
    intro i
    apply Module.End.mem_eigenspace_iff.mpr
    have h1 := (stepProps_eig hT hc hpad i.1).2.1
    have h2 : (eigSeq T pad i.1 : 𝕜) = μ := i.2
    rw [h2] at h1
    exact h1
  set v : {n | f n = μ} → ↥(Module.End.eigenspace (T : H →ₗ[𝕜] H) μ) :=
    fun i => ⟨eigVec T pad i.1, hmem i⟩ with hv
  have horth : Orthonormal 𝕜 v := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [Submodule.coe_inner]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, inner_self_eq_norm_sq_to_K,
        hnorm i.1]
      simp
    · have hij' : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Subtype.ext h)
      rw [ite_eq_right hij]
      have h2 := orthonormal_iff_ite.mp (huorth) i.1 j.1
      rw [ite_eq_right hij'] at h2
      exact h2
  have hlin : LinearIndependent 𝕜 v := horth.linearIndependent
  have hfinI : Finite {n | f n = μ} := LinearIndependent.finite hlin
  exact (not_finite_iff_infinite.mpr (Set.infinite_coe_iff.mpr hμinf)) hfinI


private theorem vanishes_on_common_orthogonal {T : H →L[𝕜] H} {pad : Bool}
    (hT : IsSelfAdjoint T) (hc : IsCompactOperator (T : H → H))
    (hpad : pad = true → ¬ FiniteDimensional 𝕜 H)
    (x : H) (hx : ∀ n, ⟪x, eigVec T pad n⟫_𝕜 = 0) : T x = 0 := by
  classical
  by_contra hTx
  let K : Submodule 𝕜 H := Submodule.span 𝕜 (Set.range (eigVec T pad))
  have hKinv : ∀ y ∈ K, T y ∈ K := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨n, rfl⟩ := hz
        rw [(stepProps_eig hT hc hpad n).2.1]
        exact Submodule.smul_mem K _ (Submodule.subset_span ⟨n, rfl⟩)
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul a y _ hy => rw [map_smul]; exact Submodule.smul_mem K _ hy
  have hSinv := orthogonalComplement_invariant hT hKinv
  have hxS : x ∈ Kᗮ := mem_orthogonal_span_range.mpr hx
  have hcomp : Kᗮ.starProjection ∘L T ∘L Kᗮ.starProjection ≠ 0 := by
    intro h0
    have h : (Kᗮ.starProjection ∘L T ∘L Kᗮ.starProjection) x = 0 := by
      rw [h0]; simp
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [Submodule.starProjection_eq_self_iff.mpr hxS,
      Submodule.starProjection_eq_self_iff.mpr (hSinv x hxS)] at h
    exact hTx h
  obtain ⟨r, v, hv1, hvS, hvT, hr0, -⟩ :=
    exists_next_eigenvector_of_invariant_max hT hc hSinv hcomp
  have hvorth : ∀ n, ⟪v, eigVec T pad n⟫_𝕜 = 0 :=
    mem_orthogonal_span_range.mp hvS
  have hray : ‖⟪T v, v⟫_𝕜‖ = |r| := by
    rw [hvT, inner_smul_left, RCLike.conj_ofReal,
      inner_self_eq_norm_sq_to_K, hv1]
    simp
  have hrle : ∀ n, |r| ≤ |eigSeq T pad n| := by
    intro n
    rw [← hray]
    exact (stepProps_eig hT hc hpad n).2.2.2.1 v hv1 (fun j _ => hvorth j)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (tendsto_abs_eigSeq hT hc hpad)
    |r| (abs_pos.mpr hr0)
  have hnear : |eigSeq T pad N| < |r| := by
    have h := hN N le_rfl
    rw [dist_eq_norm, sub_zero] at h
    simpa using h
  exact (not_lt_of_ge (hrle N)) hnear

/-- The maximum principle with both terminating and nonterminating alternatives.
The finite alternative includes the empty family for the zero operator. Only
the infinite alternative asserts convergence. In both alternatives `T` vanishes
on the common orthogonal complement, so the nonzero eigenspaces are exhausted. -/
theorem exists_nonzero_eigenvalue_enumeration {T : H →L[𝕜] H}
    (hT : IsSelfAdjoint T) (hc : IsCompactOperator (T : H → H)) :
    (∃ (N : ℕ) (s : Fin N → ℝ) (u : Fin N → H),
      (∀ i, s i ≠ 0) ∧ (∀ i, T (u i) = (s i : 𝕜) • u i) ∧
      Orthonormal 𝕜 u ∧ Antitone (fun i => |s i|) ∧
      (∀ i, (∀ x : H, ‖x‖ = 1 → (∀ j < i, ⟪x, u j⟫_𝕜 = 0) →
        ‖⟪T x, x⟫_𝕜‖ ≤ |s i|) ∧ ‖⟪T (u i), u i⟫_𝕜‖ = |s i|) ∧
      ∀ x : H, (∀ i, ⟪x, u i⟫_𝕜 = 0) → T x = 0) ∨
    (∃ (s : ℕ → ℝ) (u : ℕ → H),
      (∀ n, s n ≠ 0) ∧ (∀ n, T (u n) = (s n : 𝕜) • u n) ∧
      Orthonormal 𝕜 u ∧ Antitone (fun n => |s n|) ∧
      Tendsto (fun n => |s n|) atTop (𝓝 0) ∧
      (∀ n, (∀ x : H, ‖x‖ = 1 → (∀ j < n, ⟪x, u j⟫_𝕜 = 0) →
        ‖⟪T x, x⟫_𝕜‖ ≤ |s n|) ∧ ‖⟪T (u n), u n⟫_𝕜‖ = |s n|) ∧
      ∀ x : H, (∀ n, ⟪x, u n⟫_𝕜 = 0) → T x = 0) := by
  classical
  let s : ℕ → ℝ := eigSeq T false
  let u : ℕ → H := eigVec T false
  have hpad : false = true → ¬ FiniteDimensional 𝕜 H := by intro h; cases h
  have hf := stepProps_eig hT hc hpad
  by_cases hz : ∃ n, s n = 0
  · left
    let N := Nat.find hz
    have hne : ∀ i : Fin N, s i.1 ≠ 0 := fun i => Nat.find_min hz i.2
    refine ⟨N, (fun i => s i.1), (fun i => u i.1), hne, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact (hf i.1).2.1
    · exact orthonormal_eigVec_comp hT hc hpad Fin.val
        (by intro i j h; exact Fin.ext h) (fun i => Or.inl (hne i))
    · intro i j hij
      exact abs_eigSeq_antitone hT hc hpad hij
    · intro i
      refine ⟨?_, rayleigh_at_eigVec hT hc hpad i.1⟩
      intro x hx1 hxorth
      apply (hf i.1).2.2.2.1 x hx1
      intro j hj
      exact hxorth ⟨j, lt_trans hj i.2⟩ hj
    · intro x hxorth
      apply (hf N).2.2.2.2 (Nat.find_spec hz) x
      intro j hj
      exact hxorth ⟨j, hj⟩
  · right
    have hne : ∀ n, s n ≠ 0 := by simpa only [not_exists] using hz
    refine ⟨s, u, hne, ?_, ?_, abs_eigSeq_antitone hT hc hpad,
      tendsto_abs_eigSeq hT hc hpad, ?_, ?_⟩
    · intro n
      exact (hf n).2.1
    · exact orthonormal_eigVec_comp hT hc hpad id
        (by intro i j h; exact h) (fun n => Or.inl (hne n))
    · intro n
      exact ⟨(hf n).2.2.2.1, rayleigh_at_eigVec hT hc hpad n⟩
    · exact vanishes_on_common_orthogonal hT hc hpad

/-- On a finite-dimensional Hilbert space the nonzero maximum-principle
enumeration terminates. Its common orthogonal complement is killed by `T`. -/
theorem exists_finite_eigenvalue_enumeration [FiniteDimensional 𝕜 H]
    {T : H →L[𝕜] H} (hT : IsSelfAdjoint T) (hc : IsCompactOperator (T : H → H)) :
    ∃ (N : ℕ) (s : Fin N → ℝ) (u : Fin N → H),
      (∀ i, s i ≠ 0) ∧ (∀ i, T (u i) = (s i : 𝕜) • u i) ∧
      Orthonormal 𝕜 u ∧ Antitone (fun i => |s i|) ∧
      (∀ i, (∀ x : H, ‖x‖ = 1 → (∀ j < i, ⟪x, u j⟫_𝕜 = 0) →
        ‖⟪T x, x⟫_𝕜‖ ≤ |s i|) ∧ ‖⟪T (u i), u i⟫_𝕜‖ = |s i|) ∧
      ∀ x : H, (∀ i, ⟪x, u i⟫_𝕜 = 0) → T x = 0 := by
  rcases exists_nonzero_eigenvalue_enumeration hT hc with h | ⟨s, u, -, -, horth, -⟩
  · exact h
  · exact False.elim ((not_finite_iff_infinite.mpr inferInstance)
      horth.linearIndependent.finite)

/-- A zero-padded maximum-principle sequence on an infinite-dimensional
Hilbert space. This preserves the earlier public API: after all nonzero
eigenvalues have been enumerated, unit kernel vectors may carry eigenvalue
zero. The nonzero terminating version is `exists_nonzero_eigenvalue_enumeration`. -/
theorem exists_ordered_eigenvalue_sequence {T : H →L[𝕜] H} (hT : IsSelfAdjoint T)
    (hc : IsCompactOperator (T : H → H)) (hInf : ¬ FiniteDimensional 𝕜 H) :
    ∃ (s : ℕ → ℝ) (u : ℕ → H),
      (∀ n, T (u n) = (s n : 𝕜) • u n) ∧
      Orthonormal 𝕜 u ∧
      (∀ n, |s (n + 1)| ≤ |s n|) ∧
      Tendsto (fun n => |s n|) atTop (𝓝 0) ∧
      ∀ n, (∀ x : H, ‖x‖ = 1 → (∀ j < n, ⟪x, u j⟫_𝕜 = 0) → ‖⟪T x, x⟫_𝕜‖ ≤ |s n|) ∧
        ‖⟪T (u n), u n⟫_𝕜‖ = |s n| := by
  have hpad : true = true → ¬ FiniteDimensional 𝕜 H := fun _ => hInf
  refine ⟨eigSeq T true, eigVec T true, ?_, ?_,
    (fun n => abs_eigSeq_antitone hT hc hpad (Nat.le_succ n)),
    tendsto_abs_eigSeq hT hc hpad, ?_⟩
  · intro n
    exact (stepProps_eig hT hc hpad n).2.1
  · exact orthonormal_eigVec_comp hT hc hpad id
      (by intro i j h; exact h) (fun _ => Or.inr rfl)
  · intro n
    exact ⟨(stepProps_eig hT hc hpad n).2.2.2.1,
      rayleigh_at_eigVec hT hc hpad n⟩

end MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointMaximumPrinciple
