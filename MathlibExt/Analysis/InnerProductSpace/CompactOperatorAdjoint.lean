/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

@[expose] public section

/-!
# Schauder's theorem: the adjoint of a compact operator is compact

For a bounded operator `T` between Hilbert spaces, `T` is compact if and
only if its adjoint `T†` is compact. This is Schauder's theorem.

The book (`v1/Atlas/IntroductionToFunctionalAnalysis`) develops the two
ingredients separately: bounded operators and their adjoints in the
adjoint-operator section (April 27, 2021, `(Ran A)⊥ = Null (A*)`), and
compact operators in the Fredholm-alternative and spectral sections
(May 11, 2021). Schauder's theorem itself is not stated in the book; it is
derived here from the book's compact-operator material plus the standard
finite-rank approximation argument:

* a compact operator is a norm limit of finite-rank operators, proved by
  projecting onto the span of a finite `ε`-net for the image of the closed
  unit ball (the orthogonal projection is the nearest point of the span);
* the adjoint of a finite-rank operator is compact, because such an operator
  factors through its (finite-dimensional) range, and the adjoint of the
  codomain-restricted factor has finite-dimensional domain, hence is compact;
* compact operators are closed under norm limits, and the adjoint map is
  continuous (indeed an isometry).

No completeness hypothesis on the spaces beyond the one needed to define
the adjoint is used in the finite-rank approximation step.
-/

open Function Set Filter Topology

namespace MathlibExt.Analysis.InnerProductSpace.CompactOperatorAdjoint

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Finite-rank approximation of a compact operator between Hilbert spaces:
for every `ε > 0` there is a bounded linear operator `G` of finite rank
with `‖T - G‖ ≤ ε`. The approximant is the composition of `T` with the
orthogonal projection onto the span of a finite `ε`-net for the image of
the closed unit ball. This is the two-space form of the approximation
theorem; the one-space form is Batch 27's
`CompactFiniteRankApprox.exists_finiteRank_approx`, re-proved here as a
`private` lemma since parallel batches cannot import each other. -/
private theorem exists_finiteRank_approx (T : E →L[𝕜] F)
    (hc : IsCompactOperator (T : E → F)) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : E →L[𝕜] F,
      FiniteDimensional 𝕜 ↥(LinearMap.range (G : E →ₗ[𝕜] F)) ∧ ‖T - G‖ ≤ ε := by
  obtain ⟨K, hKcompact, hKT⟩ := hc.image_closedBall_subset_compact 1
  obtain ⟨t, htfin, htcover⟩ :=
    Metric.totallyBounded_iff.mp hKcompact.totallyBounded ε hε
  classical
  set M : Submodule 𝕜 F := Submodule.span 𝕜 t with hMdef
  have hMfin : FiniteDimensional 𝕜 M := FiniteDimensional.span_of_finite 𝕜 htfin
  have hMcomp : CompleteSpace M := FiniteDimensional.complete 𝕜 M
  set G : E →L[𝕜] F := M.starProjection ∘L T with hGdef
  have hrange : LinearMap.range (G : E →ₗ[𝕜] F) ≤ M := by
    rintro y ⟨x, rfl⟩
    simp [hGdef]
  refine ⟨G, Submodule.finiteDimensional_of_le hrange, ?_⟩
  have key : ∀ x : E, ‖x‖ ≤ 1 → ‖(T - G) x‖ ≤ ε := by
    intro x hx
    have hTxK : T x ∈ K :=
      hKT ⟨x, Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hx), rfl⟩
    obtain ⟨y, hyt, hyball⟩ := Set.mem_iUnion₂.mp (htcover hTxK)
    have hyM : y ∈ M := Submodule.subset_span hyt
    have hdist : ‖T x - y‖ < ε := by
      have h := Metric.mem_ball.mp hyball
      rwa [dist_eq_norm] at h
    have hmin : ‖T x - M.starProjection (T x)‖ =
        ⨅ z : M, ‖T x - (z : F)‖ :=
      M.starProjection_minimal (T x)
    have hbdd : BddBelow (Set.range (fun z : M => ‖T x - (z : F)‖)) :=
      ⟨0, by rintro _ ⟨z, rfl⟩; exact norm_nonneg _⟩
    have hle : (⨅ z : M, ‖T x - (z : F)‖) ≤ ‖T x - y‖ := ciInf_le hbdd ⟨y, hyM⟩
    have hEq : (T - G) x = T x - M.starProjection (T x) := by
      simp [hGdef]
    rw [hEq, hmin]
    exact le_of_lt (lt_of_le_of_lt hle hdist)
  exact ContinuousLinearMap.opNorm_le_of_unit_norm hε.le fun x hx => key x hx.le

omit [CompleteSpace E] [CompleteSpace F] in
/-- Every compact operator between Hilbert spaces is the norm limit of a
sequence of finite-rank operators. -/
private theorem exists_tendsto_finiteRank_approx (T : E →L[𝕜] F)
    (hc : IsCompactOperator (T : E → F)) :
    ∃ Gn : ℕ → E →L[𝕜] F,
      (∀ n, FiniteDimensional 𝕜 ↥(LinearMap.range (Gn n : E →ₗ[𝕜] F))) ∧
      Tendsto Gn atTop (𝓝 T) := by
  choose Gn hGn_fin hGn_norm using
    fun (n : ℕ) => exists_finiteRank_approx T hc
      (show (0 : ℝ) < 1 / ((n : ℝ) + 1) from
        one_div_pos.mpr (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) one_pos))
  refine ⟨Gn, hGn_fin, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero_norm (fun n => by simpa [norm_sub_rev] using hGn_norm n)
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- The adjoint of a finite-rank operator between Hilbert spaces is compact.
The operator factors through its (finite-dimensional) range as
`T = i ∘L π`, so `T† = π† ∘L i†`, and `π†` is compact because its domain
is finite-dimensional (hence locally compact). -/
theorem isCompactOperator_adjoint_of_finiteRank {T : E →L[𝕜] F}
    (hT : FiniteDimensional 𝕜 ↥(LinearMap.range (T : E →ₗ[𝕜] F))) :
    IsCompactOperator (ContinuousLinearMap.adjoint T : F → E) := by
  classical
  set R : Submodule 𝕜 F := LinearMap.range (T : E →ₗ[𝕜] F) with hRdef
  set π : E →L[𝕜] R := T.codRestrict R (fun x => ⟨x, rfl⟩) with hπdef
  set i : R →L[𝕜] F := R.subtypeL with hidef
  have hfac : i ∘L π = T := by
    rw [hidef, hπdef]
    exact ContinuousLinearMap.subtypeL_comp_codRestrict T R _
  have hadj : ContinuousLinearMap.adjoint T = ContinuousLinearMap.adjoint π ∘L
      ContinuousLinearMap.adjoint i := by
    rw [← hfac, ContinuousLinearMap.adjoint_comp]
  have hπcomp : IsCompactOperator (ContinuousLinearMap.adjoint π : R → E) := by
    have hloc : LocallyCompactSpace R :=
      LocallyCompactSpace.of_finiteDimensional_of_complete 𝕜 R
    exact isCompactOperator_of_locallyCompactSpace_rng (ContinuousLinearMap.adjoint π)
  rw [hadj]
  exact hπcomp.comp_clm (ContinuousLinearMap.adjoint i)

/-- **Schauder's theorem.** The adjoint of a compact operator between
Hilbert spaces is compact. -/
theorem isCompactOperator_adjoint {T : E →L[𝕜] F}
    (hT : IsCompactOperator (T : E → F)) :
    IsCompactOperator (ContinuousLinearMap.adjoint T : F → E) := by
  obtain ⟨Gn, hGn_fin, hGn_tendsto⟩ := exists_tendsto_finiteRank_approx T hT
  have htend : Tendsto (fun n => ContinuousLinearMap.adjoint (Gn n)) atTop
      (𝓝 (ContinuousLinearMap.adjoint T)) :=
    (ContinuousLinearMap.adjoint.continuous.tendsto T).comp hGn_tendsto
  exact isCompactOperator_of_tendsto htend
    (Filter.Eventually.of_forall fun n => isCompactOperator_adjoint_of_finiteRank (hGn_fin n))

/-- **Schauder's theorem, iff form.** A bounded operator between Hilbert
spaces is compact if and only if its adjoint is compact. -/
theorem isCompactOperator_adjoint_iff {T : E →L[𝕜] F} :
    IsCompactOperator (ContinuousLinearMap.adjoint T : F → E) ↔
      IsCompactOperator (T : E → F) := by
  constructor
  · intro h
    rw [← ContinuousLinearMap.adjoint_adjoint T]
    exact isCompactOperator_adjoint h
  · exact isCompactOperator_adjoint

end MathlibExt.Analysis.InnerProductSpace.CompactOperatorAdjoint
