/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

@[expose] public section

open Function Set Filter Topology

namespace MathlibExt.Analysis.InnerProductSpace.CompactFiniteRankApprox

/-!
# Finite-rank approximation of compact operators on Hilbert space

Every compact operator on a Hilbert space is a norm limit of finite-rank
operators. This is the form of the approximation theorem that needs no
self-adjointness, normality, or spectral theory: since the image of the
closed unit ball under a compact operator is contained in a compact set,
that image admits a finite `ε`-net; projecting orthogonally onto the span
of the net gives a finite-rank approximant, because the orthogonal
projection is the nearest point of the span (`Submodule.starProjection_minimal`).
No completeness hypothesis on `H` is needed: the only completeness used is
that of the finite-dimensional span, which is automatic.

This generalizes the MathlibExt result for compact *self-adjoint*
operators (`CompactSelfAdjointFiniteRankApprox.exists_finiteRank_approx`,
Batch 17), which was proved by truncating the eigenvalue expansion from
the spectral theorem. Mathlib itself stops short of approximation: it has
that compact operators form a closed subspace
(`isClosed_setOfPred_isCompactOperator`), but no finite-rank approximation
theorem for compact operators.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`,
the compact-operator material around the Fredholm alternative and the
spectral theorem (Theorem (Maximum principle), May 11, 2021). The v1
formalization states the spectral theorem only for compact self-adjoint
operators; the statement below drops self-adjointness entirely.
-/

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **Finite-rank approximation of compact operators.** Let $H$ be an inner product space over
$\mathbb{K}$, where $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$ ($H$ need not be complete),
and let $T$ be a compact bounded linear operator on $H$. For every real $\varepsilon > 0$ there
is a bounded linear operator $F$ on $H$ with finite-dimensional range such that
$\|T - F\| \le \varepsilon$.

The approximant is the composition of $T$ with the orthogonal projection onto the span of a
finite $\varepsilon$-net for the image of the closed unit ball. -/
theorem exists_finiteRank_approx (T : H →L[𝕜] H)
    (hc : IsCompactOperator (T : H → H)) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : H →L[𝕜] H,
      FiniteDimensional 𝕜 ↥(LinearMap.range (F : H →ₗ[𝕜] H)) ∧ ‖T - F‖ ≤ ε := by
  obtain ⟨K, hKcompact, hKT⟩ := hc.image_closedBall_subset_compact 1
  obtain ⟨t, htfin, htcover⟩ :=
    Metric.totallyBounded_iff.mp hKcompact.totallyBounded ε hε
  classical
  set M : Submodule 𝕜 H := Submodule.span 𝕜 t with hMdef
  have hMfin : FiniteDimensional 𝕜 M := FiniteDimensional.span_of_finite 𝕜 htfin
  have hMcomp : CompleteSpace M := FiniteDimensional.complete 𝕜 M
  set F : H →L[𝕜] H := M.starProjection ∘L T with hFdef
  have hrange : LinearMap.range (F : H →ₗ[𝕜] H) ≤ M := by
    rintro y ⟨x, rfl⟩
    simp [hFdef]
  refine ⟨F, Submodule.finiteDimensional_of_le hrange, ?_⟩
  have key : ∀ x : H, ‖x‖ ≤ 1 → ‖(T - F) x‖ ≤ ε := by
    intro x hx
    have hTxK : T x ∈ K :=
      hKT ⟨x, Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hx), rfl⟩
    obtain ⟨y, hyt, hyball⟩ := Set.mem_iUnion₂.mp (htcover hTxK)
    have hyM : y ∈ M := Submodule.subset_span hyt
    have hdist : ‖T x - y‖ < ε := by
      have h := Metric.mem_ball.mp hyball
      rwa [dist_eq_norm] at h
    have hmin : ‖T x - M.starProjection (T x)‖ =
        ⨅ z : M, ‖T x - (z : H)‖ :=
      M.starProjection_minimal (T x)
    have hbdd : BddBelow (Set.range (fun z : M => ‖T x - (z : H)‖)) :=
      ⟨0, by rintro _ ⟨z, rfl⟩; exact norm_nonneg _⟩
    have hle : (⨅ z : M, ‖T x - (z : H)‖) ≤ ‖T x - y‖ := ciInf_le hbdd ⟨y, hyM⟩
    have hEq : (T - F) x = T x - M.starProjection (T x) := by
      simp [hFdef]
    rw [hEq, hmin]
    exact le_of_lt (lt_of_le_of_lt hle hdist)
  exact ContinuousLinearMap.opNorm_le_of_unit_norm hε.le fun x hx => key x hx.le

/-- **Compact operators are norm limits of finite-rank operators.** Let $H$ be an inner product
space over $\mathbb{K}$, where $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$ ($H$ need not be
complete), and let $T$ be a compact bounded linear operator on $H$. Then there is a sequence
$(F_n)_{n \in \mathbb{N}}$ of bounded linear operators on $H$, each with finite-dimensional
range, such that $\|T - F_n\| \to 0$ as $n \to \infty$. -/
theorem exists_tendsto_finiteRank_approx (T : H →L[𝕜] H)
    (hc : IsCompactOperator (T : H → H)) :
    ∃ F : ℕ → H →L[𝕜] H,
      (∀ n, FiniteDimensional 𝕜 ↥(LinearMap.range (F n : H →ₗ[𝕜] H))) ∧
      Tendsto (fun n => ‖T - F n‖) atTop (𝓝 0) := by
  choose F hFfin hFnorm using
    fun (n : ℕ) => exists_finiteRank_approx T hc
      (show (0 : ℝ) < 1 / ((n : ℝ) + 1) from
        one_div_pos.mpr (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) one_pos))
  refine ⟨F, hFfin, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    tendsto_one_div_add_atTop_nhds_zero_nat (fun n => norm_nonneg _) hFnorm

end MathlibExt.Analysis.InnerProductSpace.CompactFiniteRankApprox
