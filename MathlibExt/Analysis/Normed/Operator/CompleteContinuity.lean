/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Normed.Module.WeakConvergence
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

import Mathlib.Topology.Sequences
import Mathlib.Tactic.Linarith

/-!
# Complete continuity of compact operators

A compact operator is *completely continuous*: it sends weakly convergent
sequences to norm-convergent sequences. That is, if `T : E →L[𝕜] F` is
compact and `u n → x` weakly in `E`, then `T (u n) → T x` in norm in `F`.

This is a new proof of a standard companion result motivated by the
compact-operator material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean` and
the Hahn–Banach material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HahnBanach.lean`.
Those archived files provide background; this theorem is not a port of
a v1 target. Rudin, *Functional Analysis*, 2nd edition, Chapter 4 is a
general background reference, not a source location for this proof.

The weak-convergence ingredients reuse
`MathlibExt.Analysis.Normed.Module.WeakConvergence`. No completeness
hypothesis on `E` or `F` is needed: its uniform-boundedness result applies
Banach–Steinhaus on the complete strong dual.

## Main declarations

* `tendsto_apply_of_isCompactOperator_of_forall_tendsto` : the main
  theorem, in the textbook all-functionals form of weak convergence.
* `tendsto_apply_of_isCompactOperator_of_tendsto_zero` : the weakly-null
  special case.
* `tendsto_apply_of_isCompactOperator_of_tendsto_weakSpace` :
  the same theorem in Mathlib's `toWeakSpace` form.
-/

@[expose] public section

namespace MathlibExt.Analysis.Normed.Operator.CompleteContinuity

open Set Filter Topology Metric
open MathlibExt.Analysis.Normed.Module

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Complete continuity of compact operators.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, let $E$ and $F$ be normed spaces over $\mathbb{K}$, and let $T : E \to F$ be a
compact continuous linear operator. If a sequence $(u_n)$ in $E$ converges weakly to $x \in E$,
that is, $f(u_n) \to f(x)$ for every continuous linear functional $f : E \to \mathbb{K}$, then
$T u_n \to T x$ in norm.

The proof is the standard subsequence argument: if $T u_n$ did not converge in norm to $T x$,
some subsequence would stay $\varepsilon$-away from $T x$; the sequence $(u_n)$ is norm-bounded
by uniform boundedness, so compactness gives a further subsequence of $(T u_n)$ converging in
norm to some $a$; but $T$ preserves weak convergence, so $a = T x$ by uniqueness of scalar
limits and the fact that the dual separates points, contradicting the
$\varepsilon$-separation. -/
theorem tendsto_apply_of_isCompactOperator_of_forall_tendsto {T : E →L[𝕜] F}
    (hT : IsCompactOperator (T : E → F)) {u : ℕ → E} {x : E}
    (h : ∀ f : StrongDual 𝕜 E, Tendsto (fun n => f (u n)) atTop (𝓝 (f x))) :
    Tendsto (fun n => T (u n)) atTop (𝓝 (T x)) := by
  obtain ⟨C, hC⟩ := WeakConvergence.bddAbove_norm_range_of_forall_tendsto h
  have hweak : ∀ g : StrongDual 𝕜 F,
      Tendsto (fun n => g (T (u n))) atTop (𝓝 (g (T x))) :=
    WeakConvergence.tendsto_apply_of_forall_tendsto T h
  by_contra hnot
  rw [Metric.tendsto_atTop] at hnot
  push Not at hnot
  obtain ⟨ε, hε, hbad⟩ := hnot
  have hfreq : ∃ᶠ n in atTop, ε ≤ dist (T (u n)) (T x) :=
    frequently_atTop.mpr hbad
  obtain ⟨φ, hφ, hφbad⟩ := extraction_of_frequently_atTop hfreq
  have hT' : IsCompactOperator (T.toLinearMap : E → F) := hT
  obtain ⟨K, hK, hKsub⟩ := hT'.image_closedBall_subset_compact C
  have hmem : ∀ n, T (u (φ n)) ∈ K := by
    intro n
    apply hKsub
    refine ⟨u (φ n), ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hC ⟨φ n, rfl⟩
  obtain ⟨a, _haK, ψ, hψ, hlim⟩ := hK.tendsto_subseq hmem
  have ha : a = T x := by
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := 𝕜) (V := F)).mpr
    intro g
    have h1 : Tendsto (fun n => g (T (u (φ (ψ n))))) atTop (𝓝 (g a)) :=
      (g.continuous.tendsto a).comp hlim
    have h2 : Tendsto (fun n => g (T (u (φ (ψ n))))) atTop (𝓝 (g (T x))) :=
      (hweak g).comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop)
    exact tendsto_nhds_unique h1 h2
  subst ha
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim ε hε
  have hle : ε ≤ dist (T (u (φ (ψ N)))) (T x) := hφbad (ψ N)
  have hlt : dist (T (u (φ (ψ N)))) (T x) < ε := by
    simpa using hN N le_rfl
  linarith

/-- **Compact operators send weakly null sequences to norm null sequences.** Let $\mathbb{K}$
be $\mathbb{R}$ or $\mathbb{C}$, let $E$ and $F$ be normed spaces over $\mathbb{K}$, and let
$T : E \to F$ be a compact continuous linear operator. If a sequence $(u_n)$ in $E$ converges
weakly to $0$, that is, $f(u_n) \to 0$ for every continuous linear functional
$f : E \to \mathbb{K}$, then $T u_n \to 0$ in norm. -/
theorem tendsto_apply_of_isCompactOperator_of_tendsto_zero {T : E →L[𝕜] F}
    (hT : IsCompactOperator (T : E → F)) {u : ℕ → E}
    (h : ∀ f : StrongDual 𝕜 E, Tendsto (fun n => f (u n)) atTop (𝓝 0)) :
    Tendsto (fun n => T (u n)) atTop (𝓝 0) := by
  have h0 : ∀ f : StrongDual 𝕜 E, Tendsto (fun n => f (u n)) atTop (𝓝 (f 0)) := by
    simpa using h
  simpa using
    tendsto_apply_of_isCompactOperator_of_forall_tendsto hT h0

/-- **Complete continuity of compact operators, weak-topology form.** Let $\mathbb{K}$ be
$\mathbb{R}$ or $\mathbb{C}$, let $E$ and $F$ be normed spaces over $\mathbb{K}$, and let
$T : E \to F$ be a compact continuous linear operator. If a sequence $(u_n)$ in $E$ converges
to $x \in E$ in the weak topology of $E$, then $T u_n \to T x$ in norm. -/
theorem tendsto_apply_of_isCompactOperator_of_tendsto_weakSpace
    {T : E →L[𝕜] F} (hT : IsCompactOperator (T : E → F)) {u : ℕ → E} {x : E}
    (h : Tendsto (fun n => toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x))) :
    Tendsto (fun n => T (u n)) atTop (𝓝 (T x)) := by
  exact tendsto_apply_of_isCompactOperator_of_forall_tendsto hT
    (WeakConvergence.forall_tendsto_of_tendsto_weakSpace h)

end MathlibExt.Analysis.Normed.Operator.CompleteContinuity
