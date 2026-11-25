/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Analysis.Convex.Combination

/-!
# Mazur's lemma

If a sequence `u : ℕ → E` converges weakly to `x` in a normed space `E`
over `ℝ` or `ℂ`, then some sequence of finite real convex combinations
of the tail terms converges to `x` in norm. In particular `x` lies in
the norm closure of the real convex hull of every tail of the sequence.

The hull form is Mathlib's theorem on closures of convex sets in the weak
topology (`Convex.toWeakSpace_closure`, the "Mazur theorem" on closures);
the point of this file is the sequenced form, which is not in Mathlib:
the limit is approximated in norm by an explicit finite convex combination
`∑ i, w i • u (n i)` with `w i ≥ 0`, `∑ i, w i = 1` and `n i ≥ N`.

Source: companion to the Hahn–Banach / separation material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HahnBanach.lean` and to
the weak convergence of orthonormal sequences (batch 24). It is not one
of the 72 v1 targets, and it is not in the pinned Mathlib or in the
earlier batches of this series: Mathlib has only the closure form
(`Convex.toWeakSpace_closure`), and the MathlibExt Banach–Saks file has
only a Cesàro form for uniformly convex spaces. See also Rudin,
*Functional Analysis*, 2nd edition, Theorem 3.13.
-/

@[expose] public section

namespace MathlibExt.Analysis.Normed.Module.MazurLemma

open Set Filter Topology

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [Module ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- **Mazur's lemma, hull form.** Let $E$ be a normed space over $\mathbb{K}$, where $\mathbb{K}$
is $\mathbb{R}$ or $\mathbb{C}$, regarded also as a real vector space by restricting scalars. If
a sequence $(u_n)_{n \in \mathbb{N}}$ in $E$ converges to $x \in E$ in the weak topology of $E$
(the topology induced by the continuous $\mathbb{K}$-linear functionals on $E$), then for every
$N \in \mathbb{N}$ the point $x$ lies in the norm closure of the real convex hull of the tail
$\{u_n : n \ge N\}$. -/
theorem mem_closure_convexHull_of_tendsto_weakSpace {u : ℕ → E} {x : E}
    (h : Tendsto (fun n => toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x)))
    (N : ℕ) :
    x ∈ closure (convexHull ℝ (u '' Set.Ici N)) := by
  have : LocallyConvexSpace ℝ E := NormedSpace.toLocallyConvexSpace' 𝕜
  have hconv : Convex ℝ (convexHull ℝ (u '' Set.Ici N)) := convex_convexHull ℝ _
  have hweak : toWeakSpace 𝕜 E x ∈
      closure (toWeakSpace 𝕜 E '' convexHull ℝ (u '' Set.Ici N)) := by
    rw [mem_closure_iff]
    intro U hU hxU
    have hev : ∀ᶠ n in atTop, toWeakSpace 𝕜 E (u n) ∈ U :=
      h.eventually (hU.mem_nhds hxU)
    obtain ⟨n, hnU, hnN⟩ := (hev.and (eventually_ge_atTop N)).exists
    exact ⟨toWeakSpace 𝕜 E (u n), hnU, u n,
      subset_convexHull ℝ _ ⟨n, hnN, rfl⟩, rfl⟩
  rw [← hconv.toWeakSpace_closure 𝕜] at hweak
  obtain ⟨y, hy, hyx⟩ := hweak
  have hyeq : y = x := (toWeakSpace 𝕜 E).injective hyx
  rwa [hyeq] at hy

/-- **Mazur's lemma, hull form for the whole sequence.** Let $E$ be a normed space over
$\mathbb{K}$, where $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$, regarded also as a real vector
space by restricting scalars. If a sequence $(u_n)_{n \in \mathbb{N}}$ in $E$ converges to
$x \in E$ in the weak topology of $E$ (the topology induced by the continuous $\mathbb{K}$-linear
functionals on $E$), then $x$ lies in the norm closure of the real convex hull of the set
$\{u_n : n \in \mathbb{N}\}$. -/
theorem mem_closure_convexHull_range_of_tendsto_weakSpace {u : ℕ → E} {x : E}
    (h : Tendsto (fun n => toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x))) :
    x ∈ closure (convexHull ℝ (Set.range u)) := by
  simpa using mem_closure_convexHull_of_tendsto_weakSpace h 0

/-- **Mazur's lemma, explicit finite convex combinations.** Let $E$ be a normed space over
$\mathbb{K}$, where $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$, regarded also as a real vector
space by restricting scalars. If a sequence $(u_n)_{n \in \mathbb{N}}$ in $E$ converges to
$x \in E$ in the weak topology of $E$ (the topology induced by the continuous $\mathbb{K}$-linear
functionals on $E$), then for every $N \in \mathbb{N}$ and every real $\varepsilon > 0$ there are
a finite index set $I$, real weights $w_i \ge 0$ with $\sum_{i \in I} w_i = 1$ and natural
numbers $n_i \ge N$ for $i \in I$ such that
$\left\| \sum_{i \in I} w_i u_{n_i} - x \right\| < \varepsilon$. -/
theorem exists_finite_convex_combination_norm_sub_lt_of_tendsto_weakSpace
    {u : ℕ → E} {x : E}
    (h : Tendsto (fun n => toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x)))
    (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (n : ι → ℕ),
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ (∀ i, N ≤ n i) ∧
        ‖∑ i, w i • u (n i) - x‖ < ε := by
  have hmem := mem_closure_convexHull_of_tendsto_weakSpace (𝕜 := 𝕜) h N
  rw [Metric.mem_closure_iff] at hmem
  obtain ⟨y, hy, hyx⟩ := hmem ε hε
  rw [mem_convexHull_iff_exists_fintype] at hy
  obtain ⟨ι, _, w, z, hw0, hw1, hz, hsum⟩ := hy
  have hchoice : ∀ i, ∃ n, N ≤ n ∧ u n = z i := fun i => by
    simpa using hz i
  choose n hnN hzn using hchoice
  refine ⟨ι, inferInstance, w, n, hw0, hw1, fun i => hnN i, ?_⟩
  have hsum' : ∑ i, w i • u (n i) = y := by
    rw [← hsum]
    exact Finset.sum_congr rfl fun i _ => by rw [hzn i]
  rw [hsum', ← dist_eq_norm, dist_comm]
  exact hyx

/-- **Mazur's lemma in the textbook phrasing.** Let $E$ be a normed space over $\mathbb{K}$,
where $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$, regarded also as a real vector space by
restricting scalars. Let $(u_n)_{n \in \mathbb{N}}$ be a sequence in $E$ and $x \in E$ such that
$f(u_n) \to f(x)$ for every continuous $\mathbb{K}$-linear functional $f \colon E \to \mathbb{K}$.
Then for every $N \in \mathbb{N}$ and every real $\varepsilon > 0$ there are a finite index set
$I$, real weights $w_i \ge 0$ with $\sum_{i \in I} w_i = 1$ and natural numbers $n_i \ge N$ for
$i \in I$ such that $\left\| \sum_{i \in I} w_i u_{n_i} - x \right\| < \varepsilon$. -/
theorem exists_finite_convex_combination_norm_sub_lt_of_forall_tendsto
    {u : ℕ → E} {x : E}
    (h : ∀ f : StrongDual 𝕜 E,
      Tendsto (fun n => f (u n)) atTop (𝓝 (f x)))
    (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (n : ι → ℕ),
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ (∀ i, N ≤ n i) ∧
        ‖∑ i, w i • u (n i) - x‖ < ε := by
  have hinj : Function.Injective (LinearMap.flip (topDualPairing 𝕜 E)) := by
    intro a b hab
    exact SeparatingDual.eq_iff_forall_dual_eq.mpr fun f =>
      congrFun (congrArg DFunLike.coe hab) f
  have hweak : Tendsto (fun n => toWeakSpace 𝕜 E (u n)) atTop
      (𝓝 (toWeakSpace 𝕜 E x)) := by
    refine (WeakBilin.tendsto_iff_forall_eval_tendsto (topDualPairing 𝕜 E).flip hinj).mpr ?_
    exact h
  exact exists_finite_convex_combination_norm_sub_lt_of_tendsto_weakSpace hweak N hε

end MathlibExt.Analysis.Normed.Module.MazurLemma
