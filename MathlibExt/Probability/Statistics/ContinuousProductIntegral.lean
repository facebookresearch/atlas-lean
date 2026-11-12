/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.FunctionalDelta

/-!
# Hadamard differentiability of the continuous-time product integral (Gill–Johansen)

This file proves that the continuous-time product-integral map
`A ↦ (t ↦ ∏_{(0, t]} (1 + dA))` is **Hadamard differentiable**, tangentially to the continuous
functions, with derivative given by the **Duhamel operator**, and derives the continuous-time
**Kaplan–Meier limit law** from a Nelson–Aalen CLT through the functional delta theorem
`MeasureTheory.TendstoInDistribution.functional_delta` (T44).

## The product integral is a hypothesis

Mathlib has no Lebesgue–Stieltjes product integral; its construction for bounded-variation
integrators is a separate, unmerged task (T77). This file does **not** construct it and does not
import that task. Instead, the product-integral map `P` and its Duhamel operator `Ψ` enter as
arguments, and the properties used are bundled in two `Prop`-valued hypothesis predicates:

* `IsDuhamelProductIntegral P Ψ D S C` (on any normed spaces): on the domain `D`
  * the **Duhamel equation** `P B - P A = Ψ A B (B - A)`;
  * the **uniform sup-norm bound** `‖Ψ A B‖ ≤ C` (for the continuous-time product integral on
    integrators of total variation `≤ M` this is the integration-by-parts estimate of
    Gill–Johansen 1990, with `C` depending only on `M`);
  * **continuity** of `B ↦ Ψ A B s` at `B = A` along `D`, for `s` in a class `S` (in the classical
    proof: step functions, whose uniform closure contains `C[0, τ]`).
* `IsStieltjesProductIntegral τ P Ψ D S C` (on `ℓ^∞([0, τ])`, Mathlib's
  `lp (fun _ : Set.Icc (0 : ℝ) τ ↦ ℝ) ∞`): the above, plus `C[0, τ] ⊆ closure S`, plus the
  **definition of the product integral on pure-jump integrators**: if `A t = ∑_{s_j ≤ t} a j`
  with jump times `0 < s 0 < s 1 < ⋯`, then `P A t = ∏_{s_j ≤ t} (1 + a j)`.

For the continuous-time product integral, `Ψ A B h t = ∫_{(0, t]} P(A)(0, s) dh(s) P(B)(s, t]`
(Gill–Johansen 1990); the Duhamel equation is derived there from
multiplicativity `P(s, u] = P(s, t] P(t, u]`. Multiplicativity is not used here and is therefore
not assumed: the Duhamel equation is taken directly.

## Main statements

* `hasHadamardDerivWithinAt_of_duhamel`: the abstract Gill–Johansen argument. A Duhamel
  representation `P B - P θ = Ψ B (B - θ)` on `D` with `‖Ψ B‖ ≤ C` and `Ψ B s → Ψ θ s` as `B → θ`
  in `D` (for `s` in a class whose closure contains `E₀`) gives Hadamard differentiability of `P`
  at `θ`, tangentially to `E₀`, with derivative `Ψ θ`.
* `IsDuhamelProductIntegral.hasHadamardDerivWithinAt`: **the product integral is Hadamard
  differentiable** at every integrator `θ ∈ D`, with the **Duhamel derivative** `Ψ θ θ`.
* `IsStieltjesProductIntegral.hasHadamardDerivWithinAt`: the same in `ℓ^∞([0, τ])`, tangentially
  to `C[0, τ]`; `IsStieltjesProductIntegral.hasHadamardDerivWithinAt_neg` gives the survival map
  `Λ ↦ P(-Λ)` tangentially to `{h | -h ∈ closure S}` (the regulated functions when `S` is the step
  functions), with the `C[0, τ]` version as a corollary.
* `isDuhamelProductIntegral_prodIntegral`: T44's grid product integral satisfies the hypothesis
  predicate on every total-variation ball, with `Ψ = gridDuhamel`, and `gridDuhamel x x` is T44's
  `duhamelDeriv x`; this is a genuine instance of the hypotheses.
* `tendstoInDistribution_kmSurvival_lInfty`: the **continuous-time Kaplan–Meier limit law**
  `√n (Ŝₙ - S) ⇒ -Ψ(-Λ, -Λ) G` in `ℓ^∞([0, τ])`, where `Ŝₙ` is `CensoredData.kmSurvival`,
  `S = P(-Λ)`, and `√n (Λ̂ₙ - Λ) ⇒ G` (Nelson–Aalen CLT, `CensoredData.nelsonAalen`) is a
  hypothesis.

## Measurability caveat (read before using the Kaplan–Meier statement)

Measurability is Borel measurability (Mathlib's `TendstoInDistribution`), **not** the
outer-probability (Hoffmann-Jørgensen) framework of van der Vaart–Wellner. `ℓ^∞([0, τ])` is not
separable, and the `AEMeasurable` fields of the Nelson–Aalen CLT hypothesis `hCLT` of
`tendstoInDistribution_kmSurvival_lInfty` **fail on the canonical space of the observations
whenever the law of the uncensored observation times in `[0, τ]` has a non-atomic part** (T44's
`n = 1` counterexample: the paths `1[u, τ]` are pairwise at sup distance `1`, so every set of them
is closed, and a non-measurable set of jump times gives a non-measurable preimage; see the module
docstring of `MathlibExt.Probability.Statistics.FunctionalDelta`). The same applies to the
measurability hypothesis `hmeas` on the Kaplan–Meier process. So the Kaplan–Meier theorem is a
**conditional** statement: it is correct as stated, but it does **not** give the classical
continuous-time Kaplan–Meier limit for continuous failure-time distributions (when
`P(death ≤ τ, uncensored) > 0`). That limit needs the outer-probability framework, which is not
formalized here (deferred: full Gill–Johansen with outer probability).

The limit `G` is only required to satisfy `-G ∈ closure S` (for `S` = step functions: the
regulated functions, which contain the càdlàg paths of `D[0, τ]`), not continuity. This matters:
for a purely atomic observation-time law the Nelson–Aalen limit jumps at every atom with
`0 < ΔΛ < 1`, so a continuity hypothesis on `G` would exclude every non-degenerate i.i.d. model.
With `closure S`, the theorem can apply to observation-time laws with finitely many atoms in
`[0, τ]`: there `Λ̂ₙ` takes finitely many values (so it is Borel measurable), its total
variation on `[0, τ]` is at most the number of atoms, and its limit is a step process.

**The domain hypothesis `hdom` is restrictive.** It asks for the negated Nelson–Aalen paths to lie
in `D` almost surely for every `n`, not merely with probability tending to one. If `D` is a
total-variation ball (as for the classical Duhamel bound), this fails for large `n` unless the
death times in `[0, τ]` have finite support: when all `n` subjects die at distinct times `≤ τ`,
the numbers at risk are `n, n - 1, …, 1` and `Λ̂ₙ(τ)` is the harmonic number `Hₙ → ∞`. A domain
without a total-variation bound (negated cumulative hazards, i.e. nonincreasing integrators with
jumps in `[-1, 0]`) would avoid this, but then the uniform bound `norm_le` would have to be
established on that domain. Finally, the Hadamard derivative is the one-sided directional notion
of T44's `HasHadamardDerivWithinAt` (implied by the usual one).

## Source receipt (reuse search, 2026-11-12)

Mathlib v4.35.0 has no product integral, no Lebesgue–Stieltjes integral against bounded-variation
functions on `ℓ^∞`, and no Hadamard differentiability. The repo's
`MathlibExt.Probability.Statistics.FunctionalDelta` (T44, merged) supplies
`HasHadamardDerivWithinAt`, `functional_delta`, the grid product integral `prodIntegral`, its
Duhamel equation `prodIntegral_sub_prodIntegral` and derivative `duhamelDeriv`; all are reused.
`CensoredData.kmSurvival` / `CensoredData.nelsonAalen` are reused from
`MathlibExt.Probability.Statistics.Survival.KaplanMeier` / `.NelsonAalen`.

## References

* R. D. Gill and S. Johansen, *A survey of product-integration with a view toward application in
  survival analysis*, Ann. Statist. 18 (1990), 1501–1555.
* A. W. van der Vaart, *Asymptotic Statistics* (1998), Theorem 20.8, §20.3.
* A. W. van der Vaart and J. A. Wellner, *Weak Convergence and Empirical Processes* (1996), §1.1,
  §3.9.4.
-/

@[expose] public section

open Filter Topology MeasureTheory Finset
open scoped ENNReal

namespace MathlibExt.Probability.Statistics.ContinuousProductIntegral

open MathlibExt.Probability.Statistics.FunctionalDelta

section Abstract

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **Duhamel representation implies Hadamard differentiability** (the Gill–Johansen argument,
van der Vaart 1998, §20.3). Suppose that on the domain `D ∋ θ`
* `P B - P θ = Ψ B (B - θ)` (Duhamel equation),
* `‖Ψ B‖ ≤ C` (uniform bound), and
* `Ψ B s → Ψ θ s` as `B → θ` within `D`, for every `s ∈ S`,

and that `E₀ ⊆ closure S`. Then `P` is Hadamard differentiable at `θ`, tangentially to `E₀`, with
derivative `Ψ θ`. The proof writes `t⁻¹ (P (θ + t k) - P θ) = Ψ (θ + t k) k` and splits
`Ψ B k - Ψ θ h` through an approximation `s ∈ S` of `h`. -/
theorem hasHadamardDerivWithinAt_of_duhamel {P : E → F} {Ψ : E → E →L[ℝ] F} {D S E₀ : Set E}
    {θ : E} {C : ℝ} (hθ : θ ∈ D) (hduh : ∀ B ∈ D, P B - P θ = Ψ B (B - θ))
    (hbound : ∀ B ∈ D, ‖Ψ B‖ ≤ C)
    (hcont : ∀ s ∈ S, Tendsto (fun B ↦ Ψ B s) (𝓝[D] θ) (𝓝 (Ψ θ s)))
    (hE₀ : E₀ ⊆ closure S) :
    HasHadamardDerivWithinAt P (Ψ θ) D E₀ θ := by
  intro h hh
  set L := (𝓝[>] (0 : ℝ) ×ˢ 𝓝 h) ⊓ 𝓟 {p : ℝ × E | θ + p.1 • p.2 ∈ D} with hL
  have hmove : Tendsto (fun p : ℝ × E ↦ θ + p.1 • p.2) L (𝓝[D] θ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, mem_inf_of_right (mem_principal_self _)⟩
    have hc : Continuous (fun p : ℝ × E ↦ θ + p.1 • p.2) := by fun_prop
    have h0 : Tendsto (fun p : ℝ × E ↦ θ + p.1 • p.2) (𝓝 ((0 : ℝ), h)) (𝓝 θ) := by
      simpa using hc.tendsto ((0 : ℝ), h)
    refine h0.mono_left (inf_le_left.trans ?_)
    rw [nhds_prod_eq]
    exact prod_mono_left _ nhdsWithin_le_nhds
  have hval : ∀ p : ℝ × E, 0 < p.1 → θ + p.1 • p.2 ∈ D →
      p.1⁻¹ • (P (θ + p.1 • p.2) - P θ) = Ψ (θ + p.1 • p.2) p.2 := by
    intro p hp hD
    rw [hduh _ hD, add_sub_cancel_left, map_smul, smul_smul, inv_mul_cancel₀ hp.ne', one_smul]
  set C' := max C 0 + 1 with hC'
  have hC'pos : 0 < C' := by positivity
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / (4 * C') := by positivity
  have key : ∀ T : E →L[ℝ] F, ‖T‖ ≤ C → ∀ v : E, ‖v‖ < ε / (4 * C') → ‖T v‖ < ε / 4 := by
    intro T hT v hv
    have hTC : ‖T‖ ≤ C' := by linarith [le_max_left C 0]
    calc ‖T v‖ ≤ ‖T‖ * ‖v‖ := T.le_opNorm v
      _ ≤ C' * ‖v‖ := mul_le_mul_of_nonneg_right hTC (norm_nonneg _)
      _ < C' * (ε / (4 * C')) := mul_lt_mul_of_pos_left hv hC'pos
      _ = ε / 4 := by field_simp
  obtain ⟨s, hsS, hs⟩ := Metric.mem_closure_iff.1 (hE₀ hh) _ hδ
  have hcs := Metric.tendsto_nhds.1 ((hcont s hsS).comp hmove) (ε / 4) (by positivity)
  have hpos : ∀ᶠ p in L, 0 < p.1 :=
    ((eventually_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0)).prod_inl _).filter_mono
      inf_le_left
  have hball : ∀ᶠ y in 𝓝 h, dist y h < ε / (4 * C') := Metric.ball_mem_nhds h hδ
  have hnear : ∀ᶠ p in L, dist p.2 h < ε / (4 * C') :=
    (hball.prod_inr _).filter_mono inf_le_left
  have hmem : ∀ᶠ p in L, θ + p.1 • p.2 ∈ D := mem_inf_of_right (mem_principal_self _)
  filter_upwards [hpos, hnear, hcs, hmem] with p hp hk hps hpD
  rw [hval p hp hpD, dist_eq_norm]
  set B := θ + p.1 • p.2
  have e : Ψ B p.2 - Ψ θ h = Ψ B (p.2 - h) + Ψ B (h - s) + (Ψ B s - Ψ θ s) + Ψ θ (s - h) := by
    simp only [map_sub]
    abel
  have h1 : ‖Ψ B (p.2 - h)‖ < ε / 4 := key _ (hbound B hpD) _ (by rwa [← dist_eq_norm])
  have h2 : ‖Ψ B (h - s)‖ < ε / 4 := key _ (hbound B hpD) _ (by rwa [← dist_eq_norm])
  have h3 : ‖Ψ B s - Ψ θ s‖ < ε / 4 := by rw [← dist_eq_norm]; exact hps
  have h4 : ‖Ψ θ (s - h)‖ < ε / 4 :=
    key _ (hbound θ hθ) _ (by rwa [← dist_eq_norm, dist_comm])
  rw [e]
  calc ‖Ψ B (p.2 - h) + Ψ B (h - s) + (Ψ B s - Ψ θ s) + Ψ θ (s - h)‖
      ≤ ‖Ψ B (p.2 - h) + Ψ B (h - s) + (Ψ B s - Ψ θ s)‖ + ‖Ψ θ (s - h)‖ := norm_add_le _ _
    _ ≤ ‖Ψ B (p.2 - h) + Ψ B (h - s)‖ + ‖Ψ B s - Ψ θ s‖ + ‖Ψ θ (s - h)‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ ‖Ψ B (p.2 - h)‖ + ‖Ψ B (h - s)‖ + ‖Ψ B s - Ψ θ s‖ + ‖Ψ θ (s - h)‖ := by
        gcongr; exact norm_add_le _ _
    _ < ε := by linarith

/-- **Duhamel hypotheses for a product-integral map** `P : E → F` with Duhamel operator
`Ψ : E → E → (E →L[ℝ] F)` on the domain `D`, with uniform bound `C` and continuity class `S`.

This is the minimal restatement, as a hypothesis, of the properties of the Lebesgue–Stieltjes
product integral `P A t = ∏_{(0, t]} (1 + dA)` (constructed in the separate task T77, not imported
here) that the Hadamard-differentiability argument uses. For that product integral on integrators
of total variation `≤ M`, `Ψ A B h t = ∫_{(0, t]} P(A)(0, s) dh(s) P(B)(s, t]` and:
* `duhamel` is the **Duhamel equation** (Gill–Johansen 1990);
* `norm_le` is the **sup-norm bound** obtained from integration by parts, with `C` depending only
  on `M` (Gill–Johansen 1990);
* `tendsto` is the continuity of the Duhamel integral in the second integrator, proved classically
  for step functions `s` (whose uniform closure contains the continuous functions). -/
structure IsDuhamelProductIntegral (P : E → F) (Ψ : E → E → E →L[ℝ] F) (D S : Set E) (C : ℝ) :
    Prop where
  /-- **Duhamel equation**: `P B - P A = Ψ A B (B - A)` for integrators `A, B ∈ D`. -/
  duhamel : ∀ A ∈ D, ∀ B ∈ D, P B - P A = Ψ A B (B - A)
  /-- The Duhamel operators are uniformly bounded in operator norm on `D`. -/
  norm_le : ∀ A ∈ D, ∀ B ∈ D, ‖Ψ A B‖ ≤ C
  /-- Continuity of the Duhamel operator in the second integrator at `B = A`, along `D`, on the
  class `S`. -/
  tendsto : ∀ A ∈ D, ∀ s ∈ S, Tendsto (fun B ↦ Ψ A B s) (𝓝[D] A) (𝓝 (Ψ A A s))

namespace IsDuhamelProductIntegral

variable {P : E → F} {Ψ : E → E → E →L[ℝ] F} {D S : Set E} {C : ℝ}

/-- A product integral with Duhamel hypotheses is Lipschitz on `D`:
`‖P B - P A‖ ≤ C ‖B - A‖` (sup-norm continuity on total-variation balls). -/
theorem norm_sub_le (hP : IsDuhamelProductIntegral P Ψ D S C) {A B : E} (hA : A ∈ D)
    (hB : B ∈ D) : ‖P B - P A‖ ≤ C * ‖B - A‖ := by
  rw [hP.duhamel A hA B hB]
  exact (Ψ A B).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right (hP.norm_le A hA B hB)
    (norm_nonneg _))

/-- **Hadamard differentiability of the product integral** (Gill–Johansen 1990;
van der Vaart 1998, §20.3): at every integrator `θ ∈ D`, `P` is Hadamard differentiable,
tangentially to any `E₀ ⊆ closure S`, with the **Duhamel derivative** `Ψ θ θ`, i.e.
`h ↦ (t ↦ ∫_{(0, t]} P(θ)(0, s) dh(s) P(θ)(s, t])` for the Lebesgue–Stieltjes product integral. -/
theorem hasHadamardDerivWithinAt (hP : IsDuhamelProductIntegral P Ψ D S C) {θ : E} (hθ : θ ∈ D)
    {E₀ : Set E} (hE₀ : E₀ ⊆ closure S) :
    HasHadamardDerivWithinAt P (Ψ θ θ) D E₀ θ :=
  hasHadamardDerivWithinAt_of_duhamel hθ (hP.duhamel θ hθ) (hP.norm_le θ hθ) (hP.tendsto θ hθ)
    hE₀

end IsDuhamelProductIntegral

end Abstract

section Grid

variable {k : ℕ}

/-- The **two-point discrete Duhamel operator** on a fixed grid of `k` times:
`gridDuhamel x y h j = ∑_{i ≤ j} (∏_{l < i} (1 + x l)) · h i · ∏_{i < l ≤ j} (1 + y l)`, the grid
analogue of `h ↦ ∫_{(0, t]} P(x)(0, s) dh(s) P(y)(s, t]`. On the diagonal it is T44's
`duhamelDeriv` (`gridDuhamel_self`), and it satisfies the exact Duhamel equation for
`prodIntegral` (`prodIntegral_sub_prodIntegral_eq_gridDuhamel`). -/
noncomputable def gridDuhamel (x y : Fin k → ℝ) : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi fun j ↦ ∑ i ∈ Iic j,
    ((∏ l ∈ Iio i, (1 + x l)) * ∏ l ∈ Ioc i j, (1 + y l)) • ContinuousLinearMap.proj i

/-- Coordinates of `gridDuhamel`. -/
theorem gridDuhamel_apply (x y h : Fin k → ℝ) (j : Fin k) :
    gridDuhamel x y h j =
      ∑ i ∈ Iic j, (∏ l ∈ Iio i, (1 + x l)) * h i * ∏ l ∈ Ioc i j, (1 + y l) := by
  simp only [gridDuhamel, ContinuousLinearMap.pi_apply, FunLike.coe_sum,
    Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul]
  exact sum_congr rfl fun i _ ↦ by ring

/-- On the diagonal, the two-point Duhamel operator is T44's Duhamel derivative. -/
theorem gridDuhamel_self (x : Fin k → ℝ) : gridDuhamel x x = duhamelDeriv x := rfl

/-- The **Duhamel equation** for the grid product integral, in operator form. -/
theorem prodIntegral_sub_prodIntegral_eq_gridDuhamel (x y : Fin k → ℝ) :
    prodIntegral y - prodIntegral x = gridDuhamel x y (y - x) := by
  funext j
  rw [Pi.sub_apply, prodIntegral_sub_prodIntegral, gridDuhamel_apply]
  rfl

private theorem abs_prod_one_add_le' (x : Fin k → ℝ) (t : Finset (Fin k)) :
    |∏ l ∈ t, (1 + x l)| ≤ Real.exp (∑ l, |x l|) := by
  rw [abs_prod]
  calc ∏ l ∈ t, |1 + x l| ≤ ∏ l ∈ t, Real.exp |x l| :=
        prod_le_prod₀ (fun _ _ ↦ abs_nonneg _) fun l _ ↦ (abs_add_le _ _).trans <| by
          rw [abs_one, add_comm]; exact Real.add_one_le_exp _
    _ = Real.exp (∑ l ∈ t, |x l|) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑ l, |x l|) := Real.exp_le_exp.2 <|
        sum_le_sum_of_subset_of_nonneg (subset_univ t) fun _ _ _ ↦ abs_nonneg _

/-- Operator-norm bound for the grid Duhamel operator on a total-variation ball:
`‖gridDuhamel x y‖ ≤ k · e^M · e^M` when `∑ |x l| ≤ M` and `∑ |y l| ≤ M`. (Unlike the
continuous-time integration-by-parts bound, this one grows with `k`; on a fixed grid that is
harmless.) -/
theorem norm_gridDuhamel_le {M : ℝ} {x y : Fin k → ℝ} (hx : ∑ l, |x l| ≤ M)
    (hy : ∑ l, |y l| ≤ M) : ‖gridDuhamel x y‖ ≤ k * (Real.exp M * Real.exp M) := by
  have hC : 0 ≤ (k : ℝ) * (Real.exp M * Real.exp M) := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun h ↦ ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j ↦ ?_
  rw [gridDuhamel_apply, Real.norm_eq_abs]
  have hterm : ∀ i ∈ Iic j, |(∏ l ∈ Iio i, (1 + x l)) * h i * ∏ l ∈ Ioc i j, (1 + y l)| ≤
      Real.exp M * Real.exp M * ‖h‖ := by
    intro i _
    rw [abs_mul, abs_mul]
    have h1 := (abs_prod_one_add_le' x (Iio i)).trans (Real.exp_le_exp.2 hx)
    have h2 := (abs_prod_one_add_le' y (Ioc i j)).trans (Real.exp_le_exp.2 hy)
    have h3 : |h i| ≤ ‖h‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm h i
    calc |∏ l ∈ Iio i, (1 + x l)| * |h i| * |∏ l ∈ Ioc i j, (1 + y l)|
        ≤ Real.exp M * ‖h‖ * Real.exp M := by gcongr
      _ = _ := by ring
  calc |∑ i ∈ Iic j, (∏ l ∈ Iio i, (1 + x l)) * h i * ∏ l ∈ Ioc i j, (1 + y l)|
      ≤ ∑ i ∈ Iic j, |(∏ l ∈ Iio i, (1 + x l)) * h i * ∏ l ∈ Ioc i j, (1 + y l)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Iic j, Real.exp M * Real.exp M * ‖h‖ := sum_le_sum hterm
    _ = (Iic j).card * (Real.exp M * Real.exp M * ‖h‖) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ k * (Real.exp M * Real.exp M * ‖h‖) := by
        gcongr
        exact_mod_cast (card_le_univ (Iic j)).trans_eq (Fintype.card_fin k)
    _ = k * (Real.exp M * Real.exp M) * ‖h‖ := by ring

/-- `y ↦ gridDuhamel x y h` is continuous. -/
theorem continuous_gridDuhamel_right (x h : Fin k → ℝ) :
    Continuous fun y ↦ gridDuhamel x y h := by
  have : (fun y ↦ gridDuhamel x y h) =
      fun y j ↦ ∑ i ∈ Iic j, (∏ l ∈ Iio i, (1 + x l)) * h i * ∏ l ∈ Ioc i j, (1 + y l) := by
    funext y j
    exact gridDuhamel_apply x y h j
  rw [this]
  fun_prop

/-- **T44's grid product integral satisfies the Duhamel hypotheses** on every total-variation
ball `{x | ∑ |x l| ≤ M}`, with Duhamel operator `gridDuhamel`, bound `k e^{2M}` and continuity
class `Set.univ`. This is a genuine instance of `IsDuhamelProductIntegral`; with
`IsDuhamelProductIntegral.hasHadamardDerivWithinAt` it recovers the Duhamel derivative
`duhamelDeriv` of T44 (via `gridDuhamel_self`). -/
theorem isDuhamelProductIntegral_prodIntegral (M : ℝ) :
    IsDuhamelProductIntegral (prodIntegral (k := k)) gridDuhamel {x | ∑ l, |x l| ≤ M} Set.univ
      (k * (Real.exp M * Real.exp M)) where
  duhamel _ _ _ _ := prodIntegral_sub_prodIntegral_eq_gridDuhamel _ _
  norm_le _ hA _ hB := norm_gridDuhamel_le hA hB
  tendsto A _ s _ := (continuous_gridDuhamel_right A s).continuousAt.continuousWithinAt.tendsto

end Grid

section LInfty

/-- `ℓ^∞([0, τ])`: bounded real functions on `[0, τ]` with the sup norm. -/
local notation "𝔻[" τ "]" => lp (fun _ : Set.Icc (0 : ℝ) τ ↦ ℝ) ∞

/-- **The continuous-time (Lebesgue–Stieltjes) product integral on `ℓ^∞([0, τ])`, restated as a
hypothesis.** `P A t` stands for `∏_{(0, t]} (1 + dA)` and `Ψ A B` for the Duhamel operator
`h ↦ (t ↦ ∫_{(0, t]} P(A)(0, s) dh(s) P(B)(s, t])` on the domain `D` (a total-variation ball, where
the construction of the separate task T77 applies). Besides the Duhamel hypotheses of
`IsDuhamelProductIntegral`:
* `continuous_subset_closure`: the continuity class `S` of the Duhamel operator is uniformly dense
  in `C[0, τ]` (classically, `S` = step functions);
* `pureJump`: the **definition of the product integral on pure-jump integrators**: if
  `A t = ∑_{s_j ≤ t} a j` on `[0, τ]` with jump times `0 < s 0 < s 1 < ⋯`, then
  `P A t = ∏_{s_j ≤ t} (1 + a j)`.

`Ψ A B` is a continuous linear operator on all of `ℓ^∞([0, τ])`: the Stieltjes integral defines it
on bounded-variation `h`, the integration-by-parts bound extends it to their uniform closure (the
regulated functions), and any norm-preserving extension beyond that (one exists because
`ℓ^∞([0, τ])` is an injective Banach space) satisfies these fields; the theorems only evaluate
`Ψ A B` on `B - A`, on `S`, and on limits of elements of `S`.

Nothing here constructs `P`; theorems taking `IsStieltjesProductIntegral τ P Ψ D S C` are
conditional on the product integral of T77 satisfying it. -/
structure IsStieltjesProductIntegral (τ : ℝ) (P : 𝔻[τ] → 𝔻[τ])
    (Ψ : 𝔻[τ] → 𝔻[τ] → 𝔻[τ] →L[ℝ] 𝔻[τ]) (D S : Set 𝔻[τ]) (C : ℝ) : Prop
    extends IsDuhamelProductIntegral P Ψ D S C where
  /-- The continuity class is dense in `C[0, τ]` for the sup norm. -/
  continuous_subset_closure : {h : 𝔻[τ] | Continuous fun t ↦ h t} ⊆ closure S
  /-- The product integral of a pure-jump integrator with finitely many jumps in `(0, ∞)` is the
  finite product of `1 + jump`. -/
  pureJump : ∀ {k : ℕ} (s a : Fin k → ℝ), StrictMono s → (∀ j, 0 < s j) → ∀ A : 𝔻[τ],
    (∀ t, A t = ∑ j with s j ≤ (t : ℝ), a j) → ∀ t, P A t = ∏ j with s j ≤ (t : ℝ), (1 + a j)

namespace IsStieltjesProductIntegral

variable {τ : ℝ} {P : 𝔻[τ] → 𝔻[τ]} {Ψ : 𝔻[τ] → 𝔻[τ] → 𝔻[τ] →L[ℝ] 𝔻[τ]} {D S : Set 𝔻[τ]}
  {C : ℝ}

/-- **Hadamard differentiability of the continuous-time product integral** (Gill–Johansen 1990,
van der Vaart 1998, §20.3), tangentially to `C[0, τ]` in the uniform topology of
`ℓ^∞([0, τ])`, at every integrator `θ ∈ D`, with the Duhamel derivative
`Ψ θ θ h = (t ↦ ∫_{(0, t]} P(θ)(0, s) dh(s) P(θ)(s, t])`. -/
theorem hasHadamardDerivWithinAt (hP : IsStieltjesProductIntegral τ P Ψ D S C) {θ : 𝔻[τ]}
    (hθ : θ ∈ D) :
    HasHadamardDerivWithinAt P (Ψ θ θ) D {h | Continuous fun t ↦ h t} θ :=
  hP.toIsDuhamelProductIntegral.hasHadamardDerivWithinAt hθ hP.continuous_subset_closure

/-- **Hadamard differentiability of the survival map** `Λ ↦ P(-Λ) = ∏_{(0, t]} (1 - dΛ)` at a
cumulative hazard `Λ` with `-Λ ∈ D`, on the domain `{A | -A ∈ D}`, with derivative
`h ↦ -Ψ(-Λ, -Λ) h`, tangentially to `{h | -h ∈ closure S}`. For `S` = step functions this is the
set of regulated functions, which contains the càdlàg paths of `D[0, τ]` (van der Vaart's tangent
set) and not only `C[0, τ]` (`hasHadamardDerivWithinAt_neg_continuous`). -/
theorem hasHadamardDerivWithinAt_neg (hP : IsStieltjesProductIntegral τ P Ψ D S C) {Λ : 𝔻[τ]}
    (hΛ : -Λ ∈ D) :
    HasHadamardDerivWithinAt (fun A ↦ P (-A)) (fun h ↦ -Ψ (-Λ) (-Λ) h) {A | -A ∈ D}
      {h | -h ∈ closure S} Λ := by
  set Ψ' : 𝔻[τ] → 𝔻[τ] →L[ℝ] 𝔻[τ] := fun B ↦ (Ψ (-Λ) (-B)).comp (-ContinuousLinearMap.id ℝ _)
    with hΨ'
  have hneg : Tendsto (fun B : 𝔻[τ] ↦ -B) (𝓝[{A | -A ∈ D}] Λ) (𝓝[D] (-Λ)) :=
    tendsto_nhdsWithin_iff.2 ⟨(continuous_neg.tendsto Λ).mono_left nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin⟩
  have key := hasHadamardDerivWithinAt_of_duhamel (P := fun A ↦ P (-A)) (Ψ := Ψ')
    (D := {A | -A ∈ D}) (S := -S) (θ := Λ) (C := C) hΛ
    (fun B hB ↦ by
      simp only [Ψ', ContinuousLinearMap.comp_apply, neg_apply,
        ContinuousLinearMap.id_apply]
      rw [hP.duhamel _ hΛ _ hB, neg_sub_neg, neg_sub])
    (fun B hB ↦ (ContinuousLinearMap.opNorm_comp_le _ _).trans <|
      (mul_le_of_le_one_right (norm_nonneg _) (by
        rw [norm_neg]; exact ContinuousLinearMap.norm_id_le)).trans (hP.norm_le _ hΛ _ hB))
    (fun s hs ↦ by
      simpa [Ψ', Function.comp_def] using (hP.tendsto _ hΛ (-s) hs).comp hneg)
    (E₀ := {h | -h ∈ closure S}) (fun h hh ↦ by
      rw [← neg_closure, Set.mem_neg]
      exact hh)
  convert key using 1
  funext h
  simp [Ψ']

/-- The survival map `Λ ↦ P(-Λ)` is Hadamard differentiable tangentially to `C[0, τ]`
(corollary of `hasHadamardDerivWithinAt_neg` through `continuous_subset_closure`). -/
theorem hasHadamardDerivWithinAt_neg_continuous (hP : IsStieltjesProductIntegral τ P Ψ D S C)
    {Λ : 𝔻[τ]} (hΛ : -Λ ∈ D) :
    HasHadamardDerivWithinAt (fun A ↦ P (-A)) (fun h ↦ -Ψ (-Λ) (-Λ) h) {A | -A ∈ D}
      {h | Continuous fun t ↦ h t} Λ := by
  intro h hh
  refine hP.hasHadamardDerivWithinAt_neg hΛ h (hP.continuous_subset_closure ?_)
  change Continuous fun t ↦ (-h) t
  simp only [lp.coeFn_neg, Pi.neg_apply]
  exact Continuous.neg hh

end IsStieltjesProductIntegral

open KaplanMeier in
/-- **Continuous-time Kaplan–Meier limit law in `ℓ^∞([0, τ])`, conditional on Borel
measurability** (van der Vaart 1998, §20.3; Gill–Johansen 1990).

Setting: `Dn n ω` is the grouped censored data set of the `n`-th sample (any number `kn n ω` of
distinct observation times, all positive). `Λhat n ω` and `KMhat n ω` are its Nelson–Aalen and
Kaplan–Meier estimates as elements of `ℓ^∞([0, τ])` (`hΛhat`, `hKMhat` tie them to
`CensoredData.nelsonAalen` and `CensoredData.kmSurvival`). `P` is the product integral, given by the
hypothesis `hP` (T77's construction is not imported), and `S = P(-Λ) = ∏_{(0, t]} (1 - dΛ)` is the
survival function of the cumulative hazard `Λ`.

If `√n (Λ̂ₙ - Λ) ⇒ G` in `ℓ^∞([0, τ])` with `-G ∈ closure S` almost surely (`hCLT`, `hG`; the
Nelson–Aalen functional CLT is a hypothesis; for `S` = step functions, `closure S` is the regulated
functions, so `G` may jump, as it does at atoms of the observation-time law) and the negated
Nelson–Aalen paths stay in the domain `D` (`hdom`), then `√n (Ŝₙ - S) ⇒ -Ψ(-Λ, -Λ) G`, i.e.
coordinatewise `-∫_{(0, t]} P(-Λ)(0, s) dG(s) P(-Λ)(s, t]` (through integration by parts, since
`G` need not be of bounded variation). The proof identifies
`Ŝₙ = P(-Λ̂ₙ)` through `IsStieltjesProductIntegral.pureJump` and applies T44's
`MeasureTheory.TendstoInDistribution.functional_delta` with the Hadamard derivative of
`IsStieltjesProductIntegral.hasHadamardDerivWithinAt_neg`.

**Caveat (outer probability / `ℓ^∞` measurability).** This is Borel weak convergence. The
`AEMeasurable` fields of `hCLT` (and `hmeas`) **fail on the canonical space of the observations
whenever the law of the uncensored observation times in `[0, τ]` has a non-atomic part** (T44's
`n = 1` counterexample, see the module docstrings here and of
`MathlibExt.Probability.Statistics.FunctionalDelta`). In that case, which includes every continuous
failure-time distribution with `P(death ≤ τ, uncensored) > 0`, the hypotheses cannot hold and this
theorem says nothing; the classical continuous-time Kaplan–Meier limit there needs the
outer-probability (Hoffmann-Jørgensen) framework, which is not formalized. The theorem can apply
when the observation-time law has finitely many atoms in `[0, τ]` (see the module docstring).

**Caveat (domain).** `hdom` asks for `-Λ̂ₙ ∈ D` almost surely for every `n`. For `D` a
total-variation ball this fails for large `n` unless the death times in `[0, τ]` have finite
support (with `n` distinct deaths `≤ τ`, `Λ̂ₙ(τ) = Hₙ → ∞`); see the module docstring. -/
theorem tendstoInDistribution_kmSurvival_lInfty {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω}
    {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω} {μ' : Measure Ω'} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] {τ : ℝ} [MeasurableSpace 𝔻[τ]] [BorelSpace 𝔻[τ]]
    {P : 𝔻[τ] → 𝔻[τ]} {Ψ : 𝔻[τ] → 𝔻[τ] → 𝔻[τ] →L[ℝ] 𝔻[τ]} {D S : Set 𝔻[τ]} {C : ℝ}
    (hP : IsStieltjesProductIntegral τ P Ψ D S C)
    {kn : ℕ → Ω → ℕ} {Dn : ∀ n ω, CensoredData (kn n ω)}
    (htime : ∀ n ω j, 0 < (Dn n ω).time j)
    {Λhat KMhat : ℕ → Ω → 𝔻[τ]}
    (hΛhat : ∀ n ω t, Λhat n ω t = (Dn n ω).nelsonAalen t)
    (hKMhat : ∀ n ω t, KMhat n ω t = (Dn n ω).kmSurvival t)
    {Λ : 𝔻[τ]} {G : Ω' → 𝔻[τ]} (hΛ : -Λ ∈ D)
    (hCLT : TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) • (Λhat n ω - Λ)) atTop G
      (fun _ ↦ μ) μ')
    (hG : ∀ᵐ ω ∂μ', -G ω ∈ closure S)
    (hdom : ∀ n, ∀ᵐ ω ∂μ, -Λhat n ω ∈ D)
    (hmeas : ∀ n : ℕ, AEMeasurable (fun ω ↦ √(n : ℝ) • (KMhat n ω - P (-Λ))) μ) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) • (KMhat n ω - P (-Λ))) atTop
      (fun ω ↦ -Ψ (-Λ) (-Λ) (G ω)) (fun _ ↦ μ) μ' := by
  have hKM : ∀ n ω, P (-Λhat n ω) = KMhat n ω := by
    intro n ω
    have hA : ∀ t, (-Λhat n ω) t = ∑ j with (Dn n ω).time j ≤ (t : ℝ),
        -(((Dn n ω).deaths j : ℝ) / (Dn n ω).atRisk j) := by
      intro t
      rw [lp.coeFn_neg, Pi.neg_apply, hΛhat, CensoredData.nelsonAalen, ← sum_neg_distrib]
    refine lp.ext (funext fun t ↦ ?_)
    rw [hP.pureJump _ _ (Dn n ω).strictMono_time (htime n ω) _ hA t, hKMhat]
    simp only [CensoredData.kmSurvival, CensoredData.kmFactor, sub_eq_add_neg]
  have hr : Tendsto (fun n : ℕ ↦ √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hφ'c : Continuous fun h ↦ -Ψ (-Λ) (-Λ) h := (Ψ (-Λ) (-Λ)).continuous.neg
  have key := hCLT.functional_delta hr (hP.hasHadamardDerivWithinAt_neg hΛ) hdom hG
    (fun n ↦ (hmeas n).congr (ae_of_all _ fun ω ↦ by simp only [hKM]))
    (hφ'c.measurable.comp_aemeasurable hCLT.aemeasurable_limit)
  refine key.congr (fun n ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun ω ↦ rfl)
  simp only [hKM]

end LInfty

end MathlibExt.Probability.Statistics.ContinuousProductIntegral
