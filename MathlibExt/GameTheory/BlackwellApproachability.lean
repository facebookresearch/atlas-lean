/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.MetricSpace.HausdorffDistance

@[expose] public section

/-! # Blackwell's approachability theorem: the expected-payoff form

In a repeated game with vector payoffs `v a b ∈ E` (`a` the decision maker's action, `b` the
opponent's), a closed convex set `C ⊆ E` is *approachable* when the decision maker can force the
average payoff to converge to `C` (Blackwell 1956). Blackwell's sufficient condition, which is
also necessary for convex `C`, is that every closed half-space containing `C` be *enforceable*:
for every half-space `{x | ⟪λ, x⟫ ≤ ρ} ⊇ C` some mixed action `q` guarantees
`⟪λ, v(q, b)⟫ ≤ ρ` against every `b` (Hart 2005, Appendix, Theorem 5; equivalently condition
(3.2) of Hart and Mas-Colell 2000). The *Blackwell strategy* plays, when the current average
`x̄` lies outside `C`, a mixed action enforcing the half-space through the nearest point `c` of
`C` orthogonal to `x̄ − c`.

This file proves the deterministic core of the theorem, in any real inner product space: the
recursion `t² δ_t ≤ (t − 1)² δ_{t−1} + M²` for the squared distance `δ_t` of the average to `C`
(Hart 2005, Appendix, equation (13); Blackwell 1956, inequalities (2)–(5)), which gives the rate
`dist(x̄_t, C) ≤ M / √t`, and its application to the averages of the *expected* vector payoffs of
the Blackwell strategy against any sequence of opponent actions. Passing from expected to
realised payoffs needs a strong law of large numbers for martingale differences; that
almost-sure statement is recorded as wanted in `BlackwellApproachabilityWanted`.

## Main results

* `sq_mul_infDist_average_le`, `infDist_average_le`: the deterministic approachability
  recursion and the `M / √t` rate.
* `exists_inner_sub_nonpos_of_enforceable`: Blackwell's half-space step.
* `blackwell_expected_approachability`: the Blackwell strategy drives the average expected
  payoff to `C` at rate `(3R + ‖c₀‖) / √t`, against every opponent sequence.

## References

* D. Blackwell, "An analog of the minimax theorem for vector payoffs", Pacific J. Math. 6
  (1956), 1–8: Theorem 1 and its proof, inequalities (1)–(5).
* S. Hart, "Adaptive heuristics", Econometrica 73(5) (2005), 1401–1430: Appendix, Theorem 5 and
  its proof, equation (13).
* S. Hart and A. Mas-Colell, "A simple adaptive procedure leading to correlated equilibrium",
  Econometrica 68(5) (2000), 1127–1150: §3, Blackwell's Approachability Theorem, (3.2).
-/

namespace MathlibExt.GameTheory.BlackwellApproachability

open Finset Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => @inner ℝ E _ x y

/-- The average `(1/n) ∑_{k < n} y k` of the first `n` vectors of a sequence (`0` for `n = 0`). -/
noncomputable def average (y : ℕ → E) (n : ℕ) : E :=
  (n : ℝ)⁻¹ • ∑ k ∈ range n, y k

/-- `n x̄_n = ∑_{k < n} y_k`, also for `n = 0`. -/
theorem natCast_smul_average (y : ℕ → E) (n : ℕ) :
    (n : ℝ) • average y n = ∑ k ∈ range n, y k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [average, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_smul]

/-- The averages satisfy `(n + 1) x̄_{n+1} = n x̄_n + y_n`. -/
theorem succ_smul_average (y : ℕ → E) (n : ℕ) :
    ((n : ℝ) + 1) • average y (n + 1) = (n : ℝ) • average y n + y n := by
  have := natCast_smul_average y (n + 1)
  push_cast at this
  rw [this, natCast_smul_average, sum_range_succ]

/-- **Blackwell's approachability recursion** (Hart 2005, Appendix, equation (13), here without
expectations; Blackwell 1956, (2)–(5)). Let `x̄_n` be the averages of `y`, let `c n ∈ C` be a
nearest point of `C` to `x̄_n` for `n ≥ 1`, suppose each new vector `y n` lies in the half-space
through `c n` with outer normal `x̄_n − c n` (`⟪x̄_n − c_n, y_n − c_n⟫ ≤ 0` for `n ≥ 1`), and
`‖y n − c n‖ ≤ M`. Then `(n · dist(x̄_n, C))² ≤ n M²` for every `n`. -/
theorem sq_mul_infDist_average_le {C : Set E} {y c : ℕ → E} {M : ℝ} (hc : ∀ n, c n ∈ C)
    (hnear : ∀ n, 0 < n → ‖average y n - c n‖ = infDist (average y n) C)
    (hhalf : ∀ n, 0 < n → ⟪average y n - c n, y n - c n⟫ ≤ 0)
    (hM : ∀ n, ‖y n - c n‖ ≤ M) (n : ℕ) :
    ((n : ℝ) * infDist (average y n) C) ^ 2 ≤ n * M ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    set u : E := (n : ℝ) • (average y n - c n)
    set w : E := y n - c n
    have hkey : ((n : ℝ) + 1) • (average y (n + 1) - c n) = u + w := by
      rw [smul_sub, succ_smul_average]
      simp only [u, w, smul_sub]
      rw [add_smul, one_smul]
      abel
    have hdist : ((n : ℝ) + 1) * infDist (average y (n + 1)) C ≤ ‖u + w‖ := by
      rw [← hkey, norm_smul, Real.norm_of_nonneg (by positivity)]
      gcongr
      rw [← dist_eq_norm]
      exact infDist_le_dist_of_mem (hc n)
    have hu : ‖u‖ ^ 2 ≤ n * M ^ 2 := by
      rcases Nat.eq_zero_or_pos n with h0 | hn
      · subst h0; simp [u]
      · rw [norm_smul, Real.norm_of_nonneg (by positivity), hnear n hn]
        exact ih
    have hinner : ⟪u, w⟫ ≤ 0 := by
      rcases Nat.eq_zero_or_pos n with h0 | hn
      · subst h0; simp [u]
      · simp only [u, w, real_inner_smul_left]
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (hhalf n hn)
    have hw : ‖w‖ ^ 2 ≤ M ^ 2 := by
      have := hM n
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
    have hsq := norm_add_sq_real u w
    have hnn : 0 ≤ ((n : ℝ) + 1) * infDist (average y (n + 1)) C := by
      have := infDist_nonneg (x := average y (n + 1)) (s := C)
      positivity
    push_cast
    nlinarith [pow_le_pow_left₀ hnn hdist 2]

/-- **The `M / √t` rate of approachability**: under the hypotheses of
`sq_mul_infDist_average_le`, `dist(x̄_n, C) ≤ M / √n` for every `n ≥ 1` (Hart 2005, Appendix:
`E[dist(x̄_t, C)] ≤ M / √t`). -/
theorem infDist_average_le {C : Set E} {y c : ℕ → E} {M : ℝ} (hc : ∀ n, c n ∈ C)
    (hnear : ∀ n, 0 < n → ‖average y n - c n‖ = infDist (average y n) C)
    (hhalf : ∀ n, 0 < n → ⟪average y n - c n, y n - c n⟫ ≤ 0)
    (hM : ∀ n, ‖y n - c n‖ ≤ M) {n : ℕ} (hn : 0 < n) :
    infDist (average y n) C ≤ M / Real.sqrt n := by
  have h := sq_mul_infDist_average_le hc hnear hhalf hM n
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn'
  rw [le_div_iff₀ hs]
  have hd := infDist_nonneg (x := average y n) (s := C)
  have hsq : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt hn'.le
  -- `(d √n)² = d² n ≤ M²`
  have h2 : (infDist (average y n) C * Real.sqrt n) ^ 2 ≤ M ^ 2 := by
    rw [mul_pow, hsq]
    have : (n : ℝ) * (infDist (average y n) C ^ 2 * n) ≤ n * M ^ 2 := by nlinarith
    exact le_of_mul_le_mul_left this hn'
  exact (pow_le_pow_iff_left₀ (by positivity) hM0 two_ne_zero).1 h2

/-- **Blackwell's half-space step** (Hart 2005, proof of Theorem 5 (ii); Blackwell 1956,
Theorem 1). Let `C` be convex and suppose every half-space containing `C` is enforceable. If `c`
is a nearest point of `C` to `x`, some mixed action `q` keeps the expected vector payoff
`v(q, b) = ∑ₐ q(a) v(a, b)` in the half-space through `c` with outer normal `x − c`, against
every opponent action `b`. -/
theorem exists_inner_sub_nonpos_of_enforceable {A B : Type*} [Fintype A] (v : A → B → E)
    {C : Set E} (hC : Convex ℝ C)
    (henf : ∀ (lam : E) (ρ : ℝ), (∀ c ∈ C, ⟪lam, c⟫ ≤ ρ) →
      ∃ q : Convexity.StdSimplex ℝ A, ∀ b, ⟪lam, ∑ a, q.weights a • v a b⟫ ≤ ρ)
    {x c : E} (hc : c ∈ C) (hnear : ‖x - c‖ = ⨅ w : C, ‖x - w‖) :
    ∃ q : Convexity.StdSimplex ℝ A, ∀ b, ⟪x - c, ∑ a, q.weights a • v a b - c⟫ ≤ 0 := by
  have hproj := (norm_eq_iInf_iff_real_inner_le_zero hC hc).1 hnear
  obtain ⟨q, hb⟩ := henf (x - c) ⟪x - c, c⟫ fun w hw => by
    have := hproj w hw
    rw [inner_sub_right] at this
    linarith
  exact ⟨q, fun b => by rw [inner_sub_right]; linarith [hb b]⟩

/-- The expected vector payoff `v(q, b) = ∑ₐ q(a) v(a, b)` of the mixed action `q`. -/
def mixedPayoff {A B : Type*} [Fintype A] (v : A → B → E) (q : A → ℝ) (b : B) : E :=
  ∑ a, q a • v a b

/-- The running sums of expected payoffs when the decision maker plays `σ x̄` against the
opponent's action `β n` at stage `n`, where `x̄` is the current average expected payoff. -/
noncomputable def strategySums {A B : Type*} [Fintype A] (v : A → B → E) (σ : E → A → ℝ)
    (β : ℕ → B) : ℕ → E
  | 0 => 0
  | n + 1 => strategySums v σ β n +
      mixedPayoff v (σ ((n : ℝ)⁻¹ • strategySums v σ β n)) (β n)

/-- The expected vector payoff at stage `n` of the strategy `σ` against `β`. -/
noncomputable def strategyPayoffs {A B : Type*} [Fintype A] (v : A → B → E) (σ : E → A → ℝ)
    (β : ℕ → B) (n : ℕ) : E :=
  mixedPayoff v (σ ((n : ℝ)⁻¹ • strategySums v σ β n)) (β n)

/-- The stage payoffs of `strategyPayoffs` add up to the running sums `strategySums`. -/
theorem sum_range_strategyPayoffs {A B : Type*} [Fintype A] (v : A → B → E) (σ : E → A → ℝ)
    (β : ℕ → B) (n : ℕ) : ∑ k ∈ range n, strategyPayoffs v σ β k = strategySums v σ β n := by
  induction n with
  | zero => simp [strategySums]
  | succ n ih => rw [sum_range_succ, ih]; rfl

/-- A mixed action's expected payoff is a convex combination of pure payoffs, so it obeys any
bound `‖v a b‖ ≤ R` on them. -/
theorem norm_mixedPayoff_le {A B : Type*} [Fintype A] {v : A → B → E} {R : ℝ}
    (hR : ∀ a b, ‖v a b‖ ≤ R) (q : Convexity.StdSimplex ℝ A) (b : B) :
    ‖mixedPayoff v q.weights b‖ ≤ R := by
  calc ‖mixedPayoff v q.weights b‖ ≤ ∑ a, ‖q.weights a • v a b‖ := norm_sum_le _ _
    _ = ∑ a, q.weights a * ‖v a b‖ := by
        refine sum_congr rfl fun a _ => ?_
        rw [norm_smul, Real.norm_of_nonneg (q.weights_nonneg a)]
    _ ≤ ∑ a, q.weights a * R :=
        sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hR a b) (q.weights_nonneg a)
    _ = R := by rw [← sum_mul, q.total_of_fintype, one_mul]

/-- **Blackwell's approachability theorem, expected-payoff form.** Let `E` be a real Hilbert
space, `v : A → B → E` a vector-payoff function with `A` finite and `‖v a b‖ ≤ R`, and `C ⊆ E`
nonempty, closed and convex. If every closed half-space containing `C` is enforceable (Hart 2005,
Appendix, Theorem 5; Hart and Mas-Colell 2000, (3.2)), then the Blackwell strategy `σ`, a map
from the current average expected payoff to a mixed action, satisfies, against every sequence
`β` of opponent actions and for every `c₀ ∈ C`,
`dist(x̄_n, C) ≤ (3R + ‖c₀‖) / √n` for all `n ≥ 1`, where `x̄_n` is the average of the first `n`
expected payoffs. (As the decision maker's mixed actions are determined by `β`, this covers
opponents who adapt to past play.) This is the expected-payoff estimate in the proof of
Theorem 5 of Hart 2005 (`E[t² δ_t] ≤ M² t`), without the probabilistic layer. -/
theorem blackwell_expected_approachability [CompleteSpace E] {A B : Type*} [Fintype A]
    (v : A → B → E) {C : Set E} (hne : C.Nonempty) (hcl : IsClosed C) (hcv : Convex ℝ C)
    (henf : ∀ (lam : E) (ρ : ℝ), (∀ c ∈ C, ⟪lam, c⟫ ≤ ρ) →
      ∃ q : Convexity.StdSimplex ℝ A, ∀ b, ⟪lam, ∑ a, q.weights a • v a b⟫ ≤ ρ)
    {R : ℝ} (hR : ∀ a b, ‖v a b‖ ≤ R) :
    ∃ σ : E → Convexity.StdSimplex ℝ A,
      ∀ (β : ℕ → B) (c₀ : E), c₀ ∈ C → ∀ n, 0 < n →
        infDist (average (strategyPayoffs v (fun x => (σ x).weights) β) n) C ≤
          (3 * R + ‖c₀‖) / Real.sqrt n := by
  -- nearest points
  have hnp : ∀ x : E, ∃ c ∈ C, ‖x - c‖ = ⨅ w : C, ‖x - w‖ := fun x =>
    exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hcv x
  choose near hnearC hnear using hnp
  have hstep : ∀ x : E, ∃ q : Convexity.StdSimplex ℝ A,
      ∀ b, ⟪x - near x, ∑ a, q.weights a • v a b - near x⟫ ≤ 0 := fun x =>
    exists_inner_sub_nonpos_of_enforceable v hcv henf (hnearC x) (hnear x)
  choose σ hσb using hstep
  refine ⟨σ, fun β c₀ hc₀ n hn => ?_⟩
  set y := strategyPayoffs v (fun x => (σ x).weights) β
  have havg : ∀ m,
      average y m = (m : ℝ)⁻¹ • strategySums v (fun x => (σ x).weights) β m := fun m => by
    rw [average, sum_range_strategyPayoffs]
  have hinfD : ∀ x : E, ‖x - near x‖ = infDist x C := fun x => by
    rw [hnear x, infDist_eq_iInf]
    simp [dist_eq_norm]
  have hy : ∀ m, ‖y m‖ ≤ R := fun m => norm_mixedPayoff_le hR (σ _) _
  -- `R ≥ 0` (B is inhabited by `β 0`, A by any point of the simplex)
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hy 0)
  have havgR : ∀ m, ‖average y m‖ ≤ R := fun m => by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [average, hR0]
    · rw [average, norm_smul, Real.norm_of_nonneg (by positivity)]
      have hm' : (0 : ℝ) < m := by exact_mod_cast hm
      calc (m : ℝ)⁻¹ * ‖∑ k ∈ range m, y k‖ ≤ (m : ℝ)⁻¹ * ∑ k ∈ range m, ‖y k‖ :=
            mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
        _ ≤ (m : ℝ)⁻¹ * ∑ _k ∈ range m, R :=
            mul_le_mul_of_nonneg_left (sum_le_sum fun k _ => hy k) (by positivity)
        _ = R := by rw [sum_const, card_range, nsmul_eq_mul]; field_simp
  refine infDist_average_le (c := fun m => near (average y m)) (fun m => hnearC _)
    (fun m _ => hinfD _) (fun m _ => ?_) (fun m => ?_) hn
  · have := hσb (average y m) (β m)
    rw [havg m] at this ⊢
    exact this
  · -- `‖y_m − c_m‖ ≤ ‖y_m‖ + ‖x̄_m‖ + ‖x̄_m − c_m‖ ≤ 2R + dist(x̄_m, c₀) ≤ 3R + ‖c₀‖`
    have h1 : ‖average y m - near (average y m)‖ ≤ ‖average y m - c₀‖ := by
      rw [hinfD, ← dist_eq_norm]
      exact infDist_le_dist_of_mem hc₀
    calc ‖y m - near (average y m)‖
        ≤ ‖y m‖ + ‖average y m‖ + ‖average y m - near (average y m)‖ := by
          have := norm_sub_le (y m - average y m) (near (average y m) - average y m)
          have h2 := norm_sub_le (y m) (average y m)
          rw [norm_sub_rev (near (average y m)) (average y m)] at this
          calc ‖y m - near (average y m)‖
              = ‖(y m - average y m) - (near (average y m) - average y m)‖ := by
                congr 1; abel
            _ ≤ _ := this
            _ ≤ _ := by linarith
      _ ≤ R + R + (‖average y m‖ + ‖c₀‖) := by
          gcongr
          · exact hy m
          · exact havgR m
          · exact h1.trans (norm_sub_le _ _)
      _ ≤ 3 * R + ‖c₀‖ := by linarith [havgR m]

end MathlibExt.GameTheory.BlackwellApproachability
