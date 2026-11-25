/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.BlackwellApproachability
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
import MathlibExt.Analysis.Series.Kronecker
import MathlibExt.MeasureTheory.Function.ConditionalExpectation.FiniteValued
import MathlibExt.Probability.SqMartingaleConvergence

/-! # Blackwell's approachability theorem, almost-sure form

In a repeated game with vector payoffs `v a b ∈ ℝᵈ` (`a` the decision maker's action, `b` the
opponent's, both from finite sets), let `C` be a nonempty closed convex set every closed half-space
of which containing `C` is enforceable. The *Blackwell strategy* `σ` maps the current average
payoff `x̄` to a mixed action that keeps the expected payoff in the half-space through the nearest
point `c` of `C` to `x̄` with outer normal `x̄ − c`. `blackwell_approachability`: whatever the
opponent does, provided its next action is conditionally independent of the decision maker's
given the past, the average realised payoff converges to `C` almost surely (Blackwell 1956,
Theorem 1 and §3; Hart 2005, Appendix, Theorem 5 (ii)). The expected-payoff form, with rate
`M / √n`, is `blackwell_expected_approachability` in
`MathlibExt.GameTheory.BlackwellApproachability`.

Randomised play is modelled on a probability space `(Ω, P)` by a process `Z : ℕ → Ω → A × B` of
realised action pairs; `historySigma Z n` is the σ-algebra of the events determined by
`Z 0, …, Z n`, and the conditional law of `Z (n + 1)` given it is written with conditional
expectations of indicators.

## Main results

* `historySigma`: the σ-algebra of the events determined by the first rounds of a process.
* `historySigma_mono`, `historySigma_le`, `measurable_historySigma`: for a finite-valued process
  with measurable level sets, the history σ-algebras form a filtration of the ambient σ-algebra,
  and every function of the first `n + 1` rounds is measurable for the history σ-algebra at time
  `n`.
* `blackwell_approachability`: Blackwell's approachability theorem for realised payoffs, with
  almost-sure convergence.

## Proof outline

Write `y_k` for the payoff of round `k`, `x̄_n` for the average of `y_0, …, y_{n-1}`, `c_n` for the
nearest point of `C` to `x̄_n`, `d_n = dist(x̄_n, C)` and `ξ_n = ⟪x̄_n − c_n, y_n − c_n⟫`.

* Recursion (Blackwell 1956, (2)–(5); Hart 2005, (13)): since
  `(n + 1)(x̄_{n+1} − c_n) = n (x̄_n − c_n) + (y_n − c_n)`, we get
  `((n + 1) d_{n+1})² ≤ (n d_n)² + 2 n ξ_n + M²`, where `M` bounds `‖y_n − c_n‖`
  (`sq_succ_mul_infDist_average_le`), and by induction
  `((n + 1) d_{n+1})² ≤ (n + 1) M² + 2 ∑_{k < n} (k + 1) ξ_{k+1}`.
* Half-space step (Blackwell 1956, (1)): the history `Z 0, …, Z k` determines `x̄_{k+1}` and
  `c_{k+1}`, so the factorisation of the conditional law of `Z (k + 1)` gives
  `E[ξ_{k+1} | history] = ∑_b P(b | history) ⟪x̄_{k+1} − c_{k+1}, v(σ(x̄_{k+1}), b) − c_{k+1}⟫ ≤ 0`.
  Hence `ξ_{k+1} ≤ e_k`, where `e_k = ξ_{k+1} − E[ξ_{k+1} | history]` are bounded martingale
  differences.
* Strong law: the series `∑_k e_k / (k + 1)` converges almost surely, as a martingale with
  bounded predictable quadratic variation (`MeasureTheory.ae_exists_tendsto_sum_div_succ`), and
  Kronecker's lemma with the weights `(k + 1)²`
  (`MetaMathlibExt.tendsto_sum_range_add_one_sq_mul_div_of_tendsto`) gives
  `(∑_{k < n} (k + 1) e_k) / (n + 1)² → 0` almost surely (Williams 1991, Chapter 12). The
  sources use a strong law of large numbers for bounded martingale differences at this point
  instead (Blackwell 1956, Theorem 2; Hart 2005, footnote 38).
* So `d_{n+1}² ≤ M² / (n + 1) + 2 (∑_{k < n} (k + 1) e_k) / (n + 1)² → 0` almost surely.

## Implementation notes

`historySigma` and `blackwell_approachability` keep the full names, statements and docstrings of
the former wanted declarations, so their namespace is `BlackwellApproachabilityWanted`. The
statement carries `[Fintype B]`, which its type does not need (the proof sums over the opponent's
actions); the `unusedFintypeInType` linter is turned off for this theorem only. The history
σ-algebras are sub-σ-algebras of the ambient one because the action sets are finite and the
events `{Z n = z}` are measurable; every function of `Z 0, …, Z n` is measurable for
`historySigma Z n`, whatever its target, which covers the strategy `σ` and the nearest-point map,
neither of which needs to be measurable.

## References

* D. Blackwell, "An analog of the minimax theorem for vector payoffs", Pacific J. Math. 6
  (1956), 1–8: Theorem 1 and its proof, (1)–(7); Theorem 2; §3, Theorem 3.
* S. Hart, "Adaptive heuristics", Econometrica 73(5) (2005), 1401–1430: Appendix, Theorem 5 and
  its proof, equation (13) and footnote 38.
* S. Hart and A. Mas-Colell, "A simple adaptive procedure leading to correlated equilibrium",
  Econometrica 68(5) (2000), 1127–1150: §3, Blackwell's Approachability Theorem.
* D. Williams, *Probability with Martingales*, Cambridge University Press (1991), Chapter 12,
  martingales bounded in `L²` and Kronecker's lemma.
-/

@[expose] public section

namespace MathlibExt.GameTheory.BlackwellApproachabilityWanted

open MeasureTheory Filter Topology Finset
open MathlibExt.GameTheory.BlackwellApproachability (average exists_inner_sub_nonpos_of_enforceable
  norm_average_le sq_succ_mul_infDist_average_le)

/-- The σ-algebra of the events determined by the history `Z 0, …, Z t` of a process (each
`Z k` carrying the discrete σ-algebra on its values). -/
@[instance_reducible]
def historySigma {Ω α : Type*} (Z : ℕ → Ω → α) (t : ℕ) : MeasurableSpace Ω :=
  ⨆ k ≤ t, MeasurableSpace.comap (Z k) ⊤

/-! ### History σ-algebras -/

section History

variable {Ω α : Type*}

/-- **Monotonicity of the history σ-algebras**: the history σ-algebras grow with time. -/
theorem historySigma_mono (Z : ℕ → Ω → α) : Monotone (historySigma Z) :=
  fun _ _ hnm => iSup₂_mono' fun k hk => ⟨k, hk.trans hnm, le_rfl⟩

/-- **History σ-algebras are sub-σ-algebras**: the history σ-algebras of a finite-valued process
with measurable level sets are sub-σ-algebras of the ambient one. -/
theorem historySigma_le [mΩ : MeasurableSpace Ω] [Finite α] {Z : ℕ → Ω → α}
    (hZ : ∀ n z, MeasurableSet {ω | Z n ω = z}) (n : ℕ) : historySigma Z n ≤ mΩ :=
  iSup₂_le fun k _ => (@measurable_to_countable' α Ω ⊤ _ _ (Z k) fun z => hZ k z).comap_le

/-- Every event about `Z k`, for `k ≤ n`, is in the history σ-algebra at time `n`. -/
private lemma measurableSet_historySigma_preimage {Z : ℕ → Ω → α} {n k : ℕ} (hk : k ≤ n)
    (s : Set α) : MeasurableSet[historySigma Z n] (Z k ⁻¹' s) :=
  le_iSup₂ (f := fun k (_ : k ≤ n) => MeasurableSpace.comap (Z k) ⊤) k hk _ ⟨s, trivial, rfl⟩

/-- **Measurability of functions of the history**: a function of the first `n + 1` values of a
finite-valued process is measurable for the history σ-algebra at time `n`, whatever its
target. -/
theorem measurable_historySigma [Finite α] {Z : ℕ → Ω → α} {n : ℕ} {β : Type*}
    [MeasurableSpace β] {g : Ω → β} (hg : ∀ ω ω', (∀ k ≤ n, Z k ω = Z k ω') → g ω = g ω') :
    Measurable[historySigma Z n] g := by
  intro s _
  let H : Ω → (Fin (n + 1) → α) := fun ω k => Z k ω
  have hH : ∀ T : Set (Fin (n + 1) → α), MeasurableSet[historySigma Z n] (H ⁻¹' T) := by
    intro T
    have hT : H ⁻¹' T = ⋃ h ∈ T, ⋂ k : Fin (n + 1), Z k ⁻¹' {h k} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_iInter, Set.mem_singleton_iff,
        exists_prop]
      exact ⟨fun hω => ⟨H ω, hω, fun k => rfl⟩, fun ⟨h, hT, hk⟩ => by
        have : H ω = h := funext hk
        rwa [this]⟩
    rw [hT]
    exact MeasurableSet.biUnion T.to_countable fun h _ =>
      MeasurableSet.iInter fun k => measurableSet_historySigma_preimage (Nat.lt_succ_iff.1 k.2) _
  convert hH (H '' (g ⁻¹' s)) using 1
  ext ω
  refine ⟨fun hω => ⟨ω, hω, rfl⟩, ?_⟩
  rintro ⟨ω', hω', hHω⟩
  have : g ω' = g ω := hg ω' ω fun k hk => congrFun hHω ⟨k, Nat.lt_succ_iff.2 hk⟩
  rw [Set.mem_preimage, ← this]
  exact hω'

end History

/-! ### The conditional expectation of the next round -/

section CondExp

variable {Ω A B : Type*} [Fintype A] [Finite B] {m mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- Let `m ≤ mΩ` be a sub-σ-algebra and `X` a random action pair with measurable level sets whose
conditional law given `m` factorises as `P(X = (a, b) | m) = q a · P(X.2 = b | m)`. Let `g z`,
for `z : A × B`, be `m`-measurable functions bounded by `K` with `∑ a, q a · g (a, b) ≤ 0`
everywhere, for every `b`. Then `E[g X | m] ≤ 0` almost surely. -/
private lemma condExp_comp_nonpos (hm : m ≤ mΩ) {X : Ω → A × B}
    (hX : ∀ z, MeasurableSet {ω | X ω = z}) {g : A × B → Ω → ℝ} {K : ℝ}
    (hg : ∀ z, StronglyMeasurable[m] (g z)) (hgK : ∀ z ω, |g z ω| ≤ K) {q : Ω → A → ℝ}
    (hlaw : ∀ a b, P[{ω | X ω = (a, b)}.indicator (fun _ => (1 : ℝ)) | m] =ᵐ[P]
      fun ω => q ω a * P[{ω | (X ω).2 = b}.indicator (fun _ => (1 : ℝ)) | m] ω)
    (hneg : ∀ ω b, ∑ a, q ω a * g (a, b) ω ≤ 0) :
    P[fun ω => g (X ω) ω | m] ≤ᵐ[P] 0 := by
  classical
  have := Fintype.ofFinite B
  have h3 := ae_all_iff.2 fun a => ae_all_iff.2 fun b => hlaw a b
  have h4 : ∀ᵐ ω ∂P, ∀ b,
      0 ≤ P[{ω | (X ω).2 = b}.indicator (fun _ => (1 : ℝ)) | m] ω :=
    ae_all_iff.2 fun b => condExp_nonneg
      (ae_of_all _ fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
  filter_upwards [condExp_comp_eq_sum hm hX hg hgK, h3, h4] with ω h1 h3 h4
  rw [h1, Pi.zero_apply, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_nonpos fun b _ => ?_
  have : ∑ a, g (a, b) ω * P[{ω | X ω = (a, b)}.indicator (fun _ => (1 : ℝ)) | m] ω =
      P[{ω | (X ω).2 = b}.indicator (fun _ => (1 : ℝ)) | m] ω * ∑ a, q ω a * g (a, b) ω := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [h3 a b]
    ring
  rw [this]
  exact mul_nonpos_of_nonneg_of_nonpos (h4 b) (hneg ω b)

end CondExp

/-! ### The squared-distance recursion -/

section Recursion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => @inner ℝ E _ x y

/-- Blackwell's recursion summed, for realised payoffs: if `c n` is a nearest point of `C` to
`x̄_n` and `‖y n − c n‖ ≤ M` for every `n`, then `((n + 1) dist(x̄_{n+1}, C))²` is at most
`(n + 1) M² + 2 ∑_{k < n} (k + 1) ⟪x̄_{k+1} − c_{k+1}, y_{k+1} − c_{k+1}⟫`. -/
private lemma sq_succ_mul_infDist_average_le_sum {C : Set E} {y c : ℕ → E} {M : ℝ}
    (hc : ∀ n, c n ∈ C) (hnear : ∀ n, ‖average y n - c n‖ = Metric.infDist (average y n) C)
    (hM : ∀ n, ‖y n - c n‖ ≤ M) (n : ℕ) :
    (((n : ℝ) + 1) * Metric.infDist (average y (n + 1)) C) ^ 2 ≤
      ((n : ℝ) + 1) * M ^ 2 + 2 * ∑ k ∈ range n,
        ((k : ℝ) + 1) * ⟪average y (k + 1) - c (k + 1), y (k + 1) - c (k + 1)⟫ := by
  have hM2 : ∀ n, ‖y n - c n‖ ^ 2 ≤ M ^ 2 := fun n => pow_le_pow_left₀ (norm_nonneg _) (hM n) 2
  induction n with
  | zero =>
    have := sq_succ_mul_infDist_average_le y (hc 0) 0
    simp only [CharP.cast_eq_zero, zero_mul, zero_add, one_mul, mul_zero, zero_pow two_ne_zero,
      zero_add, range_zero, sum_empty] at this ⊢
    linarith [hM2 0]
  | succ n ih =>
    have h := sq_succ_mul_infDist_average_le y (hc (n + 1)) (n + 1)
    rw [hnear (n + 1)] at h
    rw [sum_range_succ]
    push_cast at h ⊢
    linarith [hM2 (n + 1)]

/-- The average of the first `n` terms depends only on those terms. -/
private lemma average_congr {y y' : ℕ → E} {n : ℕ} (h : ∀ k < n, y k = y' k) :
    average y n = average y' n := by
  simp only [BlackwellApproachability.average]
  rw [sum_congr rfl fun k hk => h k (mem_range.1 hk)]

end Recursion

/-! ### Blackwell's theorem -/

set_option linter.unusedFintypeInType false in
/-- **Blackwell's approachability theorem** (Blackwell 1956, Theorem 1 and §3; Hart 2005,
Appendix, Theorem 5; Hart and Mas-Colell 2000, §3). Let `v : A → B → ℝᵈ` be a vector payoff with
finite action sets and `C` a nonempty closed convex set every closed half-space of which
containing `C` is enforceable. Then `C` is approachable: some strategy `σ` of the decision
maker, mapping the current average payoff to a mixed action (the Blackwell strategy), guarantees
that whatever the opponent does (randomising or not, independently of the decision maker's
current randomisation given the past) the average realised vector payoff converges to `C` almost
surely. The first round is arbitrary. -/
theorem blackwell_approachability {d : ℕ} {A B : Type*} [Fintype A] [Fintype B]
    (v : A → B → EuclideanSpace ℝ (Fin d)) {C : Set (EuclideanSpace ℝ (Fin d))}
    (hne : C.Nonempty) (hcl : IsClosed C) (hcv : Convex ℝ C)
    (henf : ∀ (lam : EuclideanSpace ℝ (Fin d)) (ρ : ℝ), (∀ c ∈ C, @inner ℝ _ _ lam c ≤ ρ) →
      ∃ q : Convexity.StdSimplex ℝ A, ∀ b, @inner ℝ _ _ lam (∑ a, q.weights a • v a b) ≤ ρ) :
    ∃ σ : EuclideanSpace ℝ (Fin d) → Convexity.StdSimplex ℝ A,
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (Z : ℕ → Ω → A × B), (∀ n z, MeasurableSet {ω | Z n ω = z}) →
        (∀ n a b,
          P[{ω | Z (n + 1) ω = (a, b)}.indicator (fun _ => (1 : ℝ)) | historySigma Z n] =ᵐ[P]
            fun ω => (σ (average (fun k => v (Z k ω).1 (Z k ω).2) (n + 1))).weights a *
              P[{ω | (Z (n + 1) ω).2 = b}.indicator (fun _ => (1 : ℝ)) | historySigma Z n] ω) →
        ∀ᵐ ω ∂P, Tendsto
          (fun n => Metric.infDist (average (fun k => v (Z k ω).1 (Z k ω).2) n) C) atTop (𝓝 0) := by
  classical
  -- the Blackwell strategy: a mixed action enforcing the half-space through the nearest point
  have hnp : ∀ x : EuclideanSpace ℝ (Fin d), ∃ c ∈ C, ‖x - c‖ = ⨅ w : C, ‖x - w‖ := fun x =>
    exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hcv x
  choose near hnearC hnear using hnp
  have hinfD : ∀ x, ‖x - near x‖ = Metric.infDist x C := fun x => by
    rw [hnear x, Metric.infDist_eq_iInf]
    simp [dist_eq_norm]
  have hstep : ∀ x : EuclideanSpace ℝ (Fin d), ∃ q : Convexity.StdSimplex ℝ A,
      ∀ b, inner ℝ (x - near x) (∑ a, q.weights a • v a b - near x) ≤ 0 := fun x =>
    exists_inner_sub_nonpos_of_enforceable v hcv henf (hnearC x) (hnear x)
  choose σ hσ using hstep
  refine ⟨σ, fun {Ω} mΩ P _ Z hZ hlaw => ?_⟩
  -- bounds on the payoffs, their averages and the inner products of the recursion
  obtain ⟨c₀, hc₀⟩ := hne
  set R : ℝ := ∑ a, ∑ b, ‖v a b‖ with hRdef
  have hR0 : 0 ≤ R := sum_nonneg fun a _ => sum_nonneg fun b _ => norm_nonneg _
  have hR : ∀ a b, ‖v a b‖ ≤ R := fun a b =>
    (single_le_sum (fun b _ => norm_nonneg (v a b)) (mem_univ b)).trans
      (single_le_sum (f := fun a => ∑ b, ‖v a b‖) (fun a _ => sum_nonneg fun b _ => norm_nonneg _)
        (mem_univ a))
  set M : ℝ := 3 * R + ‖c₀‖ with hMdef
  have hbd : ∀ x w : EuclideanSpace ℝ (Fin d), ‖x‖ ≤ R → ‖w‖ ≤ R →
      ‖x - near x‖ ≤ M ∧ ‖w - near x‖ ≤ M := by
    intro x w hx hw
    have h1 : ‖x - near x‖ ≤ ‖x‖ + ‖c₀‖ := by
      rw [hinfD]
      exact (Metric.infDist_le_dist_of_mem hc₀).trans (by rw [dist_eq_norm]; exact norm_sub_le _ _)
    have h2 : ‖w - near x‖ ≤ ‖w‖ + ‖x‖ + ‖x - near x‖ :=
      calc ‖w - near x‖ = ‖(w - x) + (x - near x)‖ := by congr 1; abel
        _ ≤ ‖w - x‖ + ‖x - near x‖ := norm_add_le _ _
        _ ≤ ‖w‖ + ‖x‖ + ‖x - near x‖ := by gcongr; exact norm_sub_le _ _
    constructor <;> linarith [norm_nonneg c₀]
  have hinner_bd : ∀ x w : EuclideanSpace ℝ (Fin d), ‖x‖ ≤ R → ‖w‖ ≤ R →
      |inner ℝ (x - near x) (w - near x)| ≤ M * M := fun x w hx hw =>
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hbd x w hx hw).1 (hbd x w hx hw).2 (norm_nonneg _)
        (by linarith [norm_nonneg c₀]))
  -- the realised payoffs and the inner products `ξ k = ⟪x̄_k − c_k, y_k − c_k⟫`
  set y : Ω → ℕ → EuclideanSpace ℝ (Fin d) := fun ω k => v (Z k ω).1 (Z k ω).2 with hydef
  have hy : ∀ ω k, ‖y ω k‖ ≤ R := fun ω k => hR _ _
  have hyavg : ∀ ω n, ‖average (y ω) n‖ ≤ R := fun ω n => norm_average_le (hy ω) n
  set ξ : ℕ → Ω → ℝ := fun k ω => inner ℝ (average (y ω) k - near (average (y ω) k))
    (y ω k - near (average (y ω) k)) with hξdef
  have hξK : ∀ k ω, |ξ k ω| ≤ M * M := fun k ω => hinner_bd _ _ (hyavg ω k) (hy ω k)
  -- the filtration of histories
  let ℱ : Filtration ℕ mΩ := ⟨historySigma Z, historySigma_mono Z, historySigma_le hZ⟩
  have havg_congr : ∀ n ω ω', (∀ k ≤ n, Z k ω = Z k ω') →
      average (y ω) (n + 1) = average (y ω') (n + 1) := fun n ω ω' h =>
    average_congr fun k hk => by simp only [hydef, h k (Nat.lt_succ_iff.1 hk)]
  have hξm : ∀ k, StronglyMeasurable[ℱ k] (ξ k) := fun k => by
    refine (measurable_historySigma fun ω ω' h => ?_).stronglyMeasurable
    have h1 : average (y ω) k = average (y ω') k :=
      average_congr fun j hj => by simp only [hydef, h j hj.le]
    have h2 : y ω k = y ω' k := by simp only [hydef, h k le_rfl]
    simp only [hξdef, h1, h2]
  have hξint : ∀ k, Integrable (ξ k) P := fun k =>
    Integrable.of_bound ((hξm k).mono (ℱ.le k)).aestronglyMeasurable (M * M)
      (ae_of_all _ fun ω => (Real.norm_eq_abs _).le.trans (hξK k ω))
  -- Blackwell's half-space step in conditional expectation: `E[ξ_{n+1} | history] ≤ 0`
  have hneg : ∀ n, P[ξ (n + 1) | historySigma Z n] ≤ᵐ[P] 0 := by
    intro n
    refine condExp_comp_nonpos (historySigma_le hZ n) (hZ (n + 1))
      (g := fun z ω => inner ℝ (average (y ω) (n + 1) - near (average (y ω) (n + 1)))
        (v z.1 z.2 - near (average (y ω) (n + 1)))) (K := M * M) (fun z => ?_)
      (fun z ω => hinner_bd _ _ (hyavg ω _) (hR _ _))
      (q := fun ω => (σ (average (y ω) (n + 1))).weights) (hlaw n) (fun ω b => ?_)
    · refine (measurable_historySigma fun ω ω' h => ?_).stronglyMeasurable
      simp only [havg_congr n ω ω' h]
    · set x := average (y ω) (n + 1)
      calc ∑ a, (σ x).weights a * inner ℝ (x - near x) (v a b - near x)
          = inner ℝ (x - near x) (∑ a, (σ x).weights a • v a b - near x) := by
            simp only [inner_sub_right, mul_sub, sum_sub_distrib, inner_sum,
              real_inner_smul_right, ← sum_mul, (σ x).total_of_fintype, one_mul]
        _ ≤ 0 := hσ x b
  -- the martingale differences `e k = ξ_{k+1} − E[ξ_{k+1} | history up to k]`
  set e : ℕ → Ω → ℝ := fun k => ξ (k + 1) - P[ξ (k + 1) | ℱ k] with hedef
  have he : ∀ k, StronglyMeasurable[ℱ (k + 1)] (e k) := fun k =>
    (hξm (k + 1)).sub (stronglyMeasurable_condExp.mono (ℱ.mono k.le_succ))
  have heK : ∀ k, ∀ᵐ ω ∂P, |e k ω| ≤ 2 * (M * M) := fun k => by
    filter_upwards [ae_bdd_abs_condExp_of_ae_bdd_abs (m := ℱ k) (ae_of_all P (hξK (k + 1)))]
      with ω hω
    calc |e k ω| = |ξ (k + 1) ω - P[ξ (k + 1) | ℱ k] ω| := rfl
      _ ≤ |ξ (k + 1) ω| + |P[ξ (k + 1) | ℱ k] ω| := abs_sub _ _
      _ ≤ 2 * (M * M) := by linarith [hξK (k + 1) ω]
  have hce : ∀ k, P[e k | ℱ k] =ᵐ[P] 0 := fun k => by
    have h := condExp_sub (hξint (k + 1)) (integrable_condExp (m := ℱ k) (f := ξ (k + 1)))
      (ℱ k : MeasurableSpace Ω)
    have h2 : P[P[ξ (k + 1) | ℱ k] | ℱ k] = P[ξ (k + 1) | ℱ k] :=
      condExp_of_stronglyMeasurable (ℱ.le k) stronglyMeasurable_condExp integrable_condExp
    rw [h2, sub_self] at h
    exact h
  have hle : ∀ᵐ ω ∂P, ∀ k, ξ (k + 1) ω ≤ e k ω := (ae_all_iff.2 hneg).mono fun ω h k => by
    have := h k
    simp only [Pi.zero_apply] at this
    simp only [hedef, Pi.sub_apply]
    linarith
  filter_upwards [ae_exists_tendsto_sum_div_succ (μ := P) ℱ he heK hce, hle] with ω ⟨s, hs⟩ hle
  -- Kronecker's lemma: `(∑_{k < n} (k + 1) e k) / (n + 1)² → 0`
  have hK : Tendsto (fun n : ℕ => (∑ k ∈ range n, ((k : ℝ) + 1) * e k ω) / ((n : ℝ) + 1) ^ 2)
      atTop (𝓝 0) := by
    refine (MetaMathlibExt.tendsto_sum_range_add_one_sq_mul_div_of_tendsto hs).congr fun n => ?_
    congr 1
    refine sum_congr rfl fun k _ => ?_
    field_simp
  -- the squared distance at time `n + 1` tends to `0`
  have hd2 : Tendsto (fun n => Metric.infDist (average (y ω) (n + 1)) C ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => M ^ 2 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    have hup := h1.add (hK.const_mul 2)
    rw [mul_zero, add_zero] at hup
    refine squeeze_zero (fun n => sq_nonneg _) (fun n => ?_) hup
    have h : (((n : ℝ) + 1) * Metric.infDist (average (y ω) (n + 1)) C) ^ 2 ≤
        ((n : ℝ) + 1) * M ^ 2 + 2 * ∑ k ∈ range n, ((k : ℝ) + 1) * ξ (k + 1) ω :=
      sq_succ_mul_infDist_average_le_sum (c := fun k => near (average (y ω) k))
        (fun k => hnearC _) (fun k => hinfD _) (fun k => (hbd _ _ (hyavg ω k) (hy ω k)).2) n
    have hsum : ∑ k ∈ range n, ((k : ℝ) + 1) * ξ (k + 1) ω ≤
        ∑ k ∈ range n, ((k : ℝ) + 1) * e k ω :=
      sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hle k) (by positivity)
    have hrhs : M ^ 2 / ((n : ℝ) + 1) +
        2 * ((∑ k ∈ range n, ((k : ℝ) + 1) * e k ω) / ((n : ℝ) + 1) ^ 2) =
        (((n : ℝ) + 1) * M ^ 2 + 2 * ∑ k ∈ range n, ((k : ℝ) + 1) * e k ω) /
          ((n : ℝ) + 1) ^ 2 := by
      field_simp
    rw [hrhs, le_div_iff₀ (by positivity)]
    rw [mul_pow] at h
    linarith
  have hd : Tendsto (fun n => Metric.infDist (average (y ω) (n + 1)) C) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hd2
    rw [Real.sqrt_zero] at this
    exact this.congr fun n => Real.sqrt_sq Metric.infDist_nonneg
  exact (tendsto_add_atTop_iff_nat 1).1 hd

end MathlibExt.GameTheory.BlackwellApproachabilityWanted
