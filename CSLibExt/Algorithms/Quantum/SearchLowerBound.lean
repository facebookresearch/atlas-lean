/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The hybrid argument and the `Ω(√N)` lower bound for quantum search

A `T`-query quantum algorithm alternates fixed linear isometries `U₀, U₁, …, U_T` with `T`
calls to an oracle. Running it with the oracle `O_y` that marks the item `y` or with no oracle
at all (the identity) gives final states that differ by at most the sum, over the queries, of
how much `O_y` moves the oracle-free intermediate state (`norm_queryRun_sub_queryRun_le`; Bennett,
Bernstein, Brassard and Vazirani, Theorem 3.3, and Bernstein and Vazirani, Theorem 3.4.1:
errors made along a unitary evolution only add). When `O_y` moves a state by at most twice its
query amplitude on `y`, and the query amplitudes of a state over all `y` have total squared norm
at most that of the state (Bennett et al., Definition 3.2), Cauchy–Schwarz gives
`∑_y ‖ψ_T^y - ψ_T‖² ≤ 4 T² ‖ψ₀‖²` (`sum_norm_queryRun_sub_queryRun_sq_le`), a summed form of
Bennett et al., Corollary 3.4.

If the algorithm finds every `y` with probability at least `p`, then `p N ≤ 8 T² + 2`
(`mul_card_le_of_forall_success`): unstructured search over `N` items needs `Ω(√N)` queries,
which Grover's algorithm attains. The concrete model (`markingOracle`, `queryProj`) is a state
space `ℓ²(ι × W)` with a query register `ι` and a workspace `W`, the oracle `O_y` negating the
amplitudes whose query register holds `y`, and success meaning that measuring the query
register at the end gives `y` (`card_le_of_forall_success`).

## Sources

* C. H. Bennett, E. Bernstein, G. Brassard and U. Vazirani, *Strengths and weaknesses of
  quantum computing*, SIAM J. Comput. 26 (1997), 1510–1523; arXiv:quant-ph/9701001,
  Section 3.1 (Definition 3.2, Theorem 3.3, Corollary 3.4, Theorem 3.5).
* E. Bernstein and U. Vazirani, *Quantum complexity theory*, SIAM J. Comput. 26 (1997),
  1411–1473; author-hosted version dated September 8, 1997, Theorem 3.4.1.
-/

@[expose] public section

open Finset

namespace Cslib.QuantumSearchLowerBound

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Run of a query algorithm.** Given linear isometries `U k` and an oracle map `R`, the state
after the `k`-th query step: `queryRun U R ψ₀ 0 = U 0 ψ₀` and
`queryRun U R ψ₀ (k + 1) = U (k + 1) (R (queryRun U R ψ₀ k))`. A `T`-query algorithm ends in
`queryRun U R ψ₀ T` (Bennett, Bernstein, Brassard and Vazirani, Section 3.1: the oracle machine
alternates oracle-independent unitary steps with oracle calls). -/
def queryRun (U : ℕ → E →ₗᵢ[ℂ] E) (R : E → E) (ψ₀ : E) : ℕ → E
  | 0 => U 0 ψ₀
  | k + 1 => U (k + 1) (R (queryRun U R ψ₀ k))

/-- **The oracle-free run preserves the norm.** `‖queryRun U id ψ₀ k‖ = ‖ψ₀‖`, since every step
is a linear isometry. -/
theorem norm_queryRun_id (U : ℕ → E →ₗᵢ[ℂ] E) (ψ₀ : E) (k : ℕ) :
    ‖queryRun U id ψ₀ k‖ = ‖ψ₀‖ := by
  induction k with
  | zero => simp [queryRun]
  | succ k ih => simp [queryRun, ih]

/-- **Hybrid argument.** For a linear isometry `O`, the final states of a `T`-query algorithm
queryRun with oracle `O` and with no oracle differ by at most `∑_{k < T} ‖O φ_k - φ_k‖`, where `φ_k`
is the oracle-free state before query `k + 1` (Bennett, Bernstein, Brassard and Vazirani,
Theorem 3.3, whose proof writes the difference as a sum of per-query errors carried forward by
unitaries; Bernstein and Vazirani, Theorem 3.4.1). -/
theorem norm_queryRun_sub_queryRun_le (U : ℕ → E →ₗᵢ[ℂ] E) (O : E →ₗᵢ[ℂ] E) (ψ₀ : E) (T : ℕ) :
    ‖queryRun U O ψ₀ T - queryRun U id ψ₀ T‖ ≤
      ∑ k ∈ range T, ‖O (queryRun U id ψ₀ k) - queryRun U id ψ₀ k‖ := by
  induction T with
  | zero => simp [queryRun]
  | succ T ih =>
    rw [sum_range_succ]
    have h : queryRun U O ψ₀ (T + 1) - queryRun U id ψ₀ (T + 1) =
        U (T + 1) (O (queryRun U O ψ₀ T) - queryRun U id ψ₀ T) := by
      simp [queryRun, map_sub]
    rw [h, LinearIsometry.norm_map]
    calc ‖O (queryRun U O ψ₀ T) - queryRun U id ψ₀ T‖
        ≤ ‖O (queryRun U O ψ₀ T) - O (queryRun U id ψ₀ T)‖ +
            ‖O (queryRun U id ψ₀ T) - queryRun U id ψ₀ T‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖queryRun U O ψ₀ T - queryRun U id ψ₀ T‖ +
            ‖O (queryRun U id ψ₀ T) - queryRun U id ψ₀ T‖ := by
          rw [← map_sub, LinearIsometry.norm_map]
      _ ≤ _ := by linarith

/-- **Summed hybrid bound.** Let `O y` (for `y` in a finite type `ι`) be linear isometries and
`P y` maps with `‖O y v - v‖ ≤ 2 ‖P y v‖` and `∑_y ‖P y v‖² ≤ ‖v‖²` for every `v` (`‖P y v‖²` is
the query magnitude of `y` in `v`, Bennett, Bernstein, Brassard and Vazirani, Definition 3.2).
Then the final states of a `T`-query algorithm satisfy `∑_y ‖ψ_T^y - ψ_T‖² ≤ 4 T² ‖ψ₀‖²`, where
`ψ_T^y` uses the oracle `O y` and `ψ_T` uses none. This is a summed form of Bennett et al.,
Corollary 3.4 (which bounds the number of `y` with `‖ψ_T^y - ψ_T‖ > ε` by `2T²/ε²`, for unit
`ψ₀` and oracles that change one answer); the proof is the same per-query accounting followed by
Cauchy–Schwarz. -/
theorem sum_norm_queryRun_sub_queryRun_sq_le {ι : Type*} [Fintype ι] (U : ℕ → E →ₗᵢ[ℂ] E)
    (O : ι → E →ₗᵢ[ℂ] E) (P : ι → E → E) (hOP : ∀ y v, ‖O y v - v‖ ≤ 2 * ‖P y v‖)
    (hP : ∀ v, ∑ y, ‖P y v‖ ^ 2 ≤ ‖v‖ ^ 2) (ψ₀ : E) (T : ℕ) :
    ∑ y, ‖queryRun U (O y) ψ₀ T - queryRun U id ψ₀ T‖ ^ 2 ≤ 4 * T ^ 2 * ‖ψ₀‖ ^ 2 := by
  set φ := queryRun U id ψ₀ with hφ
  have hy : ∀ y, ‖queryRun U (O y) ψ₀ T - φ T‖ ^ 2 ≤ 4 * T * ∑ k ∈ range T, ‖P y (φ k)‖ ^ 2 := by
    intro y
    have h1 : ‖queryRun U (O y) ψ₀ T - φ T‖ ≤ ∑ k ∈ range T, 2 * ‖P y (φ k)‖ :=
      (norm_queryRun_sub_queryRun_le U (O y) ψ₀ T).trans (sum_le_sum fun k _ => hOP y (φ k))
    calc ‖queryRun U (O y) ψ₀ T - φ T‖ ^ 2 ≤ (∑ k ∈ range T, 2 * ‖P y (φ k)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (range T).card * ∑ k ∈ range T, (2 * ‖P y (φ k)‖) ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ = 4 * T * ∑ k ∈ range T, ‖P y (φ k)‖ ^ 2 := by
          rw [card_range, mul_assoc, mul_sum, mul_sum, mul_sum]
          refine sum_congr rfl fun k _ => ?_
          ring
  calc ∑ y, ‖queryRun U (O y) ψ₀ T - φ T‖ ^ 2
      ≤ ∑ y, 4 * T * ∑ k ∈ range T, ‖P y (φ k)‖ ^ 2 := sum_le_sum fun y _ => hy y
    _ = 4 * T * ∑ k ∈ range T, ∑ y, ‖P y (φ k)‖ ^ 2 := by
        rw [← mul_sum, sum_comm]
    _ ≤ 4 * T * ∑ k ∈ range T, ‖ψ₀‖ ^ 2 := by
        gcongr with k hk
        calc ∑ y, ‖P y (φ k)‖ ^ 2 ≤ ‖φ k‖ ^ 2 := hP _
          _ = ‖ψ₀‖ ^ 2 := by rw [hφ, norm_queryRun_id]
    _ = 4 * T ^ 2 * ‖ψ₀‖ ^ 2 := by
        rw [sum_const, card_range, nsmul_eq_mul]
        ring

/-- **Lower bound for quantum search (BBBV).** In the setting of
`sum_norm_queryRun_sub_queryRun_sq_le`, let the final measurement be given by linear maps `Q y`
with `∑_y ‖Q y v‖² ≤ ‖v‖²` (the outcome
`y` has probability `‖Q y v‖²` in the state `v`), and let `‖ψ₀‖ = 1`. If for every `y` the
algorithm run with oracle `O y` outputs `y` with probability at least `p`, then
`p · N ≤ 8 T² + 2`, where `N` is the number of items. For `p = 1/2` this gives
`N ≤ 16 T² + 4`, so `T ≥ √(N - 4) / 4`: unstructured search needs `Ω(√N)` queries. This is the
query lower bound that Bennett, Bernstein, Brassard and Vazirani (Section 3.1) derive from their
Theorem 3.3 and Corollary 3.4 and use to prove Theorem 3.5 (relative to a random oracle, `NP` is
not contained in `BQTime(o(2^(n/2)))`); their final step bounds the error probability through
the total variation estimate of Theorem 3.1, while the final step here is a direct counting
argument for algorithms that succeed on every `y`. -/
theorem mul_card_le_of_forall_success {ι : Type*} [Fintype ι] (U : ℕ → E →ₗᵢ[ℂ] E)
    (O : ι → E →ₗᵢ[ℂ] E) (P : ι → E → E) (hOP : ∀ y v, ‖O y v - v‖ ≤ 2 * ‖P y v‖)
    (hP : ∀ v, ∑ y, ‖P y v‖ ^ 2 ≤ ‖v‖ ^ 2) (Q : ι → E →ₗ[ℂ] E)
    (hQ : ∀ v, ∑ y, ‖Q y v‖ ^ 2 ≤ ‖v‖ ^ 2) (ψ₀ : E) (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ) (p : ℝ)
    (hsucc : ∀ y, p ≤ ‖Q y (queryRun U (O y) ψ₀ T)‖ ^ 2) :
    p * Fintype.card ι ≤ 8 * T ^ 2 + 2 := by
  set ψ := queryRun U id ψ₀ T
  have hQ1 : ∀ y v, ‖Q y v‖ ^ 2 ≤ ‖v‖ ^ 2 := fun y v =>
    (single_le_sum (f := fun y => ‖Q y v‖ ^ 2) (fun _ _ => sq_nonneg _) (mem_univ y)).trans (hQ v)
  have hy : ∀ y, p ≤ 2 * ‖queryRun U (O y) ψ₀ T - ψ‖ ^ 2 + 2 * ‖Q y ψ‖ ^ 2 := by
    intro y
    have hsplit : Q y (queryRun U (O y) ψ₀ T) = Q y (queryRun U (O y) ψ₀ T - ψ) + Q y ψ := by
      rw [← map_add, sub_add_cancel]
    have htri := norm_add_le (Q y (queryRun U (O y) ψ₀ T - ψ)) (Q y ψ)
    rw [← hsplit] at htri
    have hd := hQ1 y (queryRun U (O y) ψ₀ T - ψ)
    nlinarith [hsucc y, norm_nonneg (Q y (queryRun U (O y) ψ₀ T)), norm_nonneg (Q y ψ),
      norm_nonneg (Q y (queryRun U (O y) ψ₀ T - ψ)),
      sq_nonneg (‖Q y (queryRun U (O y) ψ₀ T - ψ)‖ - ‖Q y ψ‖)]
  have hsum := sum_norm_queryRun_sub_queryRun_sq_le U O P hOP hP ψ₀ T
  rw [hψ₀] at hsum
  have hψ : ‖ψ‖ = 1 := by rw [norm_queryRun_id, hψ₀]
  have hQψ := hQ ψ
  rw [hψ] at hQψ
  calc p * Fintype.card ι = ∑ _y : ι, p := by rw [sum_const, card_univ, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ y, (2 * ‖queryRun U (O y) ψ₀ T - ψ‖ ^ 2 + 2 * ‖Q y ψ‖ ^ 2) := sum_le_sum fun y _ => hy y
    _ = 2 * ∑ y, ‖queryRun U (O y) ψ₀ T - ψ‖ ^ 2 + 2 * ∑ y, ‖Q y ψ‖ ^ 2 := by
        rw [sum_add_distrib, mul_sum, mul_sum]
    _ ≤ 2 * (4 * T ^ 2 * 1 ^ 2) + 2 * 1 ^ 2 := by gcongr
    _ = 8 * T ^ 2 + 2 := by ring

/-! ### The concrete query model -/

variable {ι W : Type*} [Fintype ι] [DecidableEq ι] [Fintype W]

/-- **Phase oracle marking one item.** On `ℓ²(ι × W)`, the linear isometry that negates the
amplitude of every basis state `|z, w⟩` whose query register `z` equals `y` and fixes the
others (Bennett, Bernstein, Brassard and Vazirani, Section 3: inverting the phase of the
marked item). -/
noncomputable def markingOracle (y : ι) :
    EuclideanSpace ℂ (ι × W) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (ι × W) :=
  LinearIsometryEquiv.piLpCongrRight 2 fun zw =>
    if zw.1 = y then LinearIsometryEquiv.neg ℂ else LinearIsometryEquiv.refl ℂ ℂ

theorem markingOracle_apply (y : ι) (v : EuclideanSpace ℂ (ι × W)) (zw : ι × W) :
    markingOracle y v zw = if zw.1 = y then -v zw else v zw := by
  by_cases h : zw.1 = y <;> simp [markingOracle, h]

/-- **Query projection.** On `ℓ²(ι × W)`, the orthogonal projection onto the basis states whose
query register holds `y`: it keeps the amplitudes at `(y, w)` and zeroes the others. Its squared
norm `‖queryProj y v‖²` is the query magnitude of `y` in `v` (Bennett, Bernstein, Brassard and
Vazirani, Definition 3.2), and also the probability that measuring the query register of `v`
gives `y`. -/
noncomputable def queryProj (y : ι) : EuclideanSpace ℂ (ι × W) →ₗ[ℂ] EuclideanSpace ℂ (ι × W) :=
  (1 / 2 : ℂ) • (LinearMap.id - ((markingOracle (W := W) y).toLinearEquiv : _ →ₗ[ℂ] _))

theorem queryProj_apply (y : ι) (v : EuclideanSpace ℂ (ι × W)) (zw : ι × W) :
    queryProj y v zw = if zw.1 = y then v zw else 0 := by
  simp only [queryProj, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply]
  rw [PiLp.smul_apply, PiLp.sub_apply]
  simp only [LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv, markingOracle_apply]
  split_ifs <;> ring

theorem norm_markingOracle_sub_le (y : ι) (v : EuclideanSpace ℂ (ι × W)) :
    ‖markingOracle y v - v‖ ≤ 2 * ‖queryProj y v‖ := by
  have : markingOracle y v - v = (-2 : ℂ) • queryProj y v := by
    ext zw
    rw [PiLp.sub_apply, PiLp.smul_apply, queryProj_apply, markingOracle_apply]
    split_ifs <;> simp; ring
  rw [this, norm_smul]
  simp

/-- **Born rule for the query register.** `‖queryProj y v‖² = ∑_w |v (y, w)|²`, the probability
that measuring the query register of `v` gives `y`. -/
theorem norm_queryProj_sq (y : ι) (v : EuclideanSpace ℂ (ι × W)) :
    ‖queryProj y v‖ ^ 2 = ∑ w, ‖v (y, w)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  simp only [queryProj_apply]
  rw [sum_eq_single y]
  · simp
  · intro z _ hz
    simp [hz]
  · simp

theorem sum_norm_queryProj_sq (v : EuclideanSpace ℂ (ι × W)) :
    ∑ y, ‖queryProj y v‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  simp only [norm_queryProj_sq]

/-- **BBBV lower bound in the standard query model.** On `ℓ²(ι × W)` with `N = |ι|` items, let
an algorithm apply linear isometries `U 0, …, U T` with `T` calls to the phase oracle marking
`y` in between, starting from a unit vector `ψ₀`. If for every `y` measuring the query register
of the final state gives `y` with probability at least `1/2`, then `N ≤ 16 T² + 4`: search needs
`Ω(√N)` queries, the order attained by Grover's algorithm (Bennett, Bernstein, Brassard and
Vazirani, Section 3.1, the query lower bound behind Theorem 3.5). -/
theorem card_le_of_forall_success (U : ℕ → EuclideanSpace ℂ (ι × W) →ₗᵢ[ℂ]
    EuclideanSpace ℂ (ι × W)) (ψ₀ : EuclideanSpace ℂ (ι × W)) (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (hsucc : ∀ y, 1 / 2 ≤ ∑ w, ‖queryRun U (markingOracle y) ψ₀ T (y, w)‖ ^ 2) :
    (Fintype.card ι : ℝ) ≤ 16 * T ^ 2 + 4 := by
  have h := mul_card_le_of_forall_success U (fun y => (markingOracle (W := W) y).toLinearIsometry)
    (fun y => queryProj y) (fun y v => norm_markingOracle_sub_le y v)
    (fun v => (sum_norm_queryProj_sq v).le) (fun y => queryProj y)
    (fun v => (sum_norm_queryProj_sq v).le) ψ₀ hψ₀ T (1 / 2) (fun y => by
      rw [norm_queryProj_sq]
      exact hsucc y)
  linarith

end Cslib.QuantumSearchLowerBound
