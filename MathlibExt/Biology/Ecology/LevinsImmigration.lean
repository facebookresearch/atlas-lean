/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Ecology.LevinsMetapopulation
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The Levins model with immigration (mainland–island model)

The Levins patch-occupancy model of `MathlibExt.Biology.Ecology.LevinsMetapopulation` with an
external source of colonists: a mainland sends propagules at rate `m` per empty patch, so the
occupied fraction `p ∈ [0, 1]` follows

  `dp/dt = c p (1 - p) - e p + m (1 - p)`,

with colonization rate `c ≥ 0`, extinction rate `e ≥ 0` and immigration rate `m > 0`
(Gotelli 1991; Hanski 1999, §4.2). The right-hand side is `balance c e m p`, and
`IsSolution c e m p` says that `p` solves the equation on `[0, ∞)`. At `m = 0` this is the Levins
model (`balance_zero_right`, `isSolution_zero_right_iff`).

**Main point.** Without immigration and with `c ≤ e`, `e > 0`, every population goes extinct
(`LevinsMetapopulation.extinction_isGloballyStable`). With any `m > 0`, extinction is not even an
equilibrium (`balance c e m 0 = m`), and there is a unique equilibrium `p̂ ∈ (0, 1]` in `[0, ∞)`,
for every `c ≥ 0` and `e ≥ 0`, which attracts every solution with `p(0) ≥ 0` at exponential rate
`m / p̂`. Even a trickle of immigrants keeps the metapopulation from going extinct
(`propagule_rain_persistence`). The immigration term `m (1 - p)` is propagule rain, mainland
colonization of empty patches: it leaves the local extinction term `e p` unchanged, so this is
not the rescue effect, in which immigration lowers local extinction (Gotelli 1991 distinguishes
the two).

The balance is the concave quadratic `-c p² + b p + m` with `b = c - e - m`, so for `c > 0` its
positive root is `(b + √(b² + 4 c m)) / (2 c)` (`immigrationEq_eq_quadratic`). The rationalized
form `p̂ = 2 m / (√(b² + 4 c m) - b)` used as the definition (`immigrationEq`) also covers `c = 0`,
where `p̂ = m / (e + m)`.

## Main results

* `balance_immigrationEq`, `immigrationEq_pos`, `immigrationEq_le_one`: `p̂ ∈ (0, 1]` is an
  equilibrium; `immigrationEq_lt_one` (`e > 0`) and `immigrationEq_eq_one_iff`.
* `balance_eq_mul`: the factorization `f(p) = -(p - p̂) (c p + m / p̂)`.
* `balance_eq_zero_iff`, `existsUnique_equilibrium`: `p̂` is the only equilibrium in `[0, ∞)`.
* `hasDerivAt_balance_immigrationEq`: the linearization `f'(p̂) = -(c p̂ + m / p̂) < 0`.
* `tendsto_immigrationEq_zero`: as `m ↓ 0`, `p̂ → max (1 - e / c) 0`, the attractor of the
  Levins model (`c > 0`).
* `isSolution_solution`, `exists_isSolution`: an explicit solution from every `p₀ ≥ 0`.
* `IsSolution.nonneg`, `IsSolution.pos`, `IsSolution.mem_Icc`: `[0, ∞)` and `[0, 1]` are
  invariant, and an empty island is colonized at once (`p(t) > 0` for `t > 0`).
* `IsSolution.abs_sub_le_exp`: `|p(t) - p̂| ≤ |p(0) - p̂| e^{-(m / p̂) t}` for `p(0) ≥ 0`.
* `isGloballyStable`: `p̂` is Lyapunov stable and attracts every solution from `[0, ∞)`.
* `propagule_rain_persistence`: for `0 ≤ c ≤ e`, `e > 0`, extinction is globally stable at
  `m = 0`, while for every `m > 0` the positive equilibrium is.

## Implementation

The stability proofs do not use the explicit solution. Positivity is a barrier argument
(`image_le_of_deriv_right_lt_deriv_boundary`) using `f(0) = m > 0`. Writing `q = p - p̂` and
`L = c p̂ + m / p̂`, the equation is `q' = -L q - c q²`; then `q e^{L t}` is nonincreasing (upper
bound and invariance of `[0, 1]`), and `q² e^{2 (m / p̂) t}` is nonincreasing while `p ≥ 0`
(exponential decay). The explicit solution `p̂ + L q₀ / ((L + c q₀) e^{L t} - c q₀)` serves only
for existence. The stability notions `IsLyapunovStable`, `IsGloballyAttracting` and
`IsGloballyStable` abbreviate the shared notions of `MathlibExt.Dynamics.EquilibriumStability` for
the solutions `IsSolution c e m`, as the Levins model's notions do for its solutions.

## References

* N. J. Gotelli, *Metapopulation models: the rescue effect, the propagule rain, and the
  core-satellite hypothesis*, Am. Nat. 138 (1991) 768–776.
* I. Hanski, *Metapopulation Ecology*, Oxford University Press (1999), §4.2.
-/

@[expose] public section

open Real Filter Set
open scoped Topology

namespace MathlibExt.Biology.Ecology.LevinsImmigration

/-- The **colonization–extinction–immigration balance**: occupied patches colonize the empty
fraction `1 - p` at rate `c`, local populations go extinct at rate `e`, and the mainland colonizes
empty patches at rate `m`, `c p (1 - p) - e p + m (1 - p)`. -/
def balance (c e m p : ℝ) : ℝ := c * p * (1 - p) - e * p + m * (1 - p)

/-- `p` solves `p' = c p (1 - p) - e p + m (1 - p)` for all `t ≥ 0`. -/
structure IsSolution (c e m : ℝ) (p : ℝ → ℝ) : Prop where
  /-- The occupied fraction changes by colonization minus extinction plus immigration. -/
  hasDerivAt : ∀ t, 0 ≤ t → HasDerivAt p (balance c e m (p t)) t

/-- The discriminant `(c - e - m)² + 4 c m` of the quadratic `c p² - (c - e - m) p - m`. -/
noncomputable def disc (c e m : ℝ) : ℝ := (c - e - m) ^ 2 + 4 * c * m

/-- The **immigration equilibrium** `p̂ = 2 m / (e + m - c + √((c - e - m)² + 4 c m))`, the positive
root of the balance in rationalized form; for `c > 0` it equals the quadratic-formula root
(`immigrationEq_eq_quadratic`), and for `c = 0` it is `m / (e + m)`. This holds for `c ≥ 0`,
`e ≥ 0` and `m > 0`, the range of every result below, where the denominator is positive
(`denom_pos`); outside it the formula need not be a root of the balance (at `m = 0` it is `0`). -/
noncomputable def immigrationEq (c e m : ℝ) : ℝ := 2 * m / (e + m - c + √(disc c e m))

/-- The **return rate** `c p̂ + m / p̂ = -f'(p̂)` at the immigration equilibrium. -/
noncomputable def rate (c e m : ℝ) : ℝ := c * immigrationEq c e m + m / immigrationEq c e m

variable {c e m : ℝ}

/-! ### Relation to the Levins model -/

/-- Without immigration the balance is the Levins balance. -/
theorem balance_zero_right (c e p : ℝ) :
    balance c e 0 p = LevinsMetapopulation.balance c e p := by
  simp [balance, LevinsMetapopulation.balance]

/-- Without immigration the solutions are the Levins solutions. -/
theorem isSolution_zero_right_iff {p : ℝ → ℝ} :
    IsSolution c e 0 p ↔ LevinsMetapopulation.IsSolution c e p :=
  ⟨fun h => ⟨fun t ht => by rw [← balance_zero_right]; exact h.hasDerivAt t ht⟩,
    fun h => ⟨fun t ht => by rw [balance_zero_right]; exact h.hasDerivAt t ht⟩⟩

/-- **Extinction is not an equilibrium**: an empty landscape receives immigrants at rate `m`. -/
theorem balance_zero (c e m : ℝ) : balance c e m 0 = m := by simp [balance]

/-- A fully occupied landscape loses patches at rate `e`. -/
theorem balance_one (c e m : ℝ) : balance c e m 1 = -e := by simp [balance]

/-! ### The immigration equilibrium -/

theorem disc_nonneg (hc : 0 ≤ c) (hm : 0 ≤ m) : 0 ≤ disc c e m := by
  unfold disc
  have := mul_nonneg hc hm
  nlinarith [sq_nonneg (c - e - m)]

/-- The denominator of `immigrationEq` is positive. -/
theorem denom_pos (he : 0 ≤ e) (hm : 0 < m) :
    0 < e + m - c + √(disc c e m) := by
  rcases lt_or_ge (c - e - m) 0 with h | h
  · have := Real.sqrt_nonneg (disc c e m)
    linarith
  · have hc' : 0 < c := by linarith
    have hlt : (c - e - m) ^ 2 < disc c e m := by
      unfold disc
      nlinarith [mul_pos hc' hm]
    have := Real.sqrt_lt_sqrt (sq_nonneg _) hlt
    rw [Real.sqrt_sq h] at this
    linarith

theorem immigrationEq_pos (he : 0 ≤ e) (hm : 0 < m) : 0 < immigrationEq c e m :=
  div_pos (by linarith) (denom_pos (c := c) he hm)

/-- **`p̂` is an equilibrium**: `f(p̂) = 0`. -/
theorem balance_immigrationEq (hc : 0 ≤ c) (he : 0 ≤ e) (hm : 0 < m) :
    balance c e m (immigrationEq c e m) = 0 := by
  have hd := denom_pos (c := c) he hm
  have hs : √(disc c e m) ^ 2 = (c - e - m) ^ 2 + 4 * c * m :=
    Real.sq_sqrt (disc_nonneg hc hm.le)
  obtain ⟨d, hd_def⟩ : ∃ d, d = e + m - c + √(disc c e m) := ⟨_, rfl⟩
  rw [← hd_def] at hd
  have hd0 : d ≠ 0 := hd.ne'
  have key : balance c e m (2 * m / d) =
      m * (d ^ 2 + 2 * (c - e - m) * d - 4 * c * m) / d ^ 2 := by
    unfold balance
    field_simp
    ring
  have hz : d ^ 2 + 2 * (c - e - m) * d - 4 * c * m = 0 := by
    rw [hd_def]
    linear_combination hs
  rw [immigrationEq, ← hd_def, key, hz, mul_zero, zero_div]

/-! ### Factorization from any positive equilibrium -/

/-- If `q > 0` is an equilibrium, `m / q = c q - c + e + m`. -/
theorem div_eq_of_balance_eq_zero {q : ℝ} (hq : 0 < q) (h0 : balance c e m q = 0) :
    m / q = c * q - c + e + m := by
  rw [div_eq_iff hq.ne']
  unfold balance at h0
  linear_combination h0

/-- If `q > 0` is an equilibrium, `f(p) = -(p - q) (c p + m / q)`. -/
theorem balance_eq_mul_of_eq {q : ℝ} (hq : 0 < q) (h0 : balance c e m q = 0) (p : ℝ) :
    balance c e m p = -(p - q) * (c * p + m / q) := by
  rw [div_eq_of_balance_eq_zero hq h0]
  unfold balance at h0 ⊢
  linear_combination h0

/-- **Factorization**: `f(p) = -(p - p̂) (c p + m / p̂)`. -/
theorem balance_eq_mul (hc : 0 ≤ c) (he : 0 ≤ e) (hm : 0 < m) (p : ℝ) :
    balance c e m p = -(p - immigrationEq c e m) * (c * p + m / immigrationEq c e m) :=
  balance_eq_mul_of_eq (immigrationEq_pos (c := c) he hm) (balance_immigrationEq hc he hm) p

/-- `(1 - p̂) (c + m / p̂) = e`, from `f(1) = -e`. -/
theorem one_sub_immigrationEq_mul (hc : 0 ≤ c) (he : 0 ≤ e) (hm : 0 < m) :
    (1 - immigrationEq c e m) * (c + m / immigrationEq c e m) = e := by
  have h := balance_eq_mul hc he hm 1
  rw [balance_one] at h
  linear_combination h

theorem immigrationEq_le_one (hc : 0 ≤ c) (he : 0 ≤ e) (hm : 0 < m) :
    immigrationEq c e m ≤ 1 := by
  have hk : 0 < c + m / immigrationEq c e m :=
    add_pos_of_nonneg_of_pos hc (div_pos hm (immigrationEq_pos (c := c) he hm))
  have h := one_sub_immigrationEq_mul hc he hm
  by_contra hlt
  have : (1 - immigrationEq c e m) * (c + m / immigrationEq c e m) < 0 :=
    mul_neg_of_neg_of_pos (by linarith [not_le.1 hlt]) hk
  linarith

/-- With local extinction (`e > 0`), the landscape is never fully occupied at equilibrium. -/
theorem immigrationEq_lt_one (hc : 0 ≤ c) (he : 0 < e) (hm : 0 < m) :
    immigrationEq c e m < 1 := by
  have h := one_sub_immigrationEq_mul hc he.le hm
  by_contra hlt
  have : (1 - immigrationEq c e m) * (c + m / immigrationEq c e m) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith [not_lt.1 hlt])
      (add_nonneg hc (div_pos hm (immigrationEq_pos (c := c) he.le hm)).le)
  linarith

theorem immigrationEq_eq_one_iff (hc : 0 ≤ c) (he : 0 ≤ e) (hm : 0 < m) :
    immigrationEq c e m = 1 ↔ e = 0 := by
  have h := one_sub_immigrationEq_mul hc he hm
  constructor
  · intro h1
    rw [h1, sub_self, zero_mul] at h
    exact h.symm
  · intro he0
    have hk : 0 < c + m / immigrationEq c e m :=
      add_pos_of_nonneg_of_pos hc (div_pos hm (immigrationEq_pos (c := c) he hm))
    have h' : (1 - immigrationEq c e m) * (c + m / immigrationEq c e m) = 0 := by
      rw [h, he0]
    rcases mul_eq_zero.1 h' with h' | h'
    · linarith
    · linarith

/-- **Persistence with immigration**: `p̂ ∈ (0, 1]` for every `c ≥ 0`, `e ≥ 0`, `m > 0`, including
`c ≤ e` with `e > 0`, where the Levins model without immigration goes extinct. -/
theorem immigrationEq_mem_Ioc (hc : 0 ≤ c) (he : 0 ≤ e) (hm : 0 < m) :
    immigrationEq c e m ∈ Ioc 0 1 :=
  ⟨immigrationEq_pos (c := c) he hm, immigrationEq_le_one hc he hm⟩

/-- **The equilibrium in `[0, ∞)`**: for `p ≥ 0`, `f(p) = 0 ↔ p = p̂`. -/
theorem balance_eq_zero_iff (hc : 0 ≤ c) (he : 0 ≤ e) (hm : 0 < m) {p : ℝ} (hp : 0 ≤ p) :
    balance c e m p = 0 ↔ p = immigrationEq c e m := by
  have hk : 0 < c * p + m / immigrationEq c e m :=
    add_pos_of_nonneg_of_pos (mul_nonneg hc hp) (div_pos hm (immigrationEq_pos (c := c) he hm))
  rw [balance_eq_mul hc he hm]
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h | h
    · linarith
    · linarith
  · rintro rfl
    ring

/-- **Existence and uniqueness of the positive equilibrium.** -/
theorem existsUnique_equilibrium (hc : 0 ≤ c) (he : 0 ≤ e) (hm : 0 < m) :
    ∃! p, 0 ≤ p ∧ balance c e m p = 0 :=
  ⟨immigrationEq c e m, ⟨(immigrationEq_pos (c := c) he hm).le, balance_immigrationEq hc he hm⟩,
    fun _ hp => (balance_eq_zero_iff hc he hm hp.1).1 hp.2⟩

/-- For `c > 0`, `p̂` is the quadratic-formula root `(c - e - m + √disc) / (2 c)`. -/
theorem immigrationEq_eq_quadratic (hc : 0 < c) (he : 0 ≤ e) (hm : 0 < m) :
    immigrationEq c e m = (c - e - m + √(disc c e m)) / (2 * c) := by
  have hd := denom_pos (c := c) he hm
  have hs : √(disc c e m) ^ 2 = (c - e - m) ^ 2 + 4 * c * m :=
    Real.sq_sqrt (disc_nonneg hc.le hm.le)
  rw [immigrationEq, div_eq_div_iff hd.ne' (mul_pos two_pos hc).ne']
  linear_combination -hs

/-- **Vanishing immigration recovers the Levins attractor.** For `c > 0`, as `m ↓ 0` the
immigration equilibrium tends to `max (1 - e / c) 0`: the persistence equilibrium when `c > e` and
extinction when `c ≤ e`. -/
theorem tendsto_immigrationEq_zero (hc : 0 < c) (he : 0 ≤ e) :
    Tendsto (fun m => immigrationEq c e m) (𝓝[>] 0)
      (𝓝 (max (LevinsMetapopulation.persistenceEq c e) 0)) := by
  have hcont : Continuous fun m : ℝ => (c - e - m + √(disc c e m)) / (2 * c) := by
    unfold disc
    fun_prop
  have hlim : Tendsto (fun m : ℝ => (c - e - m + √(disc c e m)) / (2 * c)) (𝓝 0)
      (𝓝 ((c - e - 0 + √(disc c e 0)) / (2 * c))) := hcont.tendsto 0
  have hval : (c - e - 0 + √(disc c e 0)) / (2 * c) =
      max (LevinsMetapopulation.persistenceEq c e) 0 := by
    have hd : disc c e 0 = (c - e) ^ 2 := by unfold disc; ring
    rw [hd, Real.sqrt_sq_eq_abs, LevinsMetapopulation.persistenceEq]
    rcases le_total e c with h | h
    · rw [abs_of_nonneg (by linarith), max_eq_left]
      · field_simp
        ring
      · rw [sub_nonneg, div_le_one hc]
        exact h
    · rw [abs_of_nonpos (by linarith), max_eq_right]
      · ring
      · rw [sub_nonpos, le_div_iff₀ hc]
        linarith
  rw [hval] at hlim
  refine (tendsto_nhdsWithin_of_tendsto_nhds hlim).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with m hm
  exact (immigrationEq_eq_quadratic hc he hm).symm

/-! ### Linearization -/

/-- The derivative of the balance in `p`: `c - e - m - 2 c p`. -/
theorem hasDerivAt_balance (c e m p : ℝ) :
    HasDerivAt (balance c e m) (c - e - m - 2 * c * p) p := by
  have h : HasDerivAt (fun q => c * q * (1 - q) - e * q + m * (1 - q))
      (c * 1 * (1 - p) + c * p * (0 - 1) - e * 1 + m * (0 - 1)) p :=
    ((((hasDerivAt_id p).const_mul c).mul ((hasDerivAt_const p 1).sub (hasDerivAt_id p))).sub
      ((hasDerivAt_id p).const_mul e)).add
      (((hasDerivAt_const p 1).sub (hasDerivAt_id p)).const_mul m)
  exact h.congr_deriv (by ring)

theorem rate_pos (hc : 0 ≤ c) (he : 0 ≤ e) (hm : 0 < m) : 0 < rate c e m :=
  add_pos_of_nonneg_of_pos (mul_nonneg hc (immigrationEq_pos (c := c) he hm).le)
    (div_pos hm (immigrationEq_pos (c := c) he hm))

/-- **Linear stability**: `f'(p̂) = -(c p̂ + m / p̂) < 0`. -/
theorem hasDerivAt_balance_immigrationEq (hc : 0 ≤ c) (he : 0 ≤ e) (hm : 0 < m) :
    HasDerivAt (balance c e m) (-rate c e m) (immigrationEq c e m) := by
  refine (hasDerivAt_balance c e m _).congr_deriv ?_
  rw [rate, div_eq_of_balance_eq_zero (immigrationEq_pos (c := c) he hm)
    (balance_immigrationEq hc he hm)]
  ring

/-! ### An explicit solution -/

/-- The trajectory `q + L (p₀ - q) / ((L + c (p₀ - q)) e^{L t} - c (p₀ - q))` of `q' = -L q - c q²`
shifted by `q`. -/
noncomputable def riccatiTraj (c q L p₀ t : ℝ) : ℝ :=
  q + L * (p₀ - q) / ((L + c * (p₀ - q)) * exp (L * t) - c * (p₀ - q))

/-- The **explicit solution** with `p(0) = p₀`. -/
noncomputable def solution (c e m p₀ : ℝ) : ℝ → ℝ :=
  riccatiTraj c (immigrationEq c e m) (rate c e m) p₀

theorem riccatiTraj_zero {q L : ℝ} (hL : L ≠ 0) (p₀ : ℝ) : riccatiTraj c q L p₀ 0 = p₀ := by
  rw [riccatiTraj, mul_zero, exp_zero, mul_one, add_sub_cancel_right,
    mul_div_cancel_left₀ _ hL]
  ring

theorem solution_zero (hc : 0 ≤ c) (he : 0 ≤ e) (hm : 0 < m) (p₀ : ℝ) :
    solution c e m p₀ 0 = p₀ :=
  riccatiTraj_zero (rate_pos hc he hm).ne' p₀

/-- **The explicit solution solves the equation** (`c, e ≥ 0`, `m > 0`, `p₀ ≥ 0`). -/
theorem isSolution_solution (hc : 0 ≤ c) (he : 0 ≤ e) (hm : 0 < m) {p₀ : ℝ} (hp₀ : 0 ≤ p₀) :
    IsSolution c e m (solution c e m p₀) := by
  obtain ⟨q, hqdef⟩ : ∃ q, q = immigrationEq c e m := ⟨_, rfl⟩
  have hq : 0 < q := by rw [hqdef]; exact immigrationEq_pos (c := c) he hm
  have h0 : balance c e m q = 0 := by rw [hqdef]; exact balance_immigrationEq hc he hm
  obtain ⟨L, hL⟩ : ∃ L, L = c * q + m / q := ⟨_, rfl⟩
  have hsol : solution c e m p₀ = riccatiTraj c q L p₀ := by
    rw [hL, hqdef]
    rfl
  rw [hsol]
  refine ⟨fun t ht => ?_⟩
  have hmq : 0 < m / q := div_pos hm hq
  have hLpos : 0 < L := by rw [hL]; nlinarith [mul_nonneg hc hq.le]
  have hLa : 0 < L + c * (p₀ - q) := by
    rw [hL]
    nlinarith [mul_nonneg hc hp₀]
  have hE1 : 1 ≤ exp (L * t) := one_le_exp_iff.2 (mul_nonneg hLpos.le ht)
  have hden : 0 < (L + c * (p₀ - q)) * exp (L * t) - c * (p₀ - q) := by
    nlinarith [mul_nonneg hLa.le (sub_nonneg.2 hE1)]
  have hD0 := hden.ne'
  have hE : HasDerivAt (fun s => exp (L * s)) (exp (L * t) * (L * 1)) t :=
    ((hasDerivAt_id' t).const_mul L).exp
  have hD : HasDerivAt (fun s => (L + c * (p₀ - q)) * exp (L * s) - c * (p₀ - q))
      ((L + c * (p₀ - q)) * (exp (L * t) * (L * 1))) t :=
    (hE.const_mul _).sub_const _
  have h := ((hasDerivAt_const t (L * (p₀ - q))).div hD hD0).const_add q
  refine h.congr_deriv ?_
  have hmL : m / q = L - c * q := by rw [hL]; ring
  rw [balance_eq_mul_of_eq hq h0, hmL, riccatiTraj]
  field_simp
  ring

/-- **Global existence** from every `p₀ ≥ 0`. -/
theorem exists_isSolution (hc : 0 ≤ c) (he : 0 ≤ e) (hm : 0 < m) {p₀ : ℝ} (hp₀ : 0 ≤ p₀) :
    ∃ p : ℝ → ℝ, IsSolution c e m p ∧ p 0 = p₀ :=
  ⟨solution c e m p₀, isSolution_solution hc he hm hp₀, solution_zero hc he hm p₀⟩

/-! ### Invariance and positivity -/

/-- A function with nonpositive derivative on `[0, ∞)` does not exceed its value at `0`. -/
private theorem le_zero_of_hasDerivAt_nonpos {g g' : ℝ → ℝ}
    (hg : ∀ t, 0 ≤ t → HasDerivAt g (g' t) t) (hg' : ∀ t, 0 ≤ t → g' t ≤ 0) {t : ℝ}
    (ht : 0 ≤ t) : g t ≤ g 0 := by
  have hanti : AntitoneOn g (Ici 0) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (fun s hs => (hg s hs).continuousAt.continuousWithinAt)
      (fun s hs => by
        rw [interior_Ici] at hs
        exact (hg s (le_of_lt hs)).hasDerivWithinAt)
      (fun s hs => by
        rw [interior_Ici] at hs
        exact hg' s (le_of_lt hs))
  exact hanti (mem_Ici.2 le_rfl) (mem_Ici.2 ht) ht

namespace IsSolution

variable {p : ℝ → ℝ}

/-- **The occupied fraction stays nonnegative** (barrier argument at `p = 0`, where
`f(0) = m > 0`). -/
theorem nonneg (hp : IsSolution c e m p) (hm : 0 < m) (h0 : 0 ≤ p 0) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ p t := by
  have key := image_le_of_deriv_right_lt_deriv_boundary (f := fun s => -p s)
    (f' := fun s => -balance c e m (p s)) (a := 0) (b := t) (B := fun _ => 0) (B' := fun _ => 0)
    (fun s hs => (hp.hasDerivAt s hs.1).continuousAt.neg.continuousWithinAt)
    (fun s hs => (hp.hasDerivAt s hs.1).neg.hasDerivWithinAt)
    (by simpa using h0) (fun _ => hasDerivAt_const _ _)
    (fun s _ hs => by
      have hs' : p s = 0 := by simpa using hs
      change -balance c e m (p s) < 0
      rw [hs', balance_zero]
      linarith)
    (show t ∈ Icc 0 t from ⟨ht, le_rfl⟩)
  simpa using key

/-- **An empty island is colonized at once**: `p(t) > 0` for every `t > 0`, even when
`p(0) = 0`. -/
theorem pos (hp : IsSolution c e m p) (hm : 0 < m) (h0 : 0 ≤ p 0) {t : ℝ} (ht : 0 < t) :
    0 < p t := by
  refine (hp.nonneg hm h0 ht.le).lt_of_ne fun hpt => ?_
  have hmin : IsLocalMin p t := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    rw [← hpt]
    exact hp.nonneg hm h0 (le_of_lt hs)
  have := hmin.hasDerivAt_eq_zero (hp.hasDerivAt t ht.le)
  rw [← hpt, balance_zero] at this
  exact hm.ne' this

/-- The deviation from a positive equilibrium `q`, weighted by `e^{L t}` with
`L = c q + m / q`, is nonincreasing. -/
theorem sub_le_mul_exp_of_eq (hp : IsSolution c e m p) (hc : 0 ≤ c) {q : ℝ} (hq : 0 < q)
    (h0 : balance c e m q = 0) {t : ℝ} (ht : 0 ≤ t) :
    p t - q ≤ (p 0 - q) * exp (-((c * q + m / q) * t)) := by
  obtain ⟨L, hL⟩ : ∃ L, L = c * q + m / q := ⟨_, rfl⟩
  rw [← hL]
  have hW : (p t - q) * exp (L * t) ≤ (p 0 - q) * exp (L * 0) :=
    le_zero_of_hasDerivAt_nonpos (g := fun s => (p s - q) * exp (L * s))
      (g' := fun s => -(c * (p s - q) ^ 2 * exp (L * s)))
      (fun s hs => by
        have h := ((hp.hasDerivAt s hs).sub_const q).mul ((hasDerivAt_id' s).const_mul L).exp
        refine h.congr_deriv ?_
        rw [balance_eq_mul_of_eq hq h0, hL]
        ring)
      (fun s _ => neg_nonpos.2 (mul_nonneg (mul_nonneg hc (sq_nonneg _)) (exp_pos _).le)) ht
  rw [mul_zero, exp_zero, mul_one] at hW
  have hE : exp (L * t) * exp (-(L * t)) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
  calc p t - q = (p t - q) * exp (L * t) * exp (-(L * t)) := by rw [mul_assoc, hE, mul_one]
    _ ≤ (p 0 - q) * exp (-(L * t)) := mul_le_mul_of_nonneg_right hW (exp_pos _).le

/-- **Upper bound**: `p(t) - p̂ ≤ (p(0) - p̂) e^{-L t}` with `L = c p̂ + m / p̂`. -/
theorem sub_le_mul_exp (hp : IsSolution c e m p) (hc : 0 ≤ c) (he : 0 ≤ e) (hm : 0 < m)
    {t : ℝ} (ht : 0 ≤ t) :
    p t - immigrationEq c e m ≤ (p 0 - immigrationEq c e m) * exp (-(rate c e m * t)) :=
  hp.sub_le_mul_exp_of_eq hc (immigrationEq_pos (c := c) he hm) (balance_immigrationEq hc he hm) ht

/-- The occupied fraction never exceeds `max (p(0)) p̂`. -/
theorem le_max (hp : IsSolution c e m p) (hc : 0 ≤ c) (he : 0 ≤ e) (hm : 0 < m) {t : ℝ}
    (ht : 0 ≤ t) : p t ≤ max (p 0) (immigrationEq c e m) := by
  have h := hp.sub_le_mul_exp hc he hm ht
  have hE : exp (-(rate c e m * t)) ≤ 1 :=
    exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg (rate_pos hc he hm).le ht))
  have hE0 := exp_pos (-(rate c e m * t))
  rcases le_total (immigrationEq c e m) (p 0) with h' | h'
  · have : (p 0 - immigrationEq c e m) * exp (-(rate c e m * t)) ≤ p 0 - immigrationEq c e m :=
      mul_le_of_le_one_right (by linarith) hE
    linarith [le_max_left (p 0) (immigrationEq c e m)]
  · have : (p 0 - immigrationEq c e m) * exp (-(rate c e m * t)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hE0.le
    linarith [le_max_right (p 0) (immigrationEq c e m)]

/-- **Invariance of `[0, 1]`** (`c, e ≥ 0`, `m > 0`). -/
theorem mem_Icc (hp : IsSolution c e m p) (hc : 0 ≤ c) (he : 0 ≤ e) (hm : 0 < m)
    (h0 : p 0 ∈ Icc 0 1) {t : ℝ} (ht : 0 ≤ t) : p t ∈ Icc 0 1 :=
  ⟨hp.nonneg hm h0.1 ht,
    (hp.le_max hc he hm ht).trans (max_le h0.2 (immigrationEq_le_one hc he hm))⟩

/-! ### Exponential stability -/

/-- Exponential decay towards a positive equilibrium `q`, at rate `m / q`, for `p(0) ≥ 0`. -/
theorem abs_sub_le_exp_of_eq (hp : IsSolution c e m p) (hc : 0 ≤ c) (hm : 0 < m) {q : ℝ}
    (hq : 0 < q) (h0 : balance c e m q = 0) (hp0 : 0 ≤ p 0) {t : ℝ} (ht : 0 ≤ t) :
    |p t - q| ≤ |p 0 - q| * exp (-(m / q * t)) := by
  have hV : (p t - q) * (p t - q) * exp (2 * (m / q) * t) ≤
      (p 0 - q) * (p 0 - q) * exp (2 * (m / q) * 0) :=
    le_zero_of_hasDerivAt_nonpos (g := fun s => (p s - q) * (p s - q) * exp (2 * (m / q) * s))
      (g' := fun s => -(2 * c * p s * ((p s - q) * (p s - q)) * exp (2 * (m / q) * s)))
      (fun s hs => by
        have hd := (hp.hasDerivAt s hs).sub_const q
        have h : HasDerivAt (fun y => (p y - q) * (p y - q) * exp (2 * (m / q) * y))
            ((balance c e m (p s) * (p s - q) + (p s - q) * balance c e m (p s)) *
              exp (2 * (m / q) * s) +
              (p s - q) * (p s - q) * (exp (2 * (m / q) * s) * (2 * (m / q) * 1))) s :=
          (hd.mul hd).mul ((hasDerivAt_id' s).const_mul (2 * (m / q))).exp
        refine h.congr_deriv ?_
        rw [balance_eq_mul_of_eq hq h0]
        ring)
      (fun s hs => neg_nonpos.2 (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hc)
        (hp.nonneg hm hp0 hs)) (mul_self_nonneg _)) (exp_pos _).le)) ht
  rw [mul_zero, exp_zero, mul_one] at hV
  have h1 : exp (-(m / q * t)) ^ 2 * exp (2 * (m / q) * t) = 1 := by
    rw [sq, ← exp_add, ← exp_add,
      show -(m / q * t) + -(m / q * t) + 2 * (m / q) * t = 0 by ring, exp_zero]
  have key : (p t - q) ^ 2 ≤ ((p 0 - q) * exp (-(m / q * t))) ^ 2 :=
    calc (p t - q) ^ 2
        = (p t - q) ^ 2 * (exp (-(m / q * t)) ^ 2 * exp (2 * (m / q) * t)) := by
          rw [h1, mul_one]
      _ = (p t - q) * (p t - q) * exp (2 * (m / q) * t) * exp (-(m / q * t)) ^ 2 := by ring
      _ ≤ (p 0 - q) * (p 0 - q) * exp (-(m / q * t)) ^ 2 :=
          mul_le_mul_of_nonneg_right hV (sq_nonneg _)
      _ = ((p 0 - q) * exp (-(m / q * t))) ^ 2 := by ring
  have := sq_le_sq.1 key
  rwa [abs_mul, abs_of_pos (exp_pos _)] at this

/-- **Exponential stability**: `|p(t) - p̂| ≤ |p(0) - p̂| e^{-(m / p̂) t}` for every solution with
`p(0) ≥ 0`. Since `p̂ ≤ 1`, the rate `m / p̂` is at least `m`. -/
theorem abs_sub_le_exp (hp : IsSolution c e m p) (hc : 0 ≤ c) (he : 0 ≤ e) (hm : 0 < m)
    (hp0 : 0 ≤ p 0) {t : ℝ} (ht : 0 ≤ t) :
    |p t - immigrationEq c e m| ≤
      |p 0 - immigrationEq c e m| * exp (-(m / immigrationEq c e m * t)) :=
  hp.abs_sub_le_exp_of_eq hc hm (immigrationEq_pos (c := c) he hm) (balance_immigrationEq hc he hm)
    hp0 ht

/-- **Convergence**: every solution with `p(0) ≥ 0` tends to `p̂`. -/
theorem tendsto_immigrationEq (hp : IsSolution c e m p) (hc : 0 ≤ c) (he : 0 ≤ e) (hm : 0 < m)
    (hp0 : 0 ≤ p 0) : Tendsto p atTop (𝓝 (immigrationEq c e m)) := by
  have hμ : 0 < m / immigrationEq c e m := div_pos hm (immigrationEq_pos (c := c) he hm)
  have hg : Tendsto (fun t => |p 0 - immigrationEq c e m| *
      exp (-(m / immigrationEq c e m * t))) atTop (𝓝 0) := by
    have := (tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hμ)).const_mul |p 0 - immigrationEq c e m|
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hg
  filter_upwards [eventually_ge_atTop 0] with t ht
  rw [Real.norm_eq_abs]
  exact hp.abs_sub_le_exp hc he hm hp0 ht

end IsSolution

/-! ### Global stability -/

/-- `a` is **Lyapunov stable** for solutions starting in `D`. -/
abbrev IsLyapunovStable (c e m a : ℝ) (D : Set ℝ) : Prop :=
  MathlibExt.Dynamics.EquilibriumStability.IsLyapunovStable (IsSolution c e m) a D

/-- `a` **attracts** every solution starting in `D`. -/
abbrev IsGloballyAttracting (c e m a : ℝ) (D : Set ℝ) : Prop :=
  MathlibExt.Dynamics.EquilibriumStability.IsGloballyAttracting (IsSolution c e m) a D

/-- `a` is **globally (asymptotically) stable** on `D`. -/
abbrev IsGloballyStable (c e m a : ℝ) (D : Set ℝ) : Prop :=
  MathlibExt.Dynamics.EquilibriumStability.IsGloballyStable (IsSolution c e m) a D

/-- **Global stability of the immigration equilibrium.** For `c, e ≥ 0` and `m > 0`, `p̂ ∈ (0, 1]`
is Lyapunov stable and attracts every solution with `p(0) ≥ 0`. -/
theorem isGloballyStable (hc : 0 ≤ c) (he : 0 ≤ e) (hm : 0 < m) :
    IsGloballyStable c e m (immigrationEq c e m) (Ici 0) := by
  refine ⟨fun ε hε => ⟨ε, hε, fun p hp hp0 hδ t ht => ?_⟩,
    fun p hp hp0 => hp.tendsto_immigrationEq hc he hm hp0⟩
  have h := hp.abs_sub_le_exp hc he hm hp0 ht
  have hE : exp (-(m / immigrationEq c e m * t)) ≤ 1 :=
    exp_le_one_iff.2 (neg_nonpos.2
      (mul_nonneg (div_pos hm (immigrationEq_pos (c := c) he hm)).le ht))
  calc |p t - immigrationEq c e m|
      ≤ |p 0 - immigrationEq c e m| * exp (-(m / immigrationEq c e m * t)) := h
    _ ≤ |p 0 - immigrationEq c e m| := mul_le_of_le_one_right (abs_nonneg _) hE
    _ < ε := hδ

/-- **Persistence under propagule rain.** Below the Levins threshold (`0 ≤ c ≤ e`, `e > 0`),
extinction is globally stable without immigration, while for every `m > 0` the equilibrium
`p̂ > 0` is globally stable: every solution with `p(0) ≥ 0` persists at `p̂`. Immigration only
colonizes empty patches and leaves the extinction rate `e` unchanged, so this is not the rescue
effect. -/
theorem propagule_rain_persistence (hc : 0 ≤ c) (he : 0 < e) (hce : c ≤ e) (hm : 0 < m) :
    LevinsMetapopulation.IsGloballyStable c e 0 (Icc 0 1) ∧
      0 < immigrationEq c e m ∧ IsGloballyStable c e m (immigrationEq c e m) (Ici 0) :=
  ⟨LevinsMetapopulation.extinction_isGloballyStable hc he hce, immigrationEq_pos (c := c) he.le hm,
    isGloballyStable hc he.le hm⟩

end MathlibExt.Biology.Ecology.LevinsImmigration
