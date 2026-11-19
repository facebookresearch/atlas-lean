/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Epidemiology.SIS
public import MathlibExt.Dynamics.EquilibriumStability

/-!
# The Levins metapopulation (patch-occupancy) model

A landscape consists of many identical habitat patches. Write `p(t)` for the fraction of patches
occupied at time `t`. Occupied patches send out colonists at rate `c` per patch, and a colonist
founds a population only on an empty patch (a fraction `1 - p`); each local population goes
extinct at rate `e`. The **colonization–extinction balance** (Levins 1969) is

  `dp/dt = c p (1 - p) - e p`,

with colonization rate `c ≥ 0`, extinction rate `e ≥ 0`, and state space `p ∈ [0, 1]`.
The right-hand side is `balance c e p`, and `IsSolution c e p` says that `p` solves the equation
on `[0, ∞)`.

For `c ≠ 0` the balance factors as `c p (p* - p)` with the **persistence equilibrium**
`p* = 1 - e / c`, so the equilibria are `p = 0` (extinction) and `p = p*`. For `c > 0` and
`e ≥ 0`, `p*` is an occupied state (`p* ∈ (0, 1]`) exactly when `c > e`: this is the
**persistence threshold**. The linearizations are `f'(0) = c - e` and, for `c ≠ 0`,
`f'(p*) = e - c`.

At `c = 0` the balance is `-e p`: `p = 0` is the only equilibrium when `e ≠ 0`, and every state
is one when `e = 0`. The formula `1 - e / c` means nothing there; Lean's division gives
`persistenceEq 0 e = 1`, which is not an equilibrium unless `e = 0`. Every result below about
`p*` has a hypothesis forcing `c ≠ 0`.

## Main results

* `balance_eq_mul`, `balance_eq_zero_iff`: the factorization and the two equilibria (`c ≠ 0`).
* `persistenceEq_mem_Ioc_iff`: the threshold, `p* ∈ (0, 1] ↔ e < c`.
* `hasDerivAt_balance_zero`, `hasDerivAt_balance_persistenceEq`: the linearizations (the second
  for `c ≠ 0`).
* `levins`, `isSolution_levins`, `exists_isSolution`: the explicit solution and global
  existence with `[0, 1]` invariant.
* `IsSolution.eq_of_initial`, `IsSolution.eq_levins`: forward uniqueness; every solution is the
  explicit one.
* `extinction_isGloballyStable`: if `c ≤ e` (and `e > 0`; `e > 0` is needed: for `c = e = 0`
  every state is an equilibrium, so `0` attracts nothing else), `p = 0` is Lyapunov stable and
  attracts every solution starting in `[0, 1]`; the trajectory never exceeds `p(0)`.
* `persistence_isGloballyStable`: if `0 ≤ e < c`, `p*` is Lyapunov stable and attracts every
  solution starting in `(0, 1]`; `|p(t) - p*|` is nonincreasing and decays like `e^{-(c - e) t}`
  (`abs_levins_sub_le`, `abs_levins_sub_le_exp`).
* `not_isLyapunovStable_zero`: if `0 ≤ e < c`, extinction is unstable.
* `tendsto_zero_iff_le`: for `c, e > 0`, every solution from `[0, 1]` goes extinct iff `c ≤ e`.

## Implementation

With `S = 1 - p` the pair `(S, p)` solves the closed-population SIS model of
`MathlibExt.Biology.Epidemiology.SIS` with `β = c`, `γ = e` and `N = 1` (`IsSolution.toSIS`).
The explicit solution, uniqueness and the two limits are taken from that file; the Lyapunov
stability bounds are proved here from the explicit formula. For `0 ≤ e < c` the explicit
solution is the logistic curve with rate `c - e` and carrying capacity `p*`
(`levins_eq_logistic`). The stability notions `IsLyapunovStable`, `IsGloballyAttracting` and
`IsGloballyStable` abbreviate the shared notions of `MathlibExt.Dynamics.EquilibriumStability` for
the Levins solutions `IsSolution c e`.

## References

* R. Levins, *Some demographic and genetic consequences of environmental heterogeneity for
  biological control*, Bull. Entomol. Soc. Am. 15 (1969) 237–240.
* I. Hanski, *Metapopulation Ecology*, Oxford University Press (1999), §4.1.
-/

@[expose] public section

open Real Filter Set
open scoped Topology

namespace MathlibExt.Biology.Ecology.LevinsMetapopulation

open MathlibExt.Biology.Epidemiology

/-- The **colonization–extinction balance** of the Levins model: occupied patches colonize the
empty fraction `1 - p` at rate `c`, and local populations go extinct at rate `e`,
`c p (1 - p) - e p`. -/
def balance (c e p : ℝ) : ℝ := c * p * (1 - p) - e * p

/-- `p` solves the Levins equation `p' = c p (1 - p) - e p` for all `t ≥ 0`. -/
structure IsSolution (c e : ℝ) (p : ℝ → ℝ) : Prop where
  /-- The occupied fraction changes by colonization minus extinction. -/
  hasDerivAt : ∀ t, 0 ≤ t → HasDerivAt p (balance c e (p t)) t

/-- The **persistence equilibrium** `p* = 1 - e / c`: for `c ≠ 0`, the equilibrium besides
`p = 0` (`balance_eq_zero_iff`). At `c = 0` it is not an equilibrium unless `e = 0`: Lean's
division gives `persistenceEq 0 e = 1`, while `balance 0 e 1 = -e`. -/
noncomputable def persistenceEq (c e : ℝ) : ℝ := 1 - e / c

variable {c e : ℝ}

/-! ### Equilibria and the persistence threshold -/

/-- The balance factors as `c p (p* - p)` (for `c ≠ 0`). -/
theorem balance_eq_mul (hc : c ≠ 0) (p : ℝ) :
    balance c e p = c * p * (persistenceEq c e - p) := by
  unfold balance persistenceEq
  field_simp
  ring

/-- **The equilibria.** For `c ≠ 0` the balance vanishes exactly at the extinction equilibrium
`p = 0` and the persistence equilibrium `p = p*`. -/
theorem balance_eq_zero_iff (hc : c ≠ 0) {p : ℝ} :
    balance c e p = 0 ↔ p = 0 ∨ p = persistenceEq c e := by
  rw [balance_eq_mul hc, mul_eq_zero, mul_eq_zero, sub_eq_zero]
  tauto

/-- `p* > 0` iff `e < c` (for `c > 0`). -/
theorem persistenceEq_pos_iff (hc : 0 < c) : 0 < persistenceEq c e ↔ e < c := by
  rw [persistenceEq, sub_pos, div_lt_one hc]

/-- `p* ≤ 1` for `c > 0`, `e ≥ 0`. -/
theorem persistenceEq_le_one (hc : 0 < c) (he : 0 ≤ e) : persistenceEq c e ≤ 1 := by
  rw [persistenceEq, sub_le_self_iff]
  positivity

/-- `p* < 1` for `c > 0`, `e > 0`. -/
theorem persistenceEq_lt_one (hc : 0 < c) (he : 0 < e) : persistenceEq c e < 1 := by
  rw [persistenceEq, sub_lt_self_iff]
  positivity

/-- **Persistence threshold.** For `c > 0` and `e ≥ 0`, the persistence equilibrium is an
occupied state, `p* ∈ (0, 1]`, exactly when colonization beats extinction, `e < c`. -/
theorem persistenceEq_mem_Ioc_iff (hc : 0 < c) (he : 0 ≤ e) :
    persistenceEq c e ∈ Ioc 0 1 ↔ e < c :=
  ⟨fun h => (persistenceEq_pos_iff hc).1 h.1,
    fun h => ⟨(persistenceEq_pos_iff hc).2 h, persistenceEq_le_one hc he⟩⟩

/-- The derivative of the balance in `p`: `c - e - 2 c p`. -/
theorem hasDerivAt_balance (c e p : ℝ) : HasDerivAt (balance c e) (c - e - 2 * c * p) p := by
  have h : HasDerivAt (fun q => c * q * (1 - q) - e * q) (c * 1 * (1 - p) + c * p * (0 - 1) -
      e * 1) p :=
    ((((hasDerivAt_id p).const_mul c).mul ((hasDerivAt_const p 1).sub (hasDerivAt_id p))).sub
      ((hasDerivAt_id p).const_mul e))
  exact h.congr_deriv (by ring)

/-- **Linearization at extinction**: `f'(0) = c - e`, so `p = 0` is linearly unstable iff
`c > e`. -/
theorem hasDerivAt_balance_zero (c e : ℝ) : HasDerivAt (balance c e) (c - e) 0 := by
  simpa using hasDerivAt_balance c e 0

/-- **Linearization at persistence**: `f'(p*) = e - c` (for `c ≠ 0`), so `p*` is linearly stable
iff `c > e`. -/
theorem hasDerivAt_balance_persistenceEq (hc : c ≠ 0) :
    HasDerivAt (balance c e) (e - c) (persistenceEq c e) := by
  refine (hasDerivAt_balance c e _).congr_deriv ?_
  unfold persistenceEq
  field_simp
  ring

/-- The extinction equilibrium `p ≡ 0` is a solution. -/
theorem isSolution_const_zero (c e : ℝ) : IsSolution c e (fun _ => 0) :=
  ⟨fun t _ => by simpa [balance] using hasDerivAt_const t (0 : ℝ)⟩

/-- The persistence equilibrium `p ≡ p*` is a solution (for `c ≠ 0`). -/
theorem isSolution_const_persistenceEq (hc : c ≠ 0) :
    IsSolution c e (fun _ => persistenceEq c e) :=
  ⟨fun t _ => by
    rw [(balance_eq_zero_iff hc).2 (Or.inr rfl)]
    exact hasDerivAt_const t _⟩

/-! ### Bridge to the SIS model and the explicit solution -/

/-- **Bridge to SIS.** With `S = 1 - p`, a Levins solution is an SIS solution with `β = c`,
`γ = e` and `N = 1`. -/
theorem IsSolution.toSIS {p : ℝ → ℝ} (h : IsSolution c e p) :
    SIS.IsSolution c e 1 (fun t => 1 - p t) p := by
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · convert (h.hasDerivAt t ht).const_sub 1 using 1
    simp only [balance]
    ring
  · convert h.hasDerivAt t ht using 1
    simp only [balance]
    ring

/-- The **explicit solution** of the Levins equation with `p(0) = p₀`: the SIS solution with
`β = c`, `γ = e`, `N = 1`,
`p(t) = p₀ e^{(c - e) t} / (1 + c p₀ φ(t))`, `φ(t) = ∫₀ᵗ e^{(c - e) s} ds`. -/
noncomputable def levins (c e p₀ t : ℝ) : ℝ :=
  SIS.sisInfected c e 1 p₀ t

@[simp]
theorem levins_zero (c e p₀ : ℝ) : levins c e p₀ 0 = p₀ :=
  SIS.sisInfected_zero _ _ _ _

/-- **The explicit solution solves the Levins equation** (`c ≥ 0`, `p₀ ≥ 0`). -/
theorem isSolution_levins {p₀ : ℝ} (hc : 0 ≤ c) (hp₀ : 0 ≤ p₀) :
    IsSolution c e (levins c e p₀) := by
  refine ⟨fun t ht => ?_⟩
  convert (SIS.isSolution_sis (γ := e) hc one_pos hp₀).hasDerivAt_infected t ht using 1
  · rfl
  · simp only [balance, SIS.sisSusceptible, levins]
    ring

/-- **Invariance of `[0, 1]` for the explicit solution** (`c, e ≥ 0`). -/
theorem levins_mem_Icc {p₀ t : ℝ} (hc : 0 ≤ c) (he : 0 ≤ e) (hp₀ : p₀ ∈ Icc 0 1)
    (ht : 0 ≤ t) : levins c e p₀ t ∈ Icc 0 1 :=
  SIS.sisInfected_mem_Icc hc he one_pos hp₀ ht

/-- **Global existence.** For `c, e ≥ 0` and `p₀ ∈ [0, 1]` there is a solution with `p(0) = p₀`
that stays in `[0, 1]` for all `t ≥ 0`. -/
theorem exists_isSolution {p₀ : ℝ} (hc : 0 ≤ c) (he : 0 ≤ e) (hp₀ : p₀ ∈ Icc 0 1) :
    ∃ p : ℝ → ℝ, IsSolution c e p ∧ p 0 = p₀ ∧ ∀ t, 0 ≤ t → p t ∈ Icc 0 1 :=
  ⟨levins c e p₀, isSolution_levins hc hp₀.1, levins_zero _ _ _,
    fun _ ht => levins_mem_Icc hc he hp₀ ht⟩

/-- The explicit solution is positive on `[0, ∞)` when `p₀ > 0` (`c ≥ 0`). -/
theorem levins_pos {p₀ t : ℝ} (hc : 0 ≤ c) (hp₀ : 0 < p₀) (ht : 0 ≤ t) :
    0 < levins c e p₀ t :=
  div_pos (mul_pos hp₀ (exp_pos _))
    (by linarith [SIS.one_le_sisDenom (γ := e) hc one_pos hp₀.le ht])

/-- **Logistic form.** For `0 ≤ e < c` the explicit solution is the logistic curve with rate
`c - e` and carrying capacity `p*`. -/
theorem levins_eq_logistic (hc : 0 < c) (hec : e < c) (p₀ t : ℝ) :
    levins c e p₀ t = Dynamics.Logistic.logistic (c - e) (persistenceEq c e) p₀ t := by
  rw [levins, SIS.sisInfected_eq_logistic hc.ne' (sub_pos.2 hec).ne' one_ne_zero,
    persistenceEq]
  congr 1
  field_simp

/-! ### Uniqueness -/

namespace IsSolution

variable {p q : ℝ → ℝ}

/-- **Forward uniqueness.** Two solutions with the same initial value agree on `[0, ∞)`. -/
theorem eq_of_initial (hp : IsSolution c e p) (hq : IsSolution c e q) (h0 : p 0 = q 0)
    {t : ℝ} (ht : 0 ≤ t) : p t = q t :=
  hp.toSIS.infected_eq_of_initial hq.toSIS one_ne_zero (by ring) (by ring) h0 ht

/-- **Every solution is the explicit one** (`c ≥ 0`, `p(0) ≥ 0`). -/
theorem eq_levins (hp : IsSolution c e p) (hc : 0 ≤ c) (hp0 : 0 ≤ p 0) {t : ℝ} (ht : 0 ≤ t) :
    p t = levins c e (p 0) t :=
  hp.eq_of_initial (isSolution_levins hc hp0) (levins_zero _ _ _).symm ht

/-- **Invariance of `[0, 1]`** (`c, e ≥ 0`). -/
theorem mem_Icc (hp : IsSolution c e p) (hc : 0 ≤ c) (he : 0 ≤ e) (hp0 : p 0 ∈ Icc 0 1)
    {t : ℝ} (ht : 0 ≤ t) : p t ∈ Icc 0 1 :=
  hp.eq_levins hc hp0.1 ht ▸ levins_mem_Icc hc he hp0 ht

/-- An occupied landscape stays occupied: `p(0) > 0 → p(t) > 0` (`c ≥ 0`). -/
theorem pos (hp : IsSolution c e p) (hc : 0 ≤ c) (hp0 : 0 < p 0) {t : ℝ} (ht : 0 ≤ t) :
    0 < p t :=
  hp.eq_levins hc hp0.le ht ▸ levins_pos hc hp0 ht

end IsSolution

/-! ### Stability notions -/

/-- `a` is **Lyapunov stable** for solutions starting in `D`: solutions that start in `D` close
to `a` stay close to `a` for all `t ≥ 0`. -/
abbrev IsLyapunovStable (c e a : ℝ) (D : Set ℝ) : Prop :=
  MathlibExt.Dynamics.EquilibriumStability.IsLyapunovStable (IsSolution c e) a D

/-- `a` **attracts** every solution starting in `D`. -/
abbrev IsGloballyAttracting (c e a : ℝ) (D : Set ℝ) : Prop :=
  MathlibExt.Dynamics.EquilibriumStability.IsGloballyAttracting (IsSolution c e) a D

/-- `a` is **globally (asymptotically) stable** on `D`: Lyapunov stable and attracting every
solution starting in `D`. -/
abbrev IsGloballyStable (c e a : ℝ) (D : Set ℝ) : Prop :=
  MathlibExt.Dynamics.EquilibriumStability.IsGloballyStable (IsSolution c e) a D

/-! ### Extinction: `c ≤ e` -/

namespace IsSolution

variable {p : ℝ → ℝ}

/-- For `c ≤ e`, the occupied fraction never exceeds its initial value:
`0 ≤ p(t) ≤ p(0) e^{(c - e) t} ≤ p(0)`. -/
theorem le_initial (hp : IsSolution c e p) (hc : 0 ≤ c) (hce : c ≤ e) (hp0 : 0 ≤ p 0) {t : ℝ}
    (ht : 0 ≤ t) : p t ≤ p 0 := by
  rw [hp.eq_levins hc hp0 ht]
  refine (SIS.sisInfected_le_mul_exp hc one_pos hp0 ht).trans ?_
  refine mul_le_of_le_one_right hp0 (exp_le_one_iff.2 ?_)
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) ht

/-- **Extinction.** For `0 ≤ c ≤ e`, `e > 0`, every solution with `p(0) ≥ 0` tends to `0`. -/
theorem tendsto_zero (hp : IsSolution c e p) (hc : 0 ≤ c) (he : 0 < e) (hce : c ≤ e)
    (hp0 : 0 ≤ p 0) : Tendsto p atTop (𝓝 0) :=
  hp.toSIS.tendsto_infected_zero hc he hce one_pos (by ring) hp0

end IsSolution

/-- **Global stability of extinction.** If `0 ≤ c ≤ e` and `e > 0`, the extinction equilibrium
`p = 0` is Lyapunov stable and attracts every solution starting in `[0, 1]`. `e > 0` is needed:
for `c = e = 0` every state is an equilibrium, so `0` attracts nothing else. -/
theorem extinction_isGloballyStable (hc : 0 ≤ c) (he : 0 < e) (hce : c ≤ e) :
    IsGloballyStable c e 0 (Icc 0 1) := by
  refine ⟨fun ε hε => ⟨ε, hε, fun p hp hp0 hδ t ht => ?_⟩,
    fun p hp hp0 => hp.tendsto_zero hc he hce hp0.1⟩
  have h1 := hp.le_initial hc hce hp0.1 ht
  have h2 := (hp.mem_Icc hc he.le hp0 ht).1
  rw [sub_zero, abs_of_nonneg hp0.1] at hδ
  rw [sub_zero, abs_of_nonneg h2]
  linarith

/-! ### Persistence: `c > e` -/

/-- Distance to `p*` along the explicit solution:
`p(t) - p* = p* (p₀ - p*) / (p* + p₀ (e^{(c - e) t} - 1))`. -/
theorem levins_sub_persistenceEq (hc : 0 < c) (hec : e < c) {p₀ t : ℝ}
    (hden : persistenceEq c e + p₀ * (exp ((c - e) * t) - 1) ≠ 0) :
    levins c e p₀ t - persistenceEq c e =
      persistenceEq c e * (p₀ - persistenceEq c e) /
        (persistenceEq c e + p₀ * (exp ((c - e) * t) - 1)) := by
  rw [levins_eq_logistic hc hec, Dynamics.Logistic.logistic]
  field_simp
  ring

/-- **The distance to `p*` never grows.** For `0 < c`, `e < c`, `p₀ > 0` and `t ≥ 0`,
`|p(t) - p*| ≤ |p₀ - p*|`. -/
theorem abs_levins_sub_le (hc : 0 < c) (hec : e < c) {p₀ t : ℝ} (hp₀ : 0 < p₀) (ht : 0 ≤ t) :
    |levins c e p₀ t - persistenceEq c e| ≤ |p₀ - persistenceEq c e| := by
  have hK := (persistenceEq_pos_iff hc).2 hec
  have hE : 0 ≤ exp ((c - e) * t) - 1 := by
    rw [sub_nonneg, one_le_exp_iff]; exact mul_nonneg (sub_pos.2 hec).le ht
  have hD : persistenceEq c e ≤ persistenceEq c e + p₀ * (exp ((c - e) * t) - 1) := by
    nlinarith
  have hDpos : 0 < persistenceEq c e + p₀ * (exp ((c - e) * t) - 1) := by linarith
  rw [levins_sub_persistenceEq hc hec hDpos.ne', abs_div, abs_mul, abs_of_pos hK,
    abs_of_pos hDpos, div_le_iff₀ hDpos, mul_comm]
  exact mul_le_mul_of_nonneg_left hD (abs_nonneg _)

/-- **Exponential convergence to `p*`.** For `0 < c`, `e < c`, `p₀ > 0` and `t ≥ 0`,
`|p(t) - p*| ≤ (p* / min p₀ p*) |p₀ - p*| e^{-(c - e) t}`. -/
theorem abs_levins_sub_le_exp (hc : 0 < c) (hec : e < c) {p₀ t : ℝ} (hp₀ : 0 < p₀)
    (ht : 0 ≤ t) :
    |levins c e p₀ t - persistenceEq c e| ≤
      persistenceEq c e / min p₀ (persistenceEq c e) * |p₀ - persistenceEq c e| *
        exp (-((c - e) * t)) := by
  set K := persistenceEq c e
  have hK : 0 < K := (persistenceEq_pos_iff hc).2 hec
  set E := exp ((c - e) * t)
  have hE1 : 1 ≤ E := one_le_exp_iff.2 (mul_nonneg (sub_pos.2 hec).le ht)
  set m := min p₀ K
  have hm : 0 < m := lt_min hp₀ hK
  -- The denominator is at least `min p₀ p* · e^{(c - e) t}`.
  have hD : m * E ≤ K + p₀ * (E - 1) := by
    rcases le_total p₀ K with h | h
    · rw [show m = p₀ from min_eq_left h]; nlinarith
    · rw [show m = K from min_eq_right h]; nlinarith
  have hDpos : 0 < K + p₀ * (E - 1) := lt_of_lt_of_le (by positivity) hD
  rw [levins_sub_persistenceEq hc hec hDpos.ne', abs_div, abs_mul, abs_of_pos hK,
    abs_of_pos hDpos, Real.exp_neg]
  rw [div_le_iff₀ hDpos]
  have hEpos : 0 < E := by positivity
  have key : K / m * |p₀ - K| * E⁻¹ * (K + p₀ * (E - 1)) =
      K * |p₀ - K| * ((K + p₀ * (E - 1)) / (m * E)) := by
    field_simp
  rw [key]
  have hratio : 1 ≤ (K + p₀ * (E - 1)) / (m * E) := by
    rw [le_div_iff₀ (by positivity), one_mul]; exact hD
  have : 0 ≤ K * |p₀ - K| := by positivity
  nlinarith

namespace IsSolution

variable {p : ℝ → ℝ}

/-- **Persistence.** For `0 ≤ e < c`, every solution with `p(0) > 0` tends to `p* = 1 - e / c`. -/
theorem tendsto_persistenceEq (hp : IsSolution c e p) (he : 0 ≤ e) (hec : e < c)
    (hp0 : 0 < p 0) : Tendsto p atTop (𝓝 (persistenceEq c e)) := by
  have h := hp.toSIS.tendsto_infected_endemic he hec one_pos (by ring) hp0
  rwa [one_mul] at h

end IsSolution

/-- **Global stability of persistence.** If `0 ≤ e < c`, the persistence equilibrium
`p* = 1 - e / c ∈ (0, 1]` is Lyapunov stable and attracts every solution starting in `(0, 1]`. -/
theorem persistence_isGloballyStable (he : 0 ≤ e) (hec : e < c) :
    IsGloballyStable c e (persistenceEq c e) (Ioc 0 1) := by
  have hc : 0 < c := he.trans_lt hec
  refine ⟨fun ε hε => ⟨ε, hε, fun p hp hp0 hδ t ht => ?_⟩,
    fun p hp hp0 => hp.tendsto_persistenceEq he hec hp0.1⟩
  rw [hp.eq_levins hc.le hp0.1.le ht]
  exact (abs_levins_sub_le hc hec hp0.1 ht).trans_lt hδ

/-- **Extinction is unstable above the threshold.** If `0 ≤ e < c`, the extinction equilibrium is
not Lyapunov stable on `[0, 1]`: arbitrarily small occupied fractions grow towards `p*`. -/
theorem not_isLyapunovStable_zero (he : 0 ≤ e) (hec : e < c) :
    ¬ IsLyapunovStable c e 0 (Icc 0 1) := by
  intro hstab
  have hc : 0 < c := he.trans_lt hec
  have hK := (persistenceEq_pos_iff hc).2 hec
  obtain ⟨δ, hδ, hδε⟩ := hstab (persistenceEq c e / 2) (by positivity)
  set p₀ := min (δ / 2) 1
  have hp₀ : 0 < p₀ := lt_min (by positivity) one_pos
  have hp₀1 : p₀ ≤ 1 := min_le_right _ _
  have hp₀δ : p₀ < δ := (min_le_left _ _).trans_lt (by linarith)
  have hsol := isSolution_levins (e := e) hc.le hp₀.le
  have hlim := hsol.tendsto_persistenceEq he hec (by rwa [levins_zero])
  obtain ⟨t, ht, hgt⟩ := ((eventually_ge_atTop 0).and
    (hlim.eventually (lt_mem_nhds (half_lt_self hK)))).exists
  have := hδε _ hsol (by rw [levins_zero]; exact ⟨hp₀.le, hp₀1⟩)
    (by rw [levins_zero, sub_zero, abs_of_pos hp₀]; exact hp₀δ) t ht
  rw [sub_zero] at this
  linarith [le_abs_self (levins c e p₀ t)]

/-- **Persistence threshold, global form.** For `c, e > 0`, every solution starting in `[0, 1]`
goes extinct iff `c ≤ e`. -/
theorem tendsto_zero_iff_le (hc : 0 < c) (he : 0 < e) :
    (∀ p : ℝ → ℝ, IsSolution c e p → p 0 ∈ Icc 0 1 → Tendsto p atTop (𝓝 0)) ↔ c ≤ e := by
  refine ⟨fun h => le_of_not_gt fun hec => ?_,
    fun hce p hp hp0 => hp.tendsto_zero hc.le he hce hp0.1⟩
  have hsol := isSolution_levins (e := e) hc.le zero_le_one
  have h1 := h _ hsol (by rw [levins_zero]; exact ⟨zero_le_one, le_rfl⟩)
  have h2 := hsol.tendsto_persistenceEq he.le hec (by rw [levins_zero]; exact one_pos)
  exact ((persistenceEq_pos_iff hc).2 hec).ne' (tendsto_nhds_unique h2 h1)

end MathlibExt.Biology.Ecology.LevinsMetapopulation
