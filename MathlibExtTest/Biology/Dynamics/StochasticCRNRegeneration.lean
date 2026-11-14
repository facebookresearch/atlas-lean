/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.StochasticCRNRegeneration

/-! Tests for the regeneration theorem for complex-balanced stochastic reaction networks.

* The birth–death network `∅ ⇌ A` with rate constants `k₁, k₂ > 0`: complex balance at
  `c = k₁ / k₂`, the drift bound `L V ≤ k₁` for `V(x) = x`, and reachability of every state from
  the empty state are all checked from the definitions. No forward-equation, regeneration or
  non-explosion hypothesis is assumed: `ergodic_of_isComplexBalanced_of_reachable` then gives
  recurrence of the empty state, a finite mean return time, and the long-run fraction of time with
  no molecules, `e^{-k₁/k₂}`, from every initial state and from the Poisson initial law. The
  Laplace form of the forward-equation transfer and the path non-explosion are instantiated too.
* The pure-birth network `∅ → A` satisfies the drift bound `L V ≤ k` for `V(x) = x`
  (`generator_pureBirth_le`), so it is non-explosive by `StochasticCRNNonExplosion`
  (`ae_tendsto_jumpTime_pureBirth`), and every state is reachable from `0`, but it is not complex
  balanced for any `c`, so no ergodicity is claimed.
* For the autocatalytic network `2A → 3A`, no `c > 0` is complex balanced, and no function
  `V ≥ ∑_s x_s` satisfies a drift bound `L V ≤ a V + b` (such a `V` would be bounded on
  `{x ≥ 2}`), so neither non-explosion nor ergodicity is claimed. Started from `x ≥ 2` the chain
  explodes (a remark, not proved here: the mean holding times `1 / (k x (x - 1))`, `x ≥ 2`, are
  summable). From `x ≤ 1` no reaction can fire, so explosion is claimed only from `x ≥ 2`. -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MathlibExtTest.Biology.Dynamics.StochasticCRNRegeneration

open MathlibExt.Biology.Dynamics.ComplexBalanced MathlibExt.Biology.Dynamics.SystemsBiology
open MathlibExt.Biology.Dynamics.StochasticCRNErgodicity
open MathlibExt.Biology.Dynamics.StochasticCRNNonExplosion
open MathlibExt.Biology.Dynamics.StochasticCRNRegeneration

/-- The state of a one-species network with `n` molecules. -/
def st (n : ℕ) : Unit → ℕ := fun _ => n

theorem fun_eq_st (x : Unit → ℕ) : x = st (x ()) := funext fun u => by cases u; rfl

theorem st_eq_iff {m n : ℕ} : st m = st n ↔ m = n :=
  ⟨fun h => congrFun h (), fun h => h ▸ rfl⟩

/-! ### Birth–death `∅ ⇌ A` -/

/-- The birth–death network: reaction `0` is `∅ → A`, reaction `1` is `A → ∅`. -/
def birthDeath : ReactionNetwork Unit (Fin 2) where
  src := ![st 0, st 1]
  prod := ![st 1, st 0]

@[simp] theorem birthDeath_src_zero : birthDeath.src 0 = st 0 := rfl
@[simp] theorem birthDeath_src_one : birthDeath.src 1 = st 1 := rfl
@[simp] theorem birthDeath_prod_zero : birthDeath.prod 0 = st 1 := rfl
@[simp] theorem birthDeath_prod_one : birthDeath.prod 1 = st 0 := rfl

/-- Rate constants `k₁` (birth) and `k₂` (death). -/
noncomputable def kBD (k₁ k₂ : ℝ) : Fin 2 → ℝ := ![k₁, k₂]

/-- The complex-balanced concentration `c = k₁ / k₂`. -/
noncomputable def cBD (k₁ k₂ : ℝ) : Unit → ℝ := fun _ => k₁ / k₂

theorem kBD_nonneg {k₁ k₂ : ℝ} (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂) : ∀ r, 0 ≤ kBD k₁ k₂ r := by
  intro r
  fin_cases r
  · exact hk₁
  · exact hk₂

theorem rate_birthDeath (k₁ k₂ : ℝ) (c : Unit → ℝ) :
    birthDeath.rate (kBD k₁ k₂) c 0 = k₁ ∧ birthDeath.rate (kBD k₁ k₂) c 1 = k₂ * c () := by
  simp [ReactionNetwork.rate, birthDeath, kBD, st]

/-- Complex balance of `c = k₁ / k₂`, from the definition. -/
theorem isComplexBalanced_birthDeath {k₁ k₂ : ℝ} (hk₂ : 0 < k₂) :
    birthDeath.IsComplexBalanced (kBD k₁ k₂) (cBD k₁ k₂) := by
  intro z
  obtain ⟨h0, h1⟩ := rate_birthDeath k₁ k₂ (cBD k₁ k₂)
  have hc : k₂ * cBD k₁ k₂ () = k₁ := by simp [cBD]; field_simp
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_two]
  rw [fun_eq_st z]
  simp only [birthDeath_src_zero, birthDeath_src_one, birthDeath_prod_zero,
    birthDeath_prod_one, st_eq_iff, h0, h1, hc]
  rcases Nat.lt_trichotomy (z ()) 1 with h | h | h
  · obtain h' : z () = 0 := by omega
    simp [h']
  · simp [h]
  · simp [show 0 ≠ z () by omega, show 1 ≠ z () by omega]

theorem propensity_birth (k₁ k₂ : ℝ) (x : Unit → ℕ) :
    propensity birthDeath (kBD k₁ k₂) 0 x = k₁ := by
  simp [propensity, kBD, birthDeath, st]

theorem propensity_death (k₁ k₂ : ℝ) (x : Unit → ℕ) :
    propensity birthDeath (kBD k₁ k₂) 1 x = k₂ * x () := by
  simp [propensity, kBD, birthDeath, st]

/-- The molecule count `V(x) = x`. -/
def countV : (Unit → ℕ) → ℝ≥0 := fun x => x ()

/-- The drift bound `L V ≤ k₁` for `V(x) = x`: births raise `V` by `1` at rate `k₁`, deaths lower
it. -/
theorem generator_birthDeath_le {k₁ k₂ : ℝ} (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂) (x : Unit → ℕ) :
    (massAction birthDeath (kBD k₁ k₂) (kBD_nonneg hk₁ hk₂)).generator
      (fun y => (countV y : ℝ)) x ≤ 0 * countV x + k₁ := by
  simp only [StochasticCRN.generator, Fin.sum_univ_two, jump_massAction]
  change propensity birthDeath (kBD k₁ k₂) 0 x * _ + propensity birthDeath (kBD k₁ k₂) 1 x * _ ≤ _
  rw [propensity_birth, propensity_death]
  have hb : ((countV (fire birthDeath 0 x) : ℝ≥0) : ℝ) = x () + 1 := by
    simp [countV, fire, birthDeath, st]
  have hd : ((countV (fire birthDeath 1 x) : ℝ≥0) : ℝ) ≤ x () := by
    simp only [countV, fire, birthDeath]
    exact_mod_cast Nat.sub_le _ _
  have hx : ((countV x : ℝ≥0) : ℝ) = x () := by simp [countV]
  rw [hb, hx]
  have : k₂ * (x () : ℝ) * (((countV (fire birthDeath 1 x) : ℝ≥0) : ℝ) - x ()) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  linarith

/-- Every state is reached from the empty state by births. -/
theorem reach_birthDeath {k₁ k₂ : ℝ} (hk₁ : 0 < k₁) (y : Unit → ℕ) :
    Relation.ReflTransGen
      (fun u v => ∃ r, 0 < propensity birthDeath (kBD k₁ k₂) r u ∧ fire birthDeath r u = v)
      (st 0) y := by
  rw [fun_eq_st y]
  induction y () with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
    refine ih.tail ⟨0, by rw [propensity_birth]; exact hk₁, ?_⟩
    funext u
    simp [fire, birthDeath, st]

/-- **Birth–death: every hypothesis discharged, ergodicity follows.** For `k₁, k₂ > 0`, the
stochastic mass-action chain of `∅ ⇌ A` returns to the empty state almost surely with finite mean
return time, and from every initial state the long-run fraction of time with no molecules is
`e^{-k₁/k₂}` almost surely. Complex balance, the drift bound and reachability are proved above
from the definitions; no forward-equation, regeneration or non-explosion hypothesis is taken. -/
theorem ergodic_birthDeath {k₁ k₂ : ℝ} (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (x : Unit → ℕ) :
    (massAction birthDeath (kBD k₁ k₂) (kBD_nonneg hk₁.le hk₂.le)).inputMeasure
        {ω | visit (st 0) (st 0) 1 ω ≠ ⊤} = 1 ∧
      Integrable (fun ω => (massAction birthDeath (kBD k₁ k₂) (kBD_nonneg hk₁.le hk₂.le)).jumpTime
          (st 0) ω (visit (st 0) (st 0) 1 ω).toNat)
        (massAction birthDeath (kBD k₁ k₂) (kBD_nonneg hk₁.le hk₂.le)).inputMeasure ∧
      ∀ᵐ ω ∂(massAction birthDeath (kBD k₁ k₂) (kBD_nonneg hk₁.le hk₂.le)).inputMeasure,
        Tendsto (fun t => occupation
          (fun s ω => (massAction birthDeath (kBD k₁ k₂) (kBD_nonneg hk₁.le hk₂.le)).path x ω s)
          (Set.indicator {st 0} 1) t ω / t) atTop (𝓝 (Real.exp (-(k₁ / k₂)))) := by
  have hc : ∀ s, 0 < cBD k₁ k₂ s := fun _ => div_pos hk₁ hk₂
  obtain ⟨hp, hint, hlim⟩ := ergodic_of_isComplexBalanced_of_reachable birthDeath
    (kBD_nonneg hk₁.le hk₂.le) (isComplexBalanced_birthDeath hk₂) hc countV le_rfl hk₁.le
    (generator_birthDeath_le hk₁.le hk₂.le) (fun x => by simp [countV]) (st 0)
    (reach_birthDeath hk₁)
  refine ⟨hp, hint, ?_⟩
  have hB : ∀ x, |Set.indicator {st 0} (1 : (Unit → ℕ) → ℝ) x| ≤ 1 := fun x => by
    by_cases h : x = st 0 <;> simp [Set.indicator, h]
  have hmean : ∑' x, poissonWeight (cBD k₁ k₂) x * Set.indicator {st 0} 1 x =
      Real.exp (-(k₁ / k₂)) := by
    rw [tsum_eq_single (st 0) fun x hx => by simp [Set.indicator, hx]]
    simp [poissonWeight, cBD, st]
  rw [← hmean]
  exact hlim x _ 1 hB

/-- The same limit for the chain started from the Poisson law `π_c`, the setting of
`StochasticCRNErgodicity.ergodic_of_isComplexBalanced`. -/
theorem ergodic_birthDeath_countLaw {k₁ k₂ : ℝ} (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) :
    ∀ᵐ z ∂(countLaw (poissonWeight (cBD k₁ k₂))).prod
        (massAction birthDeath (kBD k₁ k₂) (kBD_nonneg hk₁.le hk₂.le)).inputMeasure,
      Tendsto (fun t => occupation (fun s z =>
          (massAction birthDeath (kBD k₁ k₂) (kBD_nonneg hk₁.le hk₂.le)).path z.1 z.2 s)
        (Set.indicator {st 0} 1) t z / t) atTop (𝓝 (Real.exp (-(k₁ / k₂)))) := by
  have hc : ∀ s, 0 < cBD k₁ k₂ s := fun _ => div_pos hk₁ hk₂
  have hB : ∀ x, |Set.indicator {st 0} (1 : (Unit → ℕ) → ℝ) x| ≤ 1 := fun x => by
    by_cases h : x = st 0 <;> simp [Set.indicator, h]
  have hmean : ∑' x, poissonWeight (cBD k₁ k₂) x * Set.indicator {st 0} 1 x =
      Real.exp (-(k₁ / k₂)) := by
    rw [tsum_eq_single (st 0) fun x hx => by simp [Set.indicator, hx]]
    simp [poissonWeight, cBD, st]
  rw [← hmean]
  exact ergodic_of_isComplexBalanced_of_reachable_countLaw birthDeath
    (kBD_nonneg hk₁.le hk₂.le) (isComplexBalanced_birthDeath hk₂) hc countV le_rfl hk₁.le
    (generator_birthDeath_le hk₁.le hk₂.le) (fun x => by simp [countV]) (st 0)
    (reach_birthDeath hk₁) _ 1 hB

/-- The forward-equation transfer for birth–death, in Laplace form, at the empty state:
`∑_x π(x) E_x[∫_0^∞ θ e^{-θ t} [X_t = 0] dt] = π(0) = e^{-k₁/k₂}`. -/
theorem laplace_birthDeath {k₁ k₂ : ℝ} (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) {θ : ℝ} (hθ : 0 < θ) :
    ∑' x, ENNReal.ofReal (poissonWeight (cBD k₁ k₂) x) *
        ∫⁻ ω, (∫⁻ t in Set.Ioi 0, ENNReal.ofReal (θ * Real.exp (-(θ * t)) *
          Set.indicator {st 0} (1 : (Unit → ℕ) → ℝ)
            ((massAction birthDeath (kBD k₁ k₂) (kBD_nonneg hk₁.le hk₂.le)).path x ω t)))
          ∂(massAction birthDeath (kBD k₁ k₂) (kBD_nonneg hk₁.le hk₂.le)).inputMeasure =
      ENNReal.ofReal (Real.exp (-(k₁ / k₂))) := by
  have hc : ∀ s, 0 ≤ cBD k₁ k₂ s := fun _ => (div_pos hk₁ hk₂).le
  rw [tsum_poissonWeight_mul_lintegral_laplace_path birthDeath (kBD_nonneg hk₁.le hk₂.le)
    (isComplexBalanced_birthDeath hk₂) hc countV le_rfl hk₁.le
    (generator_birthDeath_le hk₁.le hk₂.le) (fun x => by simp [countV])
    (fun x => by by_cases h : x = st 0 <;> simp [Set.indicator, h])
    (fun x => by by_cases h : x = st 0 <;> simp [Set.indicator, h]) hθ,
    tsum_eq_single (st 0) fun x hx => by simp [Set.indicator, hx]]
  simp [poissonWeight, cBD, st]

/-- The path of the birth–death chain does not explode, in the sense of
`StochasticCRNErgodicity.NoExplosion`. -/
theorem noExplosion_birthDeath {k₁ k₂ : ℝ} (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (x : Unit → ℕ) :
    NoExplosion (massAction birthDeath (kBD k₁ k₂) (kBD_nonneg hk₁.le hk₂.le)).inputMeasure
      (fun s ω => (massAction birthDeath (kBD k₁ k₂) (kBD_nonneg hk₁.le hk₂.le)).path x ω s) :=
  noExplosion_path _ x (StochasticCRN.ae_tendsto_jumpTime_atTop_of_coercive _ countV le_rfl
    hk₁.le (generator_birthDeath_le hk₁.le hk₂.le) (fun x => by simp [countV]) x)

/-! ### Pure birth `∅ → A`: not complex balanced, so no claim -/

/-- The pure-birth network `∅ → A`. -/
def pureBirth : ReactionNetwork Unit Unit where
  src := fun _ => st 0
  prod := fun _ => st 1

/-- `∅ → A` is not complex balanced for any `c`: at the complex `∅` the outflow is `k > 0` and
the inflow is `0`. -/
theorem not_isComplexBalanced_pureBirth {k : ℝ} (hk : 0 < k) (c : Unit → ℝ) :
    ¬ pureBirth.IsComplexBalanced (fun _ => k) c := by
  intro h
  have := h (st 0)
  simp [pureBirth, ReactionNetwork.rate, st_eq_iff] at this
  rcases this with h1 | ⟨_, h2⟩
  · linarith
  · exact h2 rfl

/-- The drift bound `L V ≤ k` for `V(x) = x` holds for `∅ → A`: every reaction raises `V` by `1`
at rate `k`. -/
theorem generator_pureBirth_le {k : ℝ} (hk : 0 ≤ k) (x : Unit → ℕ) :
    (massAction pureBirth (fun _ => k) fun _ => hk).generator (fun y => (countV y : ℝ)) x ≤
      0 * countV x + k := by
  simp only [StochasticCRN.generator, Fintype.univ_unit, Finset.sum_singleton, jump_massAction]
  change propensity pureBirth (fun _ => k) () x * _ ≤ _
  have hp : propensity pureBirth (fun _ => k) () x = k := by
    simp [propensity, pureBirth, st]
  have hb : ((countV (fire pureBirth () x) : ℝ≥0) : ℝ) = x () + 1 := by
    simp [countV, fire, pureBirth, st]
  have hx : ((countV x : ℝ≥0) : ℝ) = x () := by simp [countV]
  rw [hp, hb, hx]
  linarith

/-- The pure-birth chain does not explode: from every initial state its jump times tend to `∞`
almost surely, by the drift bound `generator_pureBirth_le` and `StochasticCRNNonExplosion`. -/
theorem ae_tendsto_jumpTime_pureBirth {k : ℝ} (hk : 0 < k) (x : Unit → ℕ) :
    ∀ᵐ ω ∂(massAction pureBirth (fun _ => k) fun _ => hk.le).inputMeasure,
      Tendsto ((massAction pureBirth (fun _ => k) fun _ => hk.le).jumpTime x ω) atTop atTop :=
  StochasticCRN.ae_tendsto_jumpTime_atTop_of_coercive _ countV le_rfl hk.le
    (generator_pureBirth_le hk.le) (fun x => by simp [countV]) x

/-- Every state of `∅ → A` is reached from the empty state (so reachability is not what fails). -/
theorem reach_pureBirth {k : ℝ} (hk : 0 < k) (y : Unit → ℕ) :
    Relation.ReflTransGen
      (fun u v => ∃ r, 0 < propensity pureBirth (fun _ => k) r u ∧ fire pureBirth r u = v)
      (st 0) y := by
  rw [fun_eq_st y]
  induction y () with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
    refine ih.tail ⟨(), by simpa [propensity, pureBirth, st] using hk, ?_⟩
    funext u
    simp [fire, pureBirth, st]

/-! ### Autocatalysis `2A → 3A`: explosive from `x ≥ 2`, so no claim -/

/-- The autocatalytic network `2A → 3A`. -/
def autocat : ReactionNetwork Unit Unit where
  src := fun _ => st 2
  prod := fun _ => st 3

/-- `2A → 3A` is not complex balanced for `c > 0`: at the complex `2A` the outflow `k c²` is
positive and the inflow is `0`. -/
theorem not_isComplexBalanced_autocat {k : ℝ} (hk : 0 < k) {c : Unit → ℝ} (hc : 0 < c ()) :
    ¬ autocat.IsComplexBalanced (fun _ => k) c := by
  intro h
  have := h (st 2)
  simp [autocat, ReactionNetwork.rate, st_eq_iff, st] at this
  rcases this with h1 | h1
  · linarith
  · linarith

theorem generator_autocat (k : ℝ) (hk : 0 ≤ k) (V : (Unit → ℕ) → ℝ) (m : ℕ) :
    (massAction autocat (fun _ => k) fun _ => hk).generator V (st (m + 2)) =
      k * ((m + 2) * (m + 1)) * (V (st (m + 3)) - V (st (m + 2))) := by
  simp only [StochasticCRN.generator, Fintype.univ_unit, Finset.sum_singleton, jump_massAction]
  change propensity autocat (fun _ => k) () (st (m + 2)) * _ = _
  have hfire : fire autocat () (st (m + 2)) = st (m + 3) := by
    funext u; simp [fire, autocat, st]
  have hd : ((m + 2).descFactorial 2 : ℝ) = (m + 2) * (m + 1) := by
    rw [Nat.descFactorial_succ, Nat.descFactorial_one]
    push_cast
    ring
  have hp : propensity autocat (fun _ => k) () (st (m + 2)) = k * ((m + 2) * (m + 1)) := by
    simp only [propensity, autocat, st, Fintype.prod_unique]
    rw [hd]
  rw [hfire, hp]

/-- **No coercive drift bound for `2A → 3A`.** If `V ≥ ∑_s x_s` and `L V ≤ a V + b`, then from
`x ≥ 2` the bound `V(x + 1) ≤ V(x) (1 + (a + b) / (k x (x - 1)))` and `∑ 1 / (x (x - 1)) < ∞` make
`V` bounded on `{x ≥ 2}`, contradicting `V(x) ≥ x`. So the non-explosion criterion of
`StochasticCRNNonExplosion`, and hence `ergodic_of_isComplexBalanced_of_reachable`, does not
apply. Started from `x ≥ 2` the chain does explode (a remark, not proved here: the mean holding
times `1 / (k x (x - 1))`, `x ≥ 2`, are summable); from `x ≤ 1` no reaction can fire. -/
theorem not_drift_autocat {k : ℝ} (hk : 0 < k) (V : (Unit → ℕ) → ℝ≥0) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    ¬ ((∀ x, (massAction autocat (fun _ => k) fun _ => hk.le).generator
        (fun y => (V y : ℝ)) x ≤ a * V x + b) ∧ ∀ x, (∑ s, (x s : ℝ)) ≤ V x) := by
  rintro ⟨hdrift, hcoer⟩
  set C := (a + b) / k with hCdef
  have hC : 0 ≤ C := div_nonneg (by linarith) hk.le
  set W : ℕ → ℝ := fun m => (V (st (m + 2)) : ℝ) + 1 with hWdef
  have hW0 : ∀ m, 0 < W m := fun m => by simp only [hWdef]; positivity
  have hstep : ∀ m, W (m + 1) ≤ W m * Real.exp (C / ((m + 2) * (m + 1))) := by
    intro m
    have hd := hdrift (st (m + 2))
    rw [generator_autocat k hk.le (fun y => (V y : ℝ)) m] at hd
    have hpos : (0 : ℝ) < (m + 2) * (m + 1) := by positivity
    have hV : (0 : ℝ) ≤ V (st (m + 2)) := (V _).2
    have h1 : (V (st (m + 3)) : ℝ) - V (st (m + 2)) ≤ C * W m / ((m + 2) * (m + 1)) := by
      rw [le_div_iff₀ hpos, hCdef, hWdef]
      have : a * V (st (m + 2)) + b ≤ (a + b) * ((V (st (m + 2)) : ℝ) + 1) := by nlinarith
      have h2 : k * ((m + 2) * (m + 1)) * ((V (st (m + 3)) : ℝ) - V (st (m + 2))) ≤
          (a + b) * ((V (st (m + 2)) : ℝ) + 1) := hd.trans this
      rw [div_mul_eq_mul_div, le_div_iff₀ hk]
      nlinarith
    have h3 : W m * (1 + C / ((m + 2) * (m + 1))) ≤
        W m * Real.exp (C / ((m + 2) * (m + 1))) :=
      mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (C / ((m + 2) * (m + 1)))])
        (hW0 m).le
    have hWs : W (m + 1) = (V (st (m + 3)) : ℝ) + 1 := by simp only [hWdef]
    calc W (m + 1) = (V (st (m + 3)) : ℝ) + 1 := hWs
      _ ≤ W m + C * W m / ((m + 2) * (m + 1)) := by simp only [hWdef] at h1 ⊢; linarith
      _ = W m * (1 + C / ((m + 2) * (m + 1))) := by ring
      _ ≤ _ := h3
  have hbound : ∀ m : ℕ, W m ≤ W 0 * Real.exp (C * (1 - 1 / ((m : ℝ) + 1))) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc W (m + 1) ≤ W m * Real.exp (C / ((m + 2) * (m + 1))) := hstep m
        _ ≤ W 0 * Real.exp (C * (1 - 1 / ((m : ℝ) + 1))) *
            Real.exp (C / ((m + 2) * (m + 1))) :=
          mul_le_mul_of_nonneg_right ih (Real.exp_pos _).le
        _ = W 0 * Real.exp (C * (1 - 1 / (((m + 1 : ℕ) : ℝ) + 1))) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          push_cast
          field_simp
          ring
  have hfin : ∀ m : ℕ, ((m + 2 : ℕ) : ℝ) ≤ W 0 * Real.exp C := by
    intro m
    have h1 := hcoer (st (m + 2))
    simp only [st, Fintype.univ_unit, Finset.sum_singleton] at h1
    have h2 := hbound m
    have h3 : Real.exp (C * (1 - 1 / ((m : ℝ) + 1))) ≤ Real.exp C := by
      refine Real.exp_le_exp.2 ?_
      have : 0 ≤ 1 / ((m : ℝ) + 1) := by positivity
      nlinarith
    have h4 : W m ≤ W 0 * Real.exp C :=
      h2.trans (mul_le_mul_of_nonneg_left h3 (hW0 0).le)
    simp only [hWdef] at h4
    have : ((m + 2 : ℕ) : ℝ) ≤ (V (st (m + 2)) : ℝ) := h1
    linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (W 0 * Real.exp C)
  have := hfin m
  push_cast at this
  linarith

end MathlibExtTest.Biology.Dynamics.StochasticCRNRegeneration
