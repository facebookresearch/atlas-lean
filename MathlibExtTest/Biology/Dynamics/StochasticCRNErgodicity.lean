/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.StochasticCRNErgodicity

/-! Tests for the ergodic theorem for complex-balanced stochastic reaction networks.

* The birth–death network `∅ ⇌ A` with rate constants `k₁, k₂ > 0`: complex balanced at
  `c = k₁ / k₂` (checked from the definition), its stationary law is Poisson with mean
  `k₁ / k₂`, the master equation at the empty state is checked by hand, and the ergodic theorem
  gives positive recurrence and the long-run fraction of time with no molecules,
  `e^{-k₁/k₂}`, computed from the definitions.
* A one-state instance in which every hypothesis of `ergodic_of_isComplexBalanced` is
  discharged, so the hypotheses are jointly satisfiable.
* The network `∅ → A`, `2A → ∅` is not complex balanced for any `c`, and no Poisson law
  `π_c` with `c > 0` solves its master equation, so no product form is claimed.
* The autocatalytic network `2A → 3A` explodes (the expected holding times from `2` on sum to
  `1 / k`); it is not complex balanced for `c > 0` and `π_c` does not solve its master
  equation, and a path that blows up violates `NoExplosion`, so no ergodicity is claimed. -/

open MeasureTheory ProbabilityTheory Filter Topology Function

namespace MathlibExtTest.Biology.Dynamics.StochasticCRNErgodicity

open MathlibExt.Biology.Dynamics.ComplexBalanced
open MathlibExt.Biology.Dynamics.StochasticCRNErgodicity MathlibExt.Biology.Dynamics.SystemsBiology

/-- The state of a one-species network with `n` molecules. -/
def st (n : ℕ) : Unit → ℕ := fun _ => n

theorem fun_eq_st (x : Unit → ℕ) : x = st (x ()) := funext fun u => by cases u; rfl

theorem st_eq_iff {m n : ℕ} : st m = st n ↔ m = n :=
  ⟨fun h => congrFun h (), fun h => h ▸ rfl⟩

theorem st_le_iff {m n : ℕ} : st m ≤ st n ↔ m ≤ n :=
  ⟨fun h => h (), fun h _ => h⟩

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

theorem rate_birthDeath (k₁ k₂ : ℝ) (c : Unit → ℝ) :
    birthDeath.rate (kBD k₁ k₂) c 0 = k₁ ∧ birthDeath.rate (kBD k₁ k₂) c 1 = k₂ * c () := by
  simp [ReactionNetwork.rate, birthDeath, kBD, st]

/-- Complex balance of `c = k₁ / k₂`, from the definition: at the complex `∅` the outflow `k₁`
equals the inflow `k₂ c`, and at `A` the outflow `k₂ c` equals the inflow `k₁`. -/
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

/-- The stationary law is Poisson with mean `k₁ / k₂`. -/
theorem poissonWeight_birthDeath (k₁ k₂ : ℝ) (n : ℕ) :
    poissonWeight (cBD k₁ k₂) (st n) = (k₁ / k₂) ^ n * Real.exp (-(k₁ / k₂)) / n.factorial := by
  simp [poissonWeight, cBD, st]

/-- The master equation at the empty state, by hand: the outflow `π(0) k₁` (a birth) equals the
inflow `π(1) k₂` (one death from `1`). -/
theorem master_birthDeath_zero {k₁ k₂ : ℝ} (hk₂ : 0 < k₂) :
    poissonWeight (cBD k₁ k₂) (st 0) * ∑ r, propensity birthDeath (kBD k₁ k₂) r (st 0) =
      ∑ r ∈ Finset.univ.filter (fun r => birthDeath.prod r ≤ st 0),
        poissonWeight (cBD k₁ k₂) (unfire birthDeath r (st 0)) *
          propensity birthDeath (kBD k₁ k₂) r (unfire birthDeath r (st 0)) := by
  rw [Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [propensity, birthDeath_src_zero, birthDeath_src_one, birthDeath_prod_zero,
    birthDeath_prod_one, kBD, st_le_iff]
  simp [poissonWeight, cBD, st, unfire]
  field_simp

/-- The ergodic theorem for birth–death: every chain satisfying the hypotheses is positive
recurrent, and the long-run fraction of time it spends with no molecules is `e^{-k₁/k₂}`. -/
theorem ergodic_birthDeath {k₁ k₂ : ℝ} (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℝ → Ω → (Unit → ℕ)} (hX : Measurable (uncurry X)) (hnonexp : NoExplosion P X)
    (htransfer : NoExplosion P X → ∀ p : (Unit → ℕ) → ℝ, (∀ x, 0 ≤ p x) → HasSum p 1 →
      IsStationaryMasterSolution birthDeath (kBD k₁ k₂) p → P.map (X 0) = countLaw p →
      ∀ t, 0 ≤ t → P.map (X t) = countLaw p)
    (hinit : P.map (X 0) = countLaw (poissonWeight (cBD k₁ k₂)))
    {R : ℕ → Ω → ℝ} (hreg : IsRegenerative P X R (st 0)) :
    IsPositiveRecurrent P R ∧
      ∀ᵐ ω ∂P, Tendsto (fun t => occupation X (Set.indicator {st 0} 1) t ω / t) atTop
        (𝓝 (Real.exp (-(k₁ / k₂)))) := by
  have hc : ∀ s, 0 < cBD k₁ k₂ s := fun _ => div_pos hk₁ hk₂
  have hκ : ∀ r, 0 ≤ kBD k₁ k₂ r := fun r => by
    fin_cases r
    · exact hk₁.le
    · exact hk₂.le
  obtain ⟨hpr, hlim⟩ := ergodic_of_isComplexBalanced hκ (isComplexBalanced_birthDeath hk₂) hc
    hX hnonexp htransfer hinit hreg
  refine ⟨hpr, ?_⟩
  have hB : ∀ x, |Set.indicator {st 0} (1 : (Unit → ℕ) → ℝ) x| ≤ 1 := fun x => by
    by_cases h : x = st 0 <;> simp [Set.indicator, h]
  -- the stationary mean of the indicator, from the definitions
  have hmean : ∑' x, poissonWeight (cBD k₁ k₂) x * Set.indicator {st 0} 1 x =
      Real.exp (-(k₁ / k₂)) := by
    rw [tsum_eq_single (st 0) fun x hx => by simp [Set.indicator, hx]]
    simp [poissonWeight_birthDeath]
  rw [← hmean]
  exact hlim _ 1 hB

/-! ### A one-state instance: the hypotheses are jointly satisfiable -/

section OneState

/-- The empty network on no species: its only state is the empty count vector. -/
def emptyNet : ReactionNetwork Empty Empty := ⟨Empty.elim, Empty.elim⟩

/-- The only state. -/
def emptyState : Empty → ℕ := Empty.elim

/-- The constant chain on the one-point probability space. -/
def emptyChain : ℝ → Unit → (Empty → ℕ) := fun _ _ => emptyState

/-- Regeneration at the integer times. -/
def emptyTimes : ℕ → Unit → ℝ := fun k _ => k

theorem unit_fun_eq {β : Type*} (g : Unit → β) : g = fun _ => g () :=
  funext fun u => by cases u; rfl

theorem cycleLength_emptyTimes (k : ℕ) : cycleLength emptyTimes k = fun _ => 1 := by
  funext u
  simp [cycleLength, emptyTimes]

theorem cycleReward_emptyChain (f : (Empty → ℕ) → ℝ) (k : ℕ) :
    cycleReward emptyChain emptyTimes f k = fun _ => f emptyState := by
  funext u
  simp [cycleReward, emptyChain, emptyTimes]

theorem isRegenerative_emptyChain :
    IsRegenerative (Measure.dirac ()) emptyChain emptyTimes emptyState where
  nonneg _ := by simp [emptyTimes]
  strictMono _ := Nat.strictMono_cast
  mem _ _ := Subsingleton.elim _ _
  indep_length i j _ := by
    simp only [Function.onFun, cycleLength_emptyTimes]
    exact indepFun_const_left _ _
  identDistrib_length k := by
    rw [cycleLength_emptyTimes, cycleLength_emptyTimes]
    exact IdentDistrib.refl measurable_const.aemeasurable
  indep_reward f _ _ i j _ := by
    simp only [Function.onFun, cycleReward_emptyChain]
    exact indepFun_const_left _ _
  identDistrib_reward f _ _ k := by
    rw [cycleReward_emptyChain, cycleReward_emptyChain]
    exact IdentDistrib.refl measurable_const.aemeasurable
  integrable_sojourn := by
    rw [cycleReward_emptyChain]
    exact integrable_const _

/-- Any two probability measures on a subsingleton space agree. -/
theorem measure_eq_of_subsingleton {α : Type*} [MeasurableSpace α] [Subsingleton α]
    {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : μ = ν := by
  ext s _
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  · have : s = Set.univ := Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
    simp [this]

/-- Every hypothesis of `ergodic_of_isComplexBalanced` holds for the one-state chain (with
`c` the empty family), so its conclusion is available: positive recurrence and time averages
converging to the value at the single state. -/
theorem ergodic_emptyNet (c : Empty → ℝ) :
    IsPositiveRecurrent (Measure.dirac ()) emptyTimes ∧
      ∀ f : (Empty → ℕ) → ℝ, ∀ B, (∀ x, |f x| ≤ B) →
        ∀ᵐ ω ∂(Measure.dirac ()), Tendsto (fun t => occupation emptyChain f t ω / t) atTop
          (𝓝 (∑' x, poissonWeight c x * f x)) := by
  have hcb : emptyNet.IsComplexBalanced (fun r => r.elim) c := fun z => by simp
  have hlaw : IsProbabilityMeasure (countLaw (poissonWeight c)) :=
    isProbabilityMeasure_countLaw (poissonWeight_nonneg fun s => s.elim)
      (hasSum_poissonWeight fun s => s.elim)
  refine ergodic_of_isComplexBalanced (X := emptyChain) (P := Measure.dirac ())
    (fun r => r.elim) hcb (fun s => s.elim) measurable_const
    (ae_of_all _ fun _ t => ⟨0, by rintro _ ⟨s, -, rfl⟩; simp⟩)
    (fun _ p _ _ _ h0 _ _ => h0) measure_eq_of_subsingleton isRegenerative_emptyChain

end OneState

/-! ### `∅ → A`, `2A → ∅`: not complex balanced, no product form -/

section NotComplexBalanced

/-- Reaction `0` is `∅ → A`, reaction `1` is `2A → ∅`. -/
def birthPair : ReactionNetwork Unit (Fin 2) where
  src := ![st 0, st 2]
  prod := ![st 1, st 0]

@[simp] theorem birthPair_src_zero : birthPair.src 0 = st 0 := rfl
@[simp] theorem birthPair_src_one : birthPair.src 1 = st 2 := rfl
@[simp] theorem birthPair_prod_zero : birthPair.prod 0 = st 1 := rfl
@[simp] theorem birthPair_prod_one : birthPair.prod 1 = st 0 := rfl

@[simp] theorem st_sub_add (a b d : ℕ) : st a - st b + st d = st (a - b + d) := rfl

/-- No concentration is complex balanced when `k₁ ≠ 0`: the complex `A` is produced (by
`∅ → A`) but never consumed. -/
theorem not_isComplexBalanced_birthPair {k₁ k₂ : ℝ} (hk₁ : k₁ ≠ 0) (c : Unit → ℝ) :
    ¬ birthPair.IsComplexBalanced ![k₁, k₂] c := by
  intro h
  have := h (st 1)
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_two] at this
  simp [st_eq_iff, ReactionNetwork.rate, st] at this
  exact hk₁ this.symm

/-- No Poisson law solves the master equation when `k₁ ≠ 0`: at the states `0` and `1` the
balance equations read `c² k₂ = k₁` and `k₁ + c³ k₂ = c k₁`, which force `k₁ = 0`. -/
theorem not_isStationaryMasterSolution_birthPair {k₁ k₂ : ℝ} (hk₁ : k₁ ≠ 0) (c : Unit → ℝ) :
    ¬ IsStationaryMasterSolution birthPair ![k₁, k₂] (poissonWeight c) := by
  intro h
  have h0 := h (st 0)
  have h1 := h (st 1)
  simp only [Finset.sum_filter, Fin.sum_univ_two, propensity, birthPair_src_zero,
    birthPair_src_one, birthPair_prod_zero, birthPair_prod_one, st_le_iff] at h0 h1
  simp [poissonWeight, st, unfire, Nat.descFactorial, Nat.factorial] at h0 h1
  have he : Real.exp (-c ()) ≠ 0 := (Real.exp_pos _).ne'
  apply hk₁
  have e0 : c () ^ 2 * k₂ = k₁ := by
    apply mul_left_cancel₀ he
    linear_combination -h0
  have e1 : k₁ + c () ^ 3 * k₂ = c () * k₁ := by
    apply mul_left_cancel₀ he
    linear_combination -h1
  linear_combination e1 - c () * e0

end NotComplexBalanced

/-! ### `2A → 3A`: explosive, no ergodicity claimed -/

section Explosive

/-- The autocatalytic network `2A → 3A`. -/
def autocat : ReactionNetwork Unit Unit where
  src := fun _ => st 2
  prod := fun _ => st 3

theorem propensity_autocat (k : ℝ) (n : ℕ) :
    propensity autocat (fun _ => k) () (st (n + 2)) = k * ((n + 2) * (n + 1)) := by
  simp [propensity, autocat, st]
  left
  ring

/-- The explosion sum: the mean holding times `1 / λ(n)` of the pure-birth chain from `2` on
add up to `1 / k < ∞`, Reuter's criterion for explosion of a pure-birth chain (the chain
reaches infinity in finite expected time). -/
theorem hasSum_inv_propensity_autocat {k : ℝ} (hk : 0 < k) :
    HasSum (fun n : ℕ => 1 / propensity autocat (fun _ => k) () (st (n + 2))) (1 / k) := by
  have htel : HasSum (fun n : ℕ => 1 / (((n : ℝ) + 2) * ((n : ℝ) + 1))) 1 := by
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => by positivity)]
    have hps : ∀ N : ℕ, ∑ n ∈ Finset.range N, 1 / (((n : ℝ) + 2) * ((n : ℝ) + 1)) =
        1 - 1 / ((N : ℝ) + 1) := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        field_simp
        ring
    simp only [hps]
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_sub (1 : ℝ)
  have := htel.mul_left (1 / k)
  rw [mul_one] at this
  refine this.congr_fun fun n => ?_
  rw [propensity_autocat]
  field_simp

/-- `2A → 3A` has no positive complex-balanced concentration: the complex `2A` is consumed but
never produced. -/
theorem not_isComplexBalanced_autocat {k : ℝ} (hk : 0 < k) {c : Unit → ℝ} (hc : 0 < c ()) :
    ¬ autocat.IsComplexBalanced (fun _ => k) c := by
  intro h
  have := h (st 2)
  simp [autocat, st_eq_iff, ReactionNetwork.rate, st] at this
  rcases this with h1 | h1
  · exact hk.ne' h1
  · exact hc.ne' h1

/-- No Poisson law with `c > 0` solves the master equation of `2A → 3A`: the state `2` has
outflow `2 k π_c(2) > 0` and no inflow. -/
theorem not_isStationaryMasterSolution_autocat {k : ℝ} (hk : 0 < k) {c : Unit → ℝ}
    (hc : 0 < c ()) : ¬ IsStationaryMasterSolution autocat (fun _ => k) (poissonWeight c) := by
  intro h
  have h2 := h (st 2)
  have hpos : 0 < poissonWeight c (st 2) := poissonWeight_pos (fun _ => hc) _
  have hin : ∑ r ∈ Finset.univ.filter (fun r : Unit => autocat.prod r ≤ st 2),
      poissonWeight c (unfire autocat r (st 2)) *
        propensity autocat (fun _ => k) r (unfire autocat r (st 2)) = 0 :=
    Finset.sum_eq_zero fun r hr => by simp [autocat, st_le_iff] at hr
  have hout : poissonWeight c (st 2) * ∑ r, propensity autocat (fun _ => k) r (st 2) =
      poissonWeight c (st 2) * (k * 2) := by
    congr 1
    simp [propensity, autocat, st, Nat.descFactorial]
  rw [hin, hout] at h2
  have : 0 < poissonWeight c (st 2) * (k * 2) := by positivity
  linarith

/-- A path that blows up before time `1` (it takes the value `⌊1 / (1 - t)⌋` on `[0, 1)`)
violates `NoExplosion`, so that hypothesis is a real restriction. -/
theorem not_noExplosion_blowUp :
    ¬ NoExplosion (Measure.dirac ())
      (fun t (_ : Unit) => if t < 1 then st ⌊1 / (1 - t)⌋₊ else st 0) := by
  intro h
  obtain ⟨_, hω⟩ := h.exists
  obtain ⟨M, hM⟩ := hω 1
  have hM' : (0 : ℝ) ≤ M + 1 := by
    have := hM ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
    have h0 : (0 : ℕ) ≤ M := Nat.zero_le _
    positivity
  set s : ℝ := 1 - 1 / ((M : ℝ) + 2) with hs
  have hs1 : s < 1 := by rw [hs]; have : (0 : ℝ) < 1 / ((M : ℝ) + 2) := by positivity
                         linarith
  have hs0 : 0 ≤ s := by
    rw [hs, sub_nonneg, div_le_one (by positivity)]
    have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hval : ⌊(1 - s)⁻¹⌋₊ = M + 2 := by
    rw [hs, sub_sub_cancel, one_div, inv_inv]
    exact_mod_cast Nat.floor_natCast (M + 2)
  have := hM ⟨s, ⟨hs0, hs1.le⟩, rfl⟩
  simp [hs1, hval, st] at this

end Explosive

#print axioms ergodic_birthDeath
#print axioms ergodic_emptyNet
#print axioms not_isStationaryMasterSolution_birthPair
#print axioms not_noExplosion_blowUp
#print axioms isStationaryMasterSolution_poissonWeight
#print axioms isPositiveRecurrent_of_stationary
#print axioms ergodic_of_isComplexBalanced

end MathlibExtTest.Biology.Dynamics.StochasticCRNErgodicity
