/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.StochasticIntegral

@[expose] public section

open MeasureTheory Finset
open MathlibExt.Probability.Statistics.CountingProcess
open MathlibExt.Probability.Statistics.KaplanMeier

namespace MathlibExtTest.Probability.Statistics.StochasticIntegral

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}

/-! ### The stochastic integral and the jump formula -/

/-- A constant integrand `2` against the clock `Mₙ = n`: `(2 • M)₃ = 6`. -/
example (ω : Ω) : stochasticIntegral (fun _ _ => (2 : ℝ)) (fun n _ => (n : ℝ)) 3 ω = 6 := by
  simp [stochasticIntegral]; norm_num

/-- The jump formula on an explicit integrand and integrator. -/
example (ω : Ω) :
    stochasticIntegral (fun k _ => (k : ℝ)) (fun n _ => (n : ℝ) ^ 2) 3 ω -
      stochasticIntegral (fun k _ => (k : ℝ)) (fun n _ => (n : ℝ) ^ 2) 2 ω = 3 * (9 - 4) := by
  rw [stochasticIntegral_jump]; norm_num

/-- Associativity of the integral on a constant integrand. -/
example (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    stochasticIntegral (fun _ _ => (3 : ℝ)) (stochasticIntegral (fun _ _ => (2 : ℝ)) X) n ω =
      stochasticIntegral (fun _ _ => (6 : ℝ)) X n ω := by
  rw [stochasticIntegral_stochasticIntegral]; norm_num

/-- The martingale property applies to the compensated martingale of any integrable adapted
process, with the constant (predictable) integrand `1`. -/
example [IsFiniteMeasure μ] (N : ℕ → Ω → ℝ) (hN : StronglyAdapted ℱ N)
    (hint : ∀ n, Integrable (N n) μ) :
    Martingale (stochasticIntegral (fun _ _ => (1 : ℝ)) (martingalePart N ℱ μ)) ℱ μ :=
  martingale_stochasticIntegral_of_bdd (martingale_martingalePart hN hint)
    (.of_measurable_add_one stronglyMeasurable_const fun _ => stronglyMeasurable_const)
    fun _ => ⟨1, fun _ => by simp⟩

/-! ### Counting processes -/

/-- The clock `Nₙ = n` has unit jumps and is a counting process. -/
example : HasUnitJumps (fun n (_ : Ω) => (n : ℝ)) := fun n ω => Or.inr (by push_cast; ring)

example : IsCountingProcess (fun n (_ : Ω) => (n : ℝ)) :=
  HasUnitJumps.isCountingProcess (fun n ω => Or.inr (by push_cast; ring)) fun _ => by simp

/-- A process with a jump of size `2` (a tie) is a counting process without unit jumps. -/
example : IsCountingProcess (fun n (_ : Ω) => (2 * n : ℝ)) :=
  ⟨fun _ => by simp, fun n _ => ⟨2, by push_cast; ring⟩⟩

example [Nonempty Ω] : ¬ HasUnitJumps (fun n (_ : Ω) => (2 * n : ℝ)) := fun h => by
  rcases h 0 (Classical.arbitrary Ω) with h | h <;> norm_num at h

/-- **Fully predictable jumps carry no variance**: for the deterministic clock `Nₙ = n` the
compensator jumps by `1` at every step, and `⟨N - A⟩ = ∑ 1 · (1 - 1) = 0`. -/
example [IsFiniteMeasure μ] (n : ℕ) :
    predictableQuadraticVariation μ ℱ (martingalePart (fun n (_ : Ω) => (n : ℝ)) ℱ μ) n =ᵐ[μ]
      0 := by
  have h := HasUnitJumps.predictableQuadraticVariation_martingalePart (μ := μ) (ℱ := ℱ)
    (N := fun n (_ : Ω) => (n : ℝ)) (fun n ω => Or.inr (by push_cast; ring))
    (fun _ => stronglyMeasurable_const) (fun _ => integrable_const _) n
  refine h.trans (ae_of_all _ fun ω => ?_)
  have hc : ∀ k : ℕ, μ[(fun (_ : Ω) => (k : ℝ) + 1) - fun _ => (k : ℝ) | ℱ k] =
      fun _ => (1 : ℝ) := fun k => by
    have : ((fun (_ : Ω) => (k : ℝ) + 1) - fun _ => (k : ℝ)) = fun _ => 1 := by
      funext; simp
    rw [this, condExp_const (ℱ.le k)]
  simp [hc]

/-! ### Nelson–Aalen: vanishing risk -/

/-- **Vanishing risk**: with nobody ever at risk, the Nelson–Aalen process stays at `0` even if
the counting process keeps jumping. -/
example (n : ℕ) (ω : Ω) :
    nelsonAalenProcess (fun n (_ : Ω) => (n : ℝ)) (fun _ _ => 0) n ω = 0 := by
  simp [nelsonAalenProcess, stochasticIntegral]

/-- ... and so does the restricted hazard, while the Aalen compensator `∫ 0 dα` vanishes. -/
example (α : ℕ → ℝ) (n : ℕ) (ω : Ω) :
    restrictedHazard (fun _ (_ : Ω) => (0 : ℝ)) α n ω = 0 ∧
      aalenCompensator (fun _ (_ : Ω) => (0 : ℝ)) α n ω = 0 := by
  simp [restrictedHazard, aalenCompensator, stochasticIntegral]

/-- With a constant risk set of size `4` and one death per step, `Â₂ = 1/4 + 1/4`. -/
example (ω : Ω) :
    nelsonAalenProcess (fun n (_ : Ω) => (n : ℝ)) (fun _ _ => 4) 2 ω = 1 / 2 := by
  simp [nelsonAalenProcess, stochasticIntegral]; norm_num

/-- The Nelson–Aalen martingale representation, instantiated. -/
example (N Y : ℕ → Ω → ℝ) (α : ℕ → ℝ) (ω : Ω) :
    nelsonAalenProcess N Y 3 ω - restrictedHazard Y α 3 ω =
      stochasticIntegral (fun k ω => (Y k ω)⁻¹)
        (fun k ω => N k ω - aalenCompensator Y α k ω) 3 ω :=
  nelsonAalenProcess_sub_restrictedHazard N Y α 3 ω

/-! ### Product integrals, Duhamel, Kaplan–Meier -/

/-- `𝒫(1 - dA)₂ = (1 - 1/2)² = 1/4` for `Aₙ = n / 2`. -/
example : prodIntegral (fun n => (n : ℝ) / 2) 2 = 1 / 4 := by
  simp [prodIntegral, prod_range_succ]; norm_num

/-- A hazard jump of size `1` kills the product integral: the boundary excluded by
`prodIntegral_ne_zero`. -/
example : prodIntegral (fun n => (n : ℝ)) 1 = 0 := by simp [prodIntegral]

/-- Duhamel's equation, instantiated: the two forms on explicit sequences. -/
example : prodIntegral (fun n => (n : ℝ) / 2) 2 - prodIntegral (fun n => (n : ℝ) / 3) 2 =
    -∑ k ∈ range 2, prodIntegral (fun n => (n : ℝ) / 2) k *
      (((k + 1 : ℕ) : ℝ) / 2 - (k : ℝ) / 2 - (((k + 1 : ℕ) : ℝ) / 3 - (k : ℝ) / 3)) *
        ∏ i ∈ Ico (k + 1) 2, (1 - (((i + 1 : ℕ) : ℝ) / 3 - (i : ℝ) / 3)) :=
  prodIntegral_sub_prodIntegral _ _ 2

example : prodIntegral (fun n => (n : ℝ) / 2) 2 / prodIntegral (fun n => (n : ℝ) / 3) 2 - 1 =
    -∑ k ∈ range 2, prodIntegral (fun n => (n : ℝ) / 2) k /
      prodIntegral (fun n => (n : ℝ) / 3) (k + 1) *
        (((k + 1 : ℕ) : ℝ) / 2 - (k : ℝ) / 2 - (((k + 1 : ℕ) : ℝ) / 3 - (k : ℝ) / 3)) :=
  prodIntegral_div_prodIntegral_sub_one _ _ fun k _ => by push_cast; rw [← sub_div]; norm_num

/-- With nobody at risk the Kaplan–Meier process stays at `1`. -/
example (n : ℕ) (ω : Ω) :
    kaplanMeierProcess (fun n (_ : Ω) => (n : ℝ)) (fun _ _ => 0) n ω = 1 := by
  induction n with
  | zero => simp [kaplanMeierProcess]
  | succ n ih => rw [kaplanMeierProcess_succ, ih]; simp

/-- With a constant risk set of size `4` and one death per step, `Ŝ₂ = (3/4)²`. -/
example (ω : Ω) : kaplanMeierProcess (fun n (_ : Ω) => (n : ℝ)) (fun _ _ => 4) 2 ω = 9 / 16 := by
  rw [kaplanMeierProcess_succ, kaplanMeierProcess_succ]
  simp [kaplanMeierProcess]; norm_num

/-- The Kaplan–Meier integrand and remainder: with nobody at risk at step `k`, the integrand is
`0` and the remainder is `Ŝ_{k-1} / S_k`. -/
example (N : ℕ → Ω → ℝ) (α : ℕ → ℝ) (k : ℕ) (ω : Ω) :
    kaplanMeierIntegrand N (fun _ _ => 0) α k ω = 0 ∧
      kaplanMeierRemainder N (fun _ _ => 0) α k ω =
        kaplanMeierProcess N (fun _ _ => 0) (k - 1) ω / prodIntegral α k := by
  simp [kaplanMeierIntegrand, kaplanMeierRemainder]

/-- The Kaplan–Meier martingale representation, instantiated. -/
example (N Y : ℕ → Ω → ℝ) (ω : Ω) :
    kaplanMeierProcess N Y 2 ω / prodIntegral (fun n => (n : ℝ) / 2) 2 - 1 =
      -stochasticIntegral (kaplanMeierIntegrand N Y fun n => (n : ℝ) / 2)
          (fun k ω => N k ω - aalenCompensator Y (fun n => (n : ℝ) / 2) k ω) 2 ω +
        stochasticIntegral (kaplanMeierRemainder N Y fun n => (n : ℝ) / 2)
          (fun k _ => (k : ℝ) / 2) 2 ω :=
  kaplanMeierProcess_div_sub_one N Y (fun k => by push_cast; rw [← sub_div]; norm_num) 2 ω

/-! ### Bridge to grouped data -/

/-- Two observation times `1 < 2`; at time `1` one death and one censoring, at time `2` one death.
The numbers at risk are `3` and `1`. -/
noncomputable def sample : CensoredData 2 where
  time := ![1, 2]
  strictMono_time := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  deaths := ![1, 1]
  censored := ![1, 0]

/-- The grid processes of `sample`: one death at each of the first two steps, risk sets `3, 1`. -/
example (ω : Ω) : gridDeaths (Ω := Ω) sample 2 ω = 2 ∧ gridAtRisk (Ω := Ω) sample 1 ω = 3 ∧
    gridAtRisk (Ω := Ω) sample 2 ω = 1 := by
  simp [gridDeaths, gridAtRisk, sample, sum_range_succ, CensoredData.atRisk, Finset.sum_filter,
    Fin.sum_univ_two]
  norm_num

/-- The grouped Nelson–Aalen estimate of `sample` at the last time is `1/3 + 1/1 = 4/3`, read off
the grid stochastic integral. -/
example (ω : Ω) : sample.nelsonAalen (sample.time 1) = 4 / 3 := by
  rw [nelsonAalen_time_eq_nelsonAalenProcess sample 1 ω]
  simp [nelsonAalenProcess, stochasticIntegral, sum_range_succ, gridDeaths, gridAtRisk, sample,
    CensoredData.atRisk, Finset.sum_filter, Fin.sum_univ_two]
  norm_num

/-- ... and its Kaplan–Meier estimate is `(1 - 1/3)(1 - 1) = 0`. -/
example (ω : Ω) : sample.kmSurvival (sample.time 1) = 0 := by
  rw [kmSurvival_time_eq_kaplanMeierProcess sample 1 ω]
  simp [kaplanMeierProcess, prodIntegral, prod_range_succ, nelsonAalenProcess, stochasticIntegral,
    sum_range_succ, gridDeaths, gridAtRisk, sample, CensoredData.atRisk, Finset.sum_filter,
    Fin.sum_univ_two]

/-! ### A concrete non-predictable integrand that breaks the martingale property -/

/-- On `Bool`, nothing is known at time `0` and everything from time `1` on. -/
def boolFiltration : Filtration ℕ (inferInstance : MeasurableSpace Bool) where
  seq n := if n = 0 then ⊥ else ⊤
  mono' i j hij := by
    simp only
    split_ifs <;> simp_all
  le' _ := fun _ _ => MeasurableSet.of_discrete

/-- One event at step `1`, on the outcome `true`. -/
noncomputable def boolN : ℕ → Bool → ℝ := fun n ω => if n = 0 then 0 else if ω then 1 else 0

/-- Integrating the anticipating integrand `ΔN` against the compensated martingale `N - A` (here
`ΔA₁ = 1/2`) does not give a martingale: `HasUnitJumps.not_martingale_of_unpredicted_jump` is not
vacuous. -/
example : ¬ Martingale (stochasticIntegral (fun k ω => boolN k ω - boolN (k - 1) ω)
    (martingalePart boolN boolFiltration Measure.count)) boolFiltration Measure.count := by
  have hN : HasUnitJumps boolN := fun n ω => by
    cases n <;> cases ω <;> simp [boolN]
  refine hN.not_martingale_of_unpredicted_jump (fun n => Integrable.of_finite) (k := 0) ?_
  have hF : (boolFiltration 0 : MeasurableSpace Bool) = ⊥ := rfl
  have hc : (Measure.count : Measure Bool)[boolN (0 + 1) - boolN 0 | boolFiltration 0] =
      fun _ => 1 / 2 := by
    rw [hF, condExp_bot']
    funext ω
    have h2 : (Measure.count : Measure Bool).real Set.univ = 2 := by
      rw [Measure.real, Measure.count_univ]
      simp
    rw [h2, integral_fintype Integrable.of_finite]
    simp [boolN, Measure.real]
  rw [hc]
  have : {ω : Bool | boolN (0 + 1) ω - boolN 0 ω = 1 ∧ (fun _ => (1 / 2 : ℝ)) ω < 1} =
      {true} := by
    ext ω; cases ω <;> simp [boolN]
    norm_num
  rw [this]
  simp

end MathlibExtTest.Probability.Statistics.StochasticIntegral
