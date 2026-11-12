/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem.Markov
public import MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem.Fixation

/-!
# Tests for the Markov property of the neutral Wright–Fisher realization

Each public declaration is exercised on the constructed realization (no process is supplied by
the caller): the appended-time chain identity on the neutral kernel, two-time and one-time
finite-dimensional laws, the Markov property at an interior initial frequency for `s < t` and
for `s = t`, its integrated form, and the martingale problem, which feeds the neutral fixation
probability of `NeutralMartingaleProblem.Fixation`.
-/

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem.Markov

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ProbabilityTheory unitInterval

open MathlibExt.Probability.MarkovSemigroupProjective
open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralWrightFisherRaw
open MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisherSemigroup
open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem
open MathlibExt.Biology.PopulationGenetics.Diffusion (KimuraFixationProcess.IsWrightFisherSolution)

/-- The interior initial frequency `1/2`. -/
noncomputable def xHalf : I := ⟨1 / 2, by constructor <;> norm_num⟩

/-- The identity test function on `[0, 1]`. -/
def gId : C(I, ℝ) := ⟨fun y => (y : ℝ), continuous_subtype_val⟩

/-! Appending one time to a chain law, on the neutral kernel, with unordered times. -/

example :
    (finiteChainLaw neutralKernel xHalf 0 (Fin.snoc ![3, 1] 2)).map
        (fun z => (Fin.init z, z (Fin.last 2))) =
      finiteChainLaw neutralKernel xHalf 0 ![3, 1] ⊗ₘ
        (neutralKernel (2 - 1)).comap (fun w => w (Fin.last 1)) (measurable_pi_apply _) :=
  map_init_last_finiteChainLaw_snoc neutralKernel xHalf 0 ![3, 1] 2

/-! Finite-dimensional laws of the realization. -/

example :
    (rawMeasure xHalf).map (fun ω i => modifiedState xHalf (![1, 2] i) ω) =
      finiteChainLaw neutralKernel xHalf 0 ![1, 2] :=
  map_modifiedState_comp_eq_finiteChainLaw xHalf (by
    simp [Fin.strictMono_iff_lt_succ, Fin.forall_fin_one])

/-- With a single time the law is a single kernel step from the initial state. -/
example (t : ℝ≥0) :
    (rawMeasure xHalf).map (fun ω (_ : Fin 1) => modifiedState xHalf t ω) =
      finiteChainLaw neutralKernel xHalf 0 (fun _ : Fin 1 => t) :=
  map_modifiedState_comp_eq_finiteChainLaw xHalf (τ := fun _ : Fin 1 => t)
    (fun a b hab => absurd hab (by simp [Subsingleton.elim a b]))

/-! The Markov property. -/

example :
    (rawMeasure xHalf)[fun ω => gId (projIcc (0 : ℝ) 1 zero_le_one (modifiedProcess xHalf 2 ω)) |
        naturalFiltration xHalf 1] =ᵐ[rawMeasure xHalf]
      fun ω => wfSemigroup ((2 : ℝ≥0) - (1 : ℝ≥0) : ℝ) gId
        (projIcc (0 : ℝ) 1 zero_le_one (modifiedProcess xHalf 1 ω)) :=
  condExp_modifiedProcess_eq_wfSemigroup xHalf (by norm_num) gId

/-- The boundary case `s = t`: the semigroup at time `0` is the identity. -/
example (s : ℝ≥0) (g : C(I, ℝ)) :
    (rawMeasure xHalf)[fun ω => g (projIcc (0 : ℝ) 1 zero_le_one (modifiedProcess xHalf s ω)) |
        naturalFiltration xHalf s] =ᵐ[rawMeasure xHalf]
      fun ω => g (projIcc (0 : ℝ) 1 zero_le_one (modifiedProcess xHalf s ω)) := by
  simpa [wfSemigroup_zero] using condExp_modifiedProcess_eq_wfSemigroup xHalf le_rfl g

/-- The Markov property in the exact hypothesis form of `isWrightFisherSolution_zero_of_markov`,
integrated over the whole space: `E[g (X_t)] = E[(P_{t-s} g) (X_s)]`. -/
example {s t : ℝ≥0} (hst : s ≤ t) (g : C(I, ℝ)) :
    ∫ ω, g (projIcc (0 : ℝ) 1 zero_le_one (modifiedProcess xHalf t ω)) ∂rawMeasure xHalf =
      ∫ ω, wfSemigroup ((t : ℝ) - s) g (projIcc (0 : ℝ) 1 zero_le_one (modifiedProcess xHalf s ω))
        ∂rawMeasure xHalf := by
  rw [← integral_condExp ((naturalFiltration xHalf).le s)]
  exact integral_congr_ae (condExp_modifiedProcess_eq_wfSemigroup xHalf hst g)

/-! The martingale problem, and the neutral fixation probability of the realization. -/

example : KimuraFixationProcess.IsWrightFisherSolution 0 (naturalFiltration xHalf)
    (rawMeasure xHalf) (modifiedProcess xHalf) :=
  isWrightFisherSolution_zero_modifiedProcess xHalf

/-- Started at the boundary state `0`, the realization also solves the martingale problem. -/
example : KimuraFixationProcess.IsWrightFisherSolution 0 (naturalFiltration 0)
    (rawMeasure 0) (modifiedProcess 0) :=
  isWrightFisherSolution_zero_modifiedProcess 0

/-- Started at `1/2`, the realization fixes the allele with probability `1/2`. -/
example :
    (rawMeasure xHalf).real {ω | ∃ t₀ : ℝ≥0, ∀ t ≥ t₀, modifiedProcess xHalf t ω = 1} = 1 / 2 :=
  measureReal_fixation_eq (isWrightFisherSolution_zero_modifiedProcess xHalf)
    (ae_of_all _ fun ω => modifiedProcess_zero xHalf ω)

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem.Markov
