/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Admixture.RootNonIdentifiability
import MathlibExt.Biology.PopulationGenetics.Admixture.ConditionalNegDef

/-!
# Tests for root and admixture-adjacent length non-identifiability

The examples restate the two non-identifiability theorems and exhibit two
rootings with equal `f2` matrices and distinct admixture-adjacent length
triples with the same positive `f2`.
-/

@[expose] public section

open MeasureTheory MathlibExt.Biology.PopulationGenetics.FStatistics
  MathlibExt.Biology.PopulationGenetics.TreeFStatistics
open MathlibExt.Biology.PopulationGenetics.Admixture (exists_driftModel)
open scoped symmDiff

namespace MathlibExtTest.Biology.PopulationGenetics.Admixture.RootNonIdentifiability

universe u

example {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {E P : Type u} [Fintype E]
    (M : DriftModel μ E P) {e0 : E} (hconst : ∀ X Y, M.weight X e0 = M.weight Y e0)
    {t : ℝ} (ht : 0 ≤ t) (hne : t ≠ M.len e0) :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (μ' : Measure Ω') (_ : IsProbabilityMeasure μ')
      (M' : DriftModel μ' E P), M'.weight = M.weight ∧ M'.len e0 = t ∧ M'.len ≠ M.len ∧
        ∀ A B C D, f4 μ' M'.freq A B C D = f4 μ M.freq A B C D :=
  M.exists_len_ne_f4_eq_of_weight_const hconst ht hne

example {Ω Ω' P E : Type*} {m : MeasurableSpace Ω} {m' : MeasurableSpace Ω'} {μ : Measure Ω}
    {μ' : Measure Ω'} [Fintype E] [DecidableEq E] (M : DriftModel μ E P)
    (M' : DriftModel μ' E P) {Mx A B X : P} {a b c : E} {α : ℝ} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c)
    (hwM : M.weight Mx = α • (M.weight A + Pi.single a 1) +
      (1 - α) • (M.weight B + Pi.single b 1) + Pi.single c 1)
    (hw : M'.weight = M.weight)
    (hlen : ∀ e, e ∉ ({a, b, c} : Finset E) → M'.len e = M.len e)
    (hmix : mixedDrift α (M'.len a) (M'.len b) (M'.len c) =
      mixedDrift α (M.len a) (M.len b) (M.len c))
    (hA : ∀ e ∈ ({a, b, c} : Finset E), M.weight A e = 0)
    (hB : ∀ e ∈ ({a, b, c} : Finset E), M.weight B e = 0)
    (hX : ∀ e ∈ ({a, b, c} : Finset E), M.weight X e = 0) :
    f2 μ' M'.freq Mx X = f2 μ M.freq Mx X :=
  f2_eq_of_mixedDrift_eq M M' hab hac hbc hwM hw hlen hmix hA hB hX

/-- Quartet tree rooted at the left internal node; edges
`(ea, eb, eint, ec, ed)`, populations `A=0, B=1, C=2, D=3`. -/
def wRootLeftQuartet : Fin 4 → Fin 5 → ℝ :=
  ![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 1, 0], ![0, 0, 1, 0, 1]]

/-- The same unrooted quartet rooted at the right internal node. Lineages
differ from `wRootLeftQuartet` by the symmetric difference `{eint}`. -/
def wRootRightQuartet : Fin 4 → Fin 5 → ℝ :=
  ![![1, 0, 1, 0, 0], ![0, 1, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]

/-- Acceptance: two rootings with equal `f2` matrices exhibited, for every
choice of nonnegative edge lengths; the weight functions differ. -/
theorem two_rootings_f2_eq (len : Fin 5 → ℝ) (hlen : ∀ e, 0 ≤ len e) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (M : DriftModel μ (Fin 5) (Fin 4)) (Ω' : Type) (_ : MeasurableSpace Ω')
      (μ' : Measure Ω') (_ : IsProbabilityMeasure μ') (M' : DriftModel μ' (Fin 5) (Fin 4)),
        M.weight = wRootLeftQuartet ∧ M'.weight = wRootRightQuartet ∧ M.len = len ∧ M'.len = len ∧
        M.weight ≠ M'.weight ∧ ∀ X Y, f2 μ M.freq X Y = f2 μ' M'.freq X Y := by
  obtain ⟨Ω, hΩ, μ, hμ, M, hw, hl⟩ := exists_driftModel wRootLeftQuartet len hlen
  obtain ⟨Ω', hΩ', μ', hμ', M', hw', hl'⟩ := exists_driftModel wRootRightQuartet len hlen
  refine ⟨Ω, hΩ, μ, hμ, M, Ω', hΩ', μ', hμ', M', hw, hw', hl, hl', ?_, fun X Y => ?_⟩
  · rw [hw, hw']
    intro hcon
    have := congrFun (congrFun hcon 0) 2
    norm_num [wRootLeftQuartet, wRootRightQuartet] at this
  · rw [M.f2_freq, M'.f2_freq, hw, hw', hl, hl']
    fin_cases X <;> fin_cases Y <;>
      simp [wRootLeftQuartet, wRootRightQuartet, Fin.sum_univ_five]

/-- Distinct nonnegative admixture-adjacent length triples with the same
mixed drift, for the given `α`: `((1-α)², 0, 0)` and `(0, α², 0)` (distinct
for `0 < α < 1`, since `(1-α)² ≠ 0`). Pure algebra. -/
theorem mixedDrift_swap (α : ℝ) :
    mixedDrift α ((1 - α) ^ 2) 0 0 = mixedDrift α 0 (α ^ 2) 0 ∧
      mixedDrift α ((1 - α) ^ 2) 0 0 = α ^ 2 * (1 - α) ^ 2 := by
  simp only [mixedDrift]
  constructor <;> ring

/-- Exhibited admixture non-identifiability in the three-edge model:
populations `Mx=0, A=1, B=2, X=3` with weights `(α, 1-α, 1)` for `Mx` and `0`
for `A, B, X` (so `A`, `B` sit at the split points, with private edges of the
mixture components adjoined). The two length triples of `mixedDrift_swap`
give different lengths, the same weights and the same
`f2 Mx X = α² (1-α)² > 0`. -/
theorem mixedDrift_len_ne_f2_eq {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (M : DriftModel μ (Fin 3) (Fin 4)) (Ω' : Type) (_ : MeasurableSpace Ω')
      (μ' : Measure Ω') (_ : IsProbabilityMeasure μ') (M' : DriftModel μ' (Fin 3) (Fin 4)),
        M.weight = ![![α, 1 - α, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0]] ∧
        M'.weight = M.weight ∧ M.len = ![(1 - α) ^ 2, 0, 0] ∧ M'.len = ![0, α ^ 2, 0] ∧
        M.len ≠ M'.len ∧ f2 μ M.freq 0 3 = α ^ 2 * (1 - α) ^ 2 ∧
        f2 μ' M'.freq 0 3 = α ^ 2 * (1 - α) ^ 2 ∧ 0 < α ^ 2 * (1 - α) ^ 2 := by
  obtain ⟨Ω, hΩ, μ, hμ, M, hw, hl⟩ :=
    exists_driftModel ![![α, 1 - α, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0]] ![(1 - α) ^ 2, 0, 0]
      (by
        intro e
        fin_cases e <;> simp [sq_nonneg (1 - α)])
  obtain ⟨Ω', hΩ', μ', hμ', M', hw', hl'⟩ :=
    exists_driftModel ![![α, 1 - α, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0]] ![0, α ^ 2, 0]
      (by
        intro e
        fin_cases e <;> simp [sq_nonneg α])
  refine ⟨Ω, hΩ, μ, hμ, M, Ω', hΩ', μ', hμ', M', hw, by rw [hw', hw], hl, hl', ?_, ?_, ?_,
    by positivity⟩
  · intro hcon
    have h0 := congrFun hcon 0
    rw [hl, hl'] at h0
    simp only [Matrix.cons_val_zero] at h0
    have hne : (1 : ℝ) - α ≠ 0 := by linarith
    exact pow_ne_zero 2 hne h0
  · rw [M.f2_freq, hw, hl]
    simp [Fin.sum_univ_three]
  · rw [M'.f2_freq, hw', hl']
    simp [Fin.sum_univ_three]
    ring

/-- Endpoint `α = 0`: the first admixture edge is unused by the mixture
weights and the mixed drift does not see its length either. Endpoint
`α = 1`: symmetric. -/
example : mixedDrift 0 1 0 0 = 0 ∧ mixedDrift 1 0 1 0 = 0 := by
  simp [mixedDrift]

/-- Endpoint: with zero lengths the existential stem statement is not
applicable (`t ≠ len e0` fails at `t = 0`), and every `f4` vanishes. -/
example {Ω P E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [Fintype E]
    (M : DriftModel μ E P) (h0 : ∀ e, M.len e = 0) (A B C D : P) :
    f4 μ M.freq A B C D = 0 := by
  rw [M.f4_freq]
  exact Finset.sum_eq_zero fun e _ => by rw [h0 e]; ring

end MathlibExtTest.Biology.PopulationGenetics.Admixture.RootNonIdentifiability
