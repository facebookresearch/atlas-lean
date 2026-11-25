/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Admixture.RootNonIdentifiability
import Domains.Biology.PopulationGenetics.Admixture.ConditionalNegDef

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

/-! ## Part 3: acceptance and boundary examples -/

section Acceptance

/-- Populations `0 = Mx`, `1 = A`, `2 = B`, `3 = X`; edges `0 = a`, `1 = b`, `2 = c`, then the
private edges of `A`, `B`, `X`. `Mx = ½ (A + a) + ½ (B + b) + c`. -/
noncomputable def accW : Fin 4 → Fin 6 → ℝ :=
  ![![1 / 2, 1 / 2, 1, 1 / 2, 1 / 2, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 1]]

example : accW 0 = (1 / 2 : ℝ) • (accW 1 + Pi.single 0 1) +
    (1 - 1 / 2 : ℝ) • (accW 2 + Pi.single 1 1) + Pi.single 2 1 := by
  funext e
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  fin_cases e <;> simp [accW] <;> norm_num

-- Acceptance "two different (ℓa, ℓb, ℓc) give equal f2 matrix": `(1, 1, 1)` and `(2, 2, 1/2)`
-- (mixed drift `3/2` at `α = 1/2` for both), all other edges of length `1`. Realized models; the
-- sixteen `f2` entries are computed directly (independently of Part 2).
example : ∃ (Ω₁ : Type) (_ : MeasurableSpace Ω₁) (μ₁ : Measure Ω₁) (_ : IsProbabilityMeasure μ₁)
    (M₁ : DriftModel μ₁ (Fin 6) (Fin 4)) (Ω₂ : Type) (_ : MeasurableSpace Ω₂) (μ₂ : Measure Ω₂)
    (_ : IsProbabilityMeasure μ₂) (M₂ : DriftModel μ₂ (Fin 6) (Fin 4)),
      M₁.weight = accW ∧ M₂.weight = accW ∧ M₁.len ≠ M₂.len ∧
      (M₁.len 0, M₁.len 1, M₁.len 2) = (1, 1, 1) ∧ (M₂.len 0, M₂.len 1, M₂.len 2) = (2, 2, 1 / 2) ∧
      ∀ Y Z, f2 μ₁ M₁.freq Y Z = f2 μ₂ M₂.freq Y Z := by
  obtain ⟨Ω₁, h₁, μ₁, hμ₁, M₁, hw₁, hl₁⟩ :=
    MathlibExt.Biology.PopulationGenetics.Admixture.exists_driftModel accW ![1, 1, 1, 1, 1, 1]
      (by intro e; fin_cases e <;> norm_num)
  obtain ⟨Ω₂, h₂, μ₂, hμ₂, M₂, hw₂, hl₂⟩ :=
    MathlibExt.Biology.PopulationGenetics.Admixture.exists_driftModel accW
      ![2, 2, 1 / 2, 1, 1, 1] (by intro e; fin_cases e <;> norm_num)
  refine ⟨Ω₁, h₁, μ₁, hμ₁, M₁, Ω₂, h₂, μ₂, hμ₂, M₂, hw₁, hw₂, ?_, by simp [hl₁],
    by simp [hl₂], ?_⟩
  · intro h
    have := congrFun h 0
    rw [hl₁, hl₂] at this
    norm_num at this
  · intro Y Z
    rw [M₁.f2_freq, M₂.f2_freq, hw₁, hw₂, hl₁, hl₂]
    fin_cases Y <;> fin_cases Z <;> simp [accW, Fin.sum_univ_succ] <;> norm_num

-- The same instance through Part 2 (`Mx` is the only population on `a`, `b`, `c`).
example {Ω : Type} {m : MeasurableSpace Ω} {μ : Measure Ω} (M : DriftModel μ (Fin 6) (Fin 4))
    (hw : M.weight = accW) (hl : M.len = ![1, 1, 1, 1, 1, 1]) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω') (_ : IsProbabilityMeasure μ')
      (M' : DriftModel μ' (Fin 6) (Fin 4)), M'.weight = M.weight ∧ M'.len 0 = 2 ∧
        M'.len 1 = 2 ∧ M'.len 2 = 1 / 2 ∧
        ∀ W X Y Z, f4 μ' M'.freq W X Y Z = f4 μ M.freq W X Y Z := by
  have hwM : M.weight 0 = (1 / 2 : ℝ) • (M.weight 1 + Pi.single 0 1) +
      (1 - 1 / 2 : ℝ) • (M.weight 2 + Pi.single 1 1) + Pi.single 2 1 := by
    rw [hw]
    funext e
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    fin_cases e <;> simp [accW] <;> norm_num
  have hrest : ∀ Y, Y ≠ 0 → ∀ e ∈ ({0, 1, 2} : Finset (Fin 6)), M.weight Y e = 0 := by
    intro Y hY e he
    rw [hw]
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    fin_cases Y
    · exact absurd rfl hY
    all_goals rcases he with rfl | rfl | rfl <;> simp [accW]
  obtain ⟨Ω', h', μ', hμ', M', hw', la, lb, lc, -, hf⟩ :=
    exists_mixedDrift_family_f4_eq (s := 1) (t := 1) M (Mx := 0) (A := 1) (B := 2)
      (a := 0) (b := 1) (c := 2) (by decide) (by decide) (by decide) hwM (hrest 1 (by decide))
      (hrest 2 (by decide)) hrest (by rw [hl]; norm_num) (by rw [hl]; norm_num)
      (by rw [hl]; norm_num)
  refine ⟨Ω', h', μ', hμ', M', hw', ?_, ?_, ?_, hf⟩
  · rw [la, hl]; norm_num
  · rw [lb, hl]; norm_num
  · rw [lc, hl]; norm_num

-- `α` is identified in this instance: the references `A` and `B` avoid `a, b, c` and have
-- distinct contrasts `-f2 A B ≠ f2 A B` because `f2 A B = 2 ≠ 0`.
example {Ω : Type} {m : MeasurableSpace Ω} {μ : Measure Ω} (M : DriftModel μ (Fin 6) (Fin 4))
    (hw : M.weight = accW) (hl : M.len = ![1, 1, 1, 1, 1, 1]) :
    f2 μ M.freq 1 1 - f2 μ M.freq 2 1 ≠ f2 μ M.freq 1 2 - f2 μ M.freq 2 2 := by
  simp only [M.f2_freq, hw, hl]
  simp [accW, Fin.sum_univ_succ]
  norm_num

-- Boundary: within nonnegative lengths and `0 < α < 1`, zero mixed drift pins all three lengths
-- to `0` (the family collapses to a point); positive mixed drift leaves a two-dimensional
-- triangle, e.g. the two triples above.
example {α la lb lc : ℝ} (h0 : 0 < α) (h1 : α < 1) (ha : 0 ≤ la) (hb : 0 ≤ lb) (hc : 0 ≤ lc)
    (hD : mixedDrift α la lb lc = 0) : la = 0 ∧ lb = 0 ∧ lc = 0 := by
  unfold mixedDrift at hD
  have hα2 : 0 < α ^ 2 := by positivity
  have h1α : 0 < 1 - α := by linarith
  have hβ2 : 0 < (1 - α) ^ 2 := by positivity
  have e1 : 0 ≤ α ^ 2 * la := by positivity
  have e2 : 0 ≤ (1 - α) ^ 2 * lb := by positivity
  refine ⟨?_, ?_, by linarith⟩
  · nlinarith
  · nlinarith

end Acceptance

end MathlibExtTest.Biology.PopulationGenetics.Admixture.RootNonIdentifiability
