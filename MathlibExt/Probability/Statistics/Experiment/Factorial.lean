/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Experiment.Assignment
public import MathlibExt.Probability.Causality.CausalIdentification
public import MathlibExt.Probability.WeightLaw
import Mathlib.MeasureTheory.Integral.Pi

/-!
# 2x2 factorial designs: cell laws and unbiased contrasts

Complete randomization over four cells of fixed positive sizes; observed
main-effect and interaction contrasts are unbiased with no additivity
assumption. Cell sizes need not be equal.

Independent categorical assignment: each unit `i` goes to cell `c` with known probability
`π i c > 0`, independently across units (`bernoulliCell`, joint law
`Measure.pi fun i => bernoulliCell π i`). Realized cell sizes are random and a cell can be
empty, so the observed cell means are replaced by the inverse-probability-weighted
(Horvitz–Thompson) cell means `ipwCellMean`, `∑_{i : f i = c} Y i / (N π i c)`. These are unbiased
for the population cell means (`integral_ipwCellMean`), so the main-effect and interaction
contrasts built from them are unbiased too (`integral_ipwMainEffectA`, `integral_ipwMainEffectB`,
`integral_ipwInteractionAB`), with no additivity assumption and no nonempty-cell condition.

## Coding and normalization

Factors `A` and `B` each have a low level `0` and a high level `1`. Cell `c : Fin 4` is the
treatment combination `(a, b)` with `c = 2 a + b`, so cells `0, 1, 2, 3` are `(0, 0)`, `(0, 1)`,
`(1, 0)` and `(1, 1)`, and `m_ab` is the mean of cell `(a, b)`. The contrasts use the
factorial-effect normalization of Dasgupta, Pillai and Rubin: an effect is `2^{-(K-1)} g ⬝ m`
for a `±1` contrast vector `g`, here with `K = 2`.

* `mainEffectA = (m₁₁ + m₁₀ - m₀₁ - m₀₀) / 2`: the average of the two `A = 1` cell means minus
  the average of the two `A = 0` cell means.
* `mainEffectB = (m₁₁ + m₀₁ - m₁₀ - m₀₀) / 2`: the same for `B`.
* `interactionAB = (m₁₁ - m₁₀ - m₀₁ + m₀₀) / 2`: half the difference between the effect of `A`
  at `B = 1` and its effect at `B = 0`. The unhalved difference-in-differences, which part of
  the literature also calls the interaction, is `2 * interactionAB`.

## References

* T. Dasgupta, N. S. Pillai and D. B. Rubin, *Causal inference from `2^K` factorial designs
  using the potential outcomes model*, arXiv:1211.2481, Section 3.1, equations (1) and (2).
* D. G. Horvitz and D. J. Thompson, *A generalization of sampling without replacement from a
  finite universe*, J. Amer. Statist. Assoc. 47 (1952), 663–685 (the inverse-probability-weighted
  estimator behind `ipwCellMean`).
-/

@[expose] public section

open MeasureTheory Finset
open MathlibExt.Probability.Causality

namespace MathlibExt.Probability.Statistics.Experiment

/-- Assignment functions with exact fiber sizes `n c` per cell. -/
def cellAssignSpace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : Fin 4 → ℕ) : Finset (ι → Fin 4) :=
  Finset.univ.filter fun f =>
    ∀ c, (Finset.univ.filter fun i => f i = c).card = n c

/-- Complete randomization over the four cells: uniform on `cellAssignSpace`. With positive
cell sizes summing to `card ι` it is a probability measure
(`isProbabilityMeasure_cellAssignment`). When no assignment has the prescribed sizes (for
example, sizes that do not sum to `card ι`), `cellAssignSpace n` is empty and
`cellAssignment n` is the zero measure. -/
noncomputable def cellAssignment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : Fin 4 → ℕ) : Measure (ι → Fin 4) :=
  Measure.uniformOfFinset (cellAssignSpace n)

/-- Observed mean in cell `c` under the assignment `f`. The name is frozen as
`factorialCellMean`: plain `cellMean` already exists in an unrelated namespace
on main. -/
noncomputable def factorialCellMean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y : ι → ℝ) (c : Fin 4) (f : ι → Fin 4) : ℝ :=
  sampleMean y (Finset.univ.filter fun i => f i = c)

/-- **Main effect of `A`** from the cell means `m_ab` of the treatment combinations `(a, b)`
(cells `0, 1, 2, 3`, see the module docstring): the average of the two `A = 1` cell means minus
the average of the two `A = 0` cell means. -/
noncomputable def mainEffectA (m₀₀ m₀₁ m₁₀ m₁₁ : ℝ) : ℝ :=
  (m₁₁ + m₁₀ - m₀₁ - m₀₀) / 2

/-- **Main effect of `B`**: the average of the two `B = 1` cell means minus the average of the
two `B = 0` cell means. -/
noncomputable def mainEffectB (m₀₀ m₀₁ m₁₀ m₁₁ : ℝ) : ℝ :=
  (m₁₁ + m₀₁ - m₁₀ - m₀₀) / 2

/-- **Interaction of `A` and `B`**: half the difference between the effect of `A` at `B = 1`,
`m₁₁ - m₀₁`, and its effect at `B = 0`, `m₁₀ - m₀₀`; that is, half the difference-in-differences.
-/
noncomputable def interactionAB (m₀₀ m₀₁ m₁₀ m₁₁ : ℝ) : ℝ :=
  (m₁₁ - m₁₀ - m₀₁ + m₀₀) / 2

theorem cellAssignment_eq (ι : Type*) [Fintype ι] [DecidableEq ι] (n : Fin 4 → ℕ) :
    cellAssignment (ι := ι) n = Measure.uniformOfFinset (cellAssignSpace (ι := ι) n) := by
  rfl

theorem cellAssignSpace_nonempty (ι : Type*) [Fintype ι] [DecidableEq ι]
    (n : Fin 4 → ℕ) (hpos : ∀ c, 0 < n c)
    (hsum : ∑ c, n c = Fintype.card ι) :
    (cellAssignSpace (ι := ι) n).Nonempty := by
  have hsum4 : n 0 + n 1 + n 2 + n 3 = Fintype.card ι := by
    have h := hsum
    rwa [Fin.sum_univ_four] at h
  have h0 := hpos 0
  have h1 := hpos 1
  have h2 := hpos 2
  have h3 := hpos 3
  obtain ⟨s₀, hs₀sub, hs₀card⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι)) (n := n 0) (by
      rw [Finset.card_univ]
      omega)
  have e0 : (Finset.univ \ s₀).card = Fintype.card ι - n 0 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hs₀card]
  obtain ⟨s₁, hs₁sub, hs₁card⟩ :=
    Finset.exists_subset_card_eq (s := Finset.univ \ s₀) (n := n 1) (by
      rw [e0]
      omega)
  have hcap1 : s₁ ∩ (Finset.univ \ s₀) = s₁ := by
    ext x
    simp only [Finset.mem_inter]
    exact ⟨fun h => h.1, fun h => ⟨h, hs₁sub h⟩⟩
  have e1 : ((Finset.univ \ s₀) \ s₁).card = (Fintype.card ι - n 0) - n 1 := by
    rw [Finset.card_sdiff, hcap1, hs₁card, e0]
  obtain ⟨s₂, hs₂sub, hs₂card⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ \ s₀) \ s₁) (n := n 2) (by
      rw [e1]
      omega)
  have hcap2 : s₂ ∩ ((Finset.univ \ s₀) \ s₁) = s₂ := by
    ext x
    simp only [Finset.mem_inter]
    exact ⟨fun h => h.1, fun h => ⟨h, hs₂sub h⟩⟩
  have hcard3 : (((Finset.univ \ s₀) \ s₁) \ s₂).card = n 3 := by
    have e2 : (((Finset.univ \ s₀) \ s₁) \ s₂).card =
        ((Finset.univ \ s₀) \ s₁).card - n 2 := by
      rw [Finset.card_sdiff, hcap2, hs₂card]
    rw [e2, e1]
    omega
  refine ⟨fun i => if i ∈ s₀ then (0 : Fin 4) else if i ∈ s₁ then (1 : Fin 4)
    else if i ∈ s₂ then (2 : Fin 4) else (3 : Fin 4), ?_⟩
  simp only [cellAssignSpace, Finset.mem_filter, Finset.mem_univ, true_and]
  have hP0 : (Finset.univ.filter fun i =>
      (if i ∈ s₀ then (0 : Fin 4) else if i ∈ s₁ then (1 : Fin 4)
        else if i ∈ s₂ then (2 : Fin 4) else (3 : Fin 4)) = 0).card = n 0 := by
    have hfil : Finset.univ.filter (fun i =>
        (if i ∈ s₀ then (0 : Fin 4) else if i ∈ s₁ then (1 : Fin 4)
          else if i ∈ s₂ then (2 : Fin 4) else (3 : Fin 4)) = 0) = s₀ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hi : i ∈ s₀
      · simp [hi]
      · simp [hi]
        split_ifs <;> simp
    rw [hfil, hs₀card]
  have hP1 : (Finset.univ.filter fun i =>
      (if i ∈ s₀ then (0 : Fin 4) else if i ∈ s₁ then (1 : Fin 4)
        else if i ∈ s₂ then (2 : Fin 4) else (3 : Fin 4)) = 1).card = n 1 := by
    have hfil : Finset.univ.filter (fun i =>
        (if i ∈ s₀ then (0 : Fin 4) else if i ∈ s₁ then (1 : Fin 4)
          else if i ∈ s₂ then (2 : Fin 4) else (3 : Fin 4)) = 1) = s₁ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hi1 : i ∈ s₁
      · have hi0 : i ∉ s₀ := (Finset.mem_sdiff.mp (hs₁sub hi1)).2
        simp [hi0, hi1]
      · by_cases hi0 : i ∈ s₀
        · simp [hi0, hi1]
        · simp [hi0, hi1]
          split_ifs <;> simp
    rw [hfil, hs₁card]
  have hP2 : (Finset.univ.filter fun i =>
      (if i ∈ s₀ then (0 : Fin 4) else if i ∈ s₁ then (1 : Fin 4)
        else if i ∈ s₂ then (2 : Fin 4) else (3 : Fin 4)) = 2).card = n 2 := by
    have hfil : Finset.univ.filter (fun i =>
        (if i ∈ s₀ then (0 : Fin 4) else if i ∈ s₁ then (1 : Fin 4)
          else if i ∈ s₂ then (2 : Fin 4) else (3 : Fin 4)) = 2) = s₂ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hi2 : i ∈ s₂
      · have h10 : i ∈ Finset.univ \ s₀ ∧ i ∉ s₁ :=
          Finset.mem_sdiff.mp (hs₂sub hi2)
        have hi0 : i ∉ s₀ := (Finset.mem_sdiff.mp h10.1).2
        have hi1 : i ∉ s₁ := h10.2
        simp [hi0, hi1, hi2]
      · by_cases hi0 : i ∈ s₀
        · simp [hi0, hi2]
        · by_cases hi1 : i ∈ s₁
          · simp [hi0, hi1, hi2]
          · simp [hi0, hi1, hi2]
    rw [hfil, hs₂card]
  have hP3 : (Finset.univ.filter fun i =>
      (if i ∈ s₀ then (0 : Fin 4) else if i ∈ s₁ then (1 : Fin 4)
        else if i ∈ s₂ then (2 : Fin 4) else (3 : Fin 4)) = 3).card = n 3 := by
    have hfil : Finset.univ.filter (fun i =>
        (if i ∈ s₀ then (0 : Fin 4) else if i ∈ s₁ then (1 : Fin 4)
          else if i ∈ s₂ then (2 : Fin 4) else (3 : Fin 4)) = 3)
        = ((Finset.univ \ s₀) \ s₁) \ s₂ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
      by_cases hi0 : i ∈ s₀
      · simp [hi0]
      · by_cases hi1 : i ∈ s₁
        · simp [hi0, hi1]
        · by_cases hi2 : i ∈ s₂
          · simp [hi0, hi1, hi2]
          · simp [hi0, hi1, hi2]
    rw [hfil, hcard3]
  intro c
  fin_cases c
  · exact hP0
  · exact hP1
  · exact hP2
  · exact hP3

/-- With positive cell sizes summing to `card ι`, the cell-assignment law is a probability
measure. -/
theorem isProbabilityMeasure_cellAssignment (ι : Type*) [Fintype ι] [DecidableEq ι]
    (n : Fin 4 → ℕ) (hpos : ∀ c, 0 < n c) (hsum : ∑ c, n c = Fintype.card ι) :
    IsProbabilityMeasure (cellAssignment (ι := ι) n) := by
  constructor
  have hC : ((cellAssignSpace (ι := ι) n).card : ENNReal) ≠ 0 := by
    exact_mod_cast (cellAssignSpace_nonempty ι n hpos hsum).card_pos.ne'
  rw [cellAssignment_eq, Measure.uniformOfFinset_apply]
  simp only [Set.mem_univ, filter_true]
  exact ENNReal.div_self hC (ENNReal.natCast_ne_top _)

theorem integral_cellAssignment (ι : Type*) [Fintype ι] [DecidableEq ι]
    (n : Fin 4 → ℕ) (g : (ι → Fin 4) → ℝ)
    (hne : (cellAssignSpace (ι := ι) n).Nonempty) :
    ∫ f, g f ∂(cellAssignment (ι := ι) n)
      = (∑ f ∈ cellAssignSpace (ι := ι) n, g f) / (cellAssignSpace (ι := ι) n).card := by
  have hC0 : (cellAssignSpace (ι := ι) n).card ≠ 0 := (Finset.card_pos.mpr hne).ne'
  have hC : (((cellAssignSpace (ι := ι) n).card : ℕ) : ENNReal) ≠ 0 := by
    exact_mod_cast hC0
  rw [cellAssignment_eq, Measure.uniformOfFinset,
    integral_finsetSum_measure fun f _ =>
      (Integrable.of_finite : Integrable g (Measure.dirac f)).smul_measure
        (ENNReal.inv_ne_top.2 hC)]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul, ← mul_sum]
  rw [div_eq_inv_mul]

theorem exchange_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : Fin 4 → ℕ) (c : Fin 4) (i j : ι) :
    ((cellAssignSpace (ι := ι) n).filter (fun f => f i = c)).card
      = ((cellAssignSpace (ι := ι) n).filter (fun f => f j = c)).card := by
  have hfib : ∀ (f : ι → Fin 4) (c' : Fin 4),
      (Finset.univ.filter fun i' => (f ∘ Equiv.swap i j) i' = c').card
        = (Finset.univ.filter fun i' => f i' = c').card := by
    intro f c'
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact Fintype.card_congr
      ((Equiv.swap i j).subtypeEquiv (fun _ => Iff.rfl))
  have hmap : ∀ f ∈ cellAssignSpace (ι := ι) n,
      (f ∘ Equiv.swap i j) ∈ cellAssignSpace (ι := ι) n := by
    intro f hf
    simp only [cellAssignSpace, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    intro c'
    rw [hfib]
    exact hf c'
  have hinv : ∀ f : ι → Fin 4,
      (f ∘ Equiv.swap i j) ∘ Equiv.swap i j = f := by
    intro f
    funext x
    change f (Equiv.swap i j (Equiv.swap i j x)) = f x
    congr 1
    by_cases h1 : x = i
    · subst h1
      rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
    · by_cases h2 : x = j
      · subst h2
        rw [Equiv.swap_apply_right, Equiv.swap_apply_left]
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2,
          Equiv.swap_apply_of_ne_of_ne h1 h2]
  refine Finset.card_bij (fun f _ => f ∘ Equiv.swap i j) ?_ ?_ ?_
  · intro f hf
    rw [Finset.mem_filter] at hf ⊢
    refine ⟨hmap f hf.1, ?_⟩
    simp only [Function.comp_apply, Equiv.swap_apply_right]
    exact hf.2
  · intro f₁ _ f₂ _ h
    have h2 := congrArg (fun g => g ∘ Equiv.swap i j) h
    simpa [hinv] using h2
  · intro g hg
    rw [Finset.mem_filter] at hg
    refine ⟨g ∘ Equiv.swap i j,
      Finset.mem_filter.mpr ⟨hmap g hg.1, ?_⟩, hinv g⟩
    simp only [Function.comp_apply, Equiv.swap_apply_left]
    exact hg.2

/-- Observed cell means are unbiased for the population cell means: for the fixed
potential-outcome surface `y`, cell `c`, and fixed positive cell sizes `n`
(`hpos`, summing to the population size in `hsum`), the integral of the observed
cell mean `factorialCellMean y c` under complete randomization `cellAssignment n`
equals the population mean `popMean y`. -/
theorem integral_factorialCellMean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y : ι → ℝ) (c : Fin 4) (n : Fin 4 → ℕ)
    (hpos : ∀ c, 0 < n c) (hsum : ∑ c, n c = Fintype.card ι) :
    ∫ f, factorialCellMean y c f ∂(cellAssignment n) = popMean y := by
  have hne : (cellAssignSpace (ι := ι) n).Nonempty := cellAssignSpace_nonempty ι n hpos hsum
  have hS0 : ((cellAssignSpace (ι := ι) n).card : ℝ) ≠ 0 :=
    by exact_mod_cast (Finset.card_pos.mpr hne).ne'
  have hnc : (n c : ℝ) ≠ 0 := by exact_mod_cast (hpos c).ne'
  have hsum4 : n 0 + n 1 + n 2 + n 3 = Fintype.card ι := by
    have h := hsum
    rwa [Fin.sum_univ_four] at h
  have hNpos : 0 < Fintype.card ι := by
    have h0 := hpos 0
    have h1 := hpos 1
    have h2 := hpos 2
    have h3 := hpos 3
    omega
  have hN : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
  obtain ⟨i₀⟩ : Nonempty ι := Fintype.card_pos_iff.mp hNpos
  have hmem : ∀ f ∈ cellAssignSpace (ι := ι) n,
      (Finset.univ.filter fun i => f i = c).card = n c := by
    intro f hf
    simp only [cellAssignSpace, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    exact hf c
  have hterm : ∀ f ∈ cellAssignSpace (ι := ι) n, factorialCellMean y c f
      = (∑ i, (if f i = c then y i else 0)) / n c := by
    intro f hf
    unfold factorialCellMean sampleMean
    rw [hmem f hf, ← Finset.sum_filter]
  have hinner : ∀ i : ι,
      (∑ f ∈ cellAssignSpace (ι := ι) n, (if f i = c then y i else 0))
        = y i * (((cellAssignSpace (ι := ι) n).filter (fun f => f i = c)).card : ℝ) := by
    intro i
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    ring
  have hexch : ∀ i : ι,
      (((cellAssignSpace (ι := ι) n).filter (fun f => f i = c)).card : ℝ)
        = (((cellAssignSpace (ι := ι) n).filter (fun f => f i₀ = c)).card : ℝ) := by
    intro i
    exact congrArg Nat.cast (exchange_count n c i i₀)
  have hdouble : (∑ i : ι, (((cellAssignSpace (ι := ι) n).filter (fun f => f i = c)).card : ℝ))
      = ((cellAssignSpace (ι := ι) n).card : ℝ) * n c := by
    have hcard_eq : ∀ i : ι, (((cellAssignSpace (ι := ι) n).filter (fun f => f i = c)).card : ℝ)
        = ∑ f ∈ cellAssignSpace (ι := ι) n, (if f i = c then (1 : ℝ) else 0) :=
      fun i => (Finset.sum_boole _ _).symm
    simp_rw [hcard_eq]
    rw [Finset.sum_comm]
    have hone : ∀ f ∈ cellAssignSpace (ι := ι) n,
        (∑ i, (if f i = c then (1 : ℝ) else 0)) = (n c : ℝ) := by
      intro f hf
      rw [Finset.sum_boole]
      exact congrArg (Nat.cast : ℕ → ℝ) (hmem f hf)
    rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul]
  have hK : (Fintype.card ι : ℝ)
        * (((cellAssignSpace (ι := ι) n).filter (fun f => f i₀ = c)).card : ℝ)
      = ((cellAssignSpace (ι := ι) n).card : ℝ) * n c := by
    have h1 : (∑ _i : ι, (((cellAssignSpace (ι := ι) n).filter (fun f => f i₀ = c)).card : ℝ))
        = ((cellAssignSpace (ι := ι) n).card : ℝ) * n c := by
      rw [← hdouble]
      exact Finset.sum_congr rfl fun i _ => (hexch i).symm
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
    exact h1
  rw [integral_cellAssignment _ n _ hne]
  have hsum1 : (∑ f ∈ cellAssignSpace (ι := ι) n, factorialCellMean y c f)
      = ∑ f ∈ cellAssignSpace (ι := ι) n, (∑ i, (if f i = c then y i else 0)) / n c :=
    Finset.sum_congr rfl fun f hf => hterm f hf
  rw [hsum1, ← Finset.sum_div, Finset.sum_comm]
  simp only [hinner, hexch, ← Finset.sum_mul]
  unfold popMean
  rw [div_div, div_eq_div_iff (mul_ne_zero hnc hS0) hN]
  linear_combination (∑ i, y i) * hK

/-- Observed factorial contrasts are unbiased: one corollary per contrast by
linearity of the integral from `integral_factorialCellMean`, with explicit
cell-size positivity and exact-size hypotheses inherited from it. -/
theorem integral_mainEffectA {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y₀₀ y₀₁ y₁₀ y₁₁ : ι → ℝ) (n : Fin 4 → ℕ)
    (hpos : ∀ c, 0 < n c) (hsum : ∑ c, n c = Fintype.card ι) :
    ∫ f, mainEffectA (factorialCellMean y₀₀ 0 f) (factorialCellMean y₀₁ 1 f)
      (factorialCellMean y₁₀ 2 f) (factorialCellMean y₁₁ 3 f)
      ∂(cellAssignment n) =
      mainEffectA (popMean y₀₀) (popMean y₀₁) (popMean y₁₀)
        (popMean y₁₁) := by
  have hne : (cellAssignSpace (ι := ι) n).Nonempty := cellAssignSpace_nonempty ι n hpos hsum
  have hS0 : ((cellAssignSpace (ι := ι) n).card : ℝ) ≠ 0 :=
    by exact_mod_cast (Finset.card_pos.mpr hne).ne'
  have e : ∀ (y : ι → ℝ) (c : Fin 4),
      (∑ f ∈ cellAssignSpace (ι := ι) n, factorialCellMean y c f)
        = popMean y * (cellAssignSpace (ι := ι) n).card := by
    intro y c
    have h := integral_cellAssignment ι n (fun f => factorialCellMean y c f) hne
    rw [integral_factorialCellMean y c n hpos hsum, eq_comm, div_eq_iff hS0] at h
    exact h
  simp only [mainEffectA]
  rw [integral_cellAssignment _ n _ hne]
  simp only [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [e y₁₁ 3, e y₁₀ 2, e y₀₁ 1, e y₀₀ 0, div_div,
    div_eq_div_iff (mul_ne_zero (by norm_num) hS0) (by norm_num)]
  ring

theorem integral_mainEffectB {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y₀₀ y₀₁ y₁₀ y₁₁ : ι → ℝ) (n : Fin 4 → ℕ)
    (hpos : ∀ c, 0 < n c) (hsum : ∑ c, n c = Fintype.card ι) :
    ∫ f, mainEffectB (factorialCellMean y₀₀ 0 f) (factorialCellMean y₀₁ 1 f)
      (factorialCellMean y₁₀ 2 f) (factorialCellMean y₁₁ 3 f)
      ∂(cellAssignment n) =
      mainEffectB (popMean y₀₀) (popMean y₀₁) (popMean y₁₀)
        (popMean y₁₁) := by
  have hne : (cellAssignSpace (ι := ι) n).Nonempty := cellAssignSpace_nonempty ι n hpos hsum
  have hS0 : ((cellAssignSpace (ι := ι) n).card : ℝ) ≠ 0 :=
    by exact_mod_cast (Finset.card_pos.mpr hne).ne'
  have e : ∀ (y : ι → ℝ) (c : Fin 4),
      (∑ f ∈ cellAssignSpace (ι := ι) n, factorialCellMean y c f)
        = popMean y * (cellAssignSpace (ι := ι) n).card := by
    intro y c
    have h := integral_cellAssignment ι n (fun f => factorialCellMean y c f) hne
    rw [integral_factorialCellMean y c n hpos hsum, eq_comm, div_eq_iff hS0] at h
    exact h
  simp only [mainEffectB]
  rw [integral_cellAssignment _ n _ hne]
  simp only [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [e y₁₁ 3, e y₁₀ 2, e y₀₁ 1, e y₀₀ 0, div_div,
    div_eq_div_iff (mul_ne_zero (by norm_num) hS0) (by norm_num)]
  ring

theorem integral_interactionAB {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y₀₀ y₀₁ y₁₀ y₁₁ : ι → ℝ) (n : Fin 4 → ℕ)
    (hpos : ∀ c, 0 < n c) (hsum : ∑ c, n c = Fintype.card ι) :
    ∫ f, interactionAB (factorialCellMean y₀₀ 0 f)
      (factorialCellMean y₀₁ 1 f) (factorialCellMean y₁₀ 2 f)
      (factorialCellMean y₁₁ 3 f) ∂(cellAssignment n) =
      interactionAB (popMean y₀₀) (popMean y₀₁) (popMean y₁₀)
        (popMean y₁₁) := by
  have hne : (cellAssignSpace (ι := ι) n).Nonempty := cellAssignSpace_nonempty ι n hpos hsum
  have hS0 : ((cellAssignSpace (ι := ι) n).card : ℝ) ≠ 0 :=
    by exact_mod_cast (Finset.card_pos.mpr hne).ne'
  have e : ∀ (y : ι → ℝ) (c : Fin 4),
      (∑ f ∈ cellAssignSpace (ι := ι) n, factorialCellMean y c f)
        = popMean y * (cellAssignSpace (ι := ι) n).card := by
    intro y c
    have h := integral_cellAssignment ι n (fun f => factorialCellMean y c f) hne
    rw [integral_factorialCellMean y c n hpos hsum, eq_comm, div_eq_iff hS0] at h
    exact h
  simp only [interactionAB]
  rw [integral_cellAssignment _ n _ hne]
  simp only [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [e y₁₁ 3, e y₁₀ 2, e y₀₁ 1, e y₀₀ 0, div_div,
    div_eq_div_iff (mul_ne_zero (by norm_num) hS0) (by norm_num)]
  ring

/-- **Per-unit assignment law**: unit `i` goes to cell `c` with probability `π i c`. This is the
finite law `weightLaw (π i)` of `MathlibExt.Probability.WeightLaw`; independent assignment of all
units is the product law `Measure.pi fun i => bernoulliCell π i`. -/
noncomputable abbrev bernoulliCell {ι : Type*} (π : ι → Fin 4 → ℝ) (i : ι) : Measure (Fin 4) :=
  weightLaw (π i)

/-- **Inverse-probability-weighted (Horvitz–Thompson) cell mean** of cell `c` under the
assignment `f`: `∑_{i : f i = c} Y i / (N π i c)`, where `N = card ι`. An empty realized cell
gives `0`. -/
noncomputable def ipwCellMean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Y : ι → ℝ) (π : ι → Fin 4 → ℝ) (c : Fin 4)
    (f : ι → Fin 4) : ℝ :=
  (∑ i ∈ Finset.univ.filter fun i => f i = c,
    Y i / ((Fintype.card ι : ℝ) * π i c))

/-- The per-unit assignment law is a probability measure under nonnegativity and per-unit
normalization of the cell probabilities. -/
theorem isProbabilityMeasure_bernoulliCell {ι : Type*} (π : ι → Fin 4 → ℝ) (i : ι)
    (hnn : ∀ i c, 0 ≤ π i c) (hnorm : ∀ i, ∑ c, π i c = 1) :
    IsProbabilityMeasure (bernoulliCell π i) :=
  isProbabilityMeasure_weightLaw (π i) (hnn i) (hnorm i)

/-- Per-unit mean-value property: the integral of the single-unit IPW
contribution under `bernoulliCell π i` is the unit's outcome share `Y i / N`. -/
private theorem integral_bernoulliCell_ite {ι : Type*} [Fintype ι]
    (Y : ι → ℝ) (π : ι → Fin 4 → ℝ)
    (hpos : ∀ i c, 0 < π i c)
    (hN : 0 < Fintype.card ι) (i : ι) (c : Fin 4) :
    ∫ a, (if a = c then Y i / ((Fintype.card ι : ℝ) * π i c) else 0)
      ∂(bernoulliCell π i) = Y i / Fintype.card ι := by
  rw [bernoulliCell, integral_weightLaw (π i) fun c' => (hpos i c').le]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  have hπ : π i c ≠ 0 := ne_of_gt (hpos i c)
  have hN' : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hN)
  field_simp

/-- The IPW cell mean as a sum over all units of the single-unit contributions
`1{f i = c} Y i / (N π i c)`. -/
theorem ipwCellMean_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Y : ι → ℝ) (π : ι → Fin 4 → ℝ) (c : Fin 4) (f : ι → Fin 4) :
    ipwCellMean Y π c f =
      ∑ i, (if f i = c then Y i / ((Fintype.card ι : ℝ) * π i c) else 0) := by
  rw [ipwCellMean, Finset.sum_filter]

/-- Each single-unit contribution is integrable over the product law. -/
private theorem integrable_ipwCellMean_term {ι : Type*} [Fintype ι]
    (Y : ι → ℝ) (π : ι → Fin 4 → ℝ)
    (hpos : ∀ i c, 0 < π i c) (hnorm : ∀ i, ∑ c, π i c = 1)
    (i : ι) (c : Fin 4) :
    Integrable (fun f : ι → Fin 4 => if f i = c then Y i / ((Fintype.card ι : ℝ) * π i c) else 0)
      (Measure.pi fun i => bernoulliCell π i) := by
  have _hprob : ∀ j, IsProbabilityMeasure (bernoulliCell π j) :=
    fun j => isProbabilityMeasure_bernoulliCell π j (fun i c => le_of_lt (hpos i c)) hnorm
  exact integrable_comp_eval (μ := fun j => bernoulliCell π j) (i := i)
    (f := fun a => if a = c then Y i / ((Fintype.card ι : ℝ) * π i c) else 0)
    (Integrable.of_finite)

/-- Each single-unit contribution integrates to the outcome share `Y i / N`. -/
private theorem integral_ipwCellMean_term {ι : Type*} [Fintype ι]
    (Y : ι → ℝ) (π : ι → Fin 4 → ℝ)
    (hpos : ∀ i c, 0 < π i c) (hnorm : ∀ i, ∑ c, π i c = 1)
    (hN : 0 < Fintype.card ι) (i : ι) (c : Fin 4) :
    (∫ f, (if f i = c then Y i / ((Fintype.card ι : ℝ) * π i c) else 0)
      ∂(Measure.pi fun i => bernoulliCell π i)) = Y i / Fintype.card ι := by
  have _hprob : ∀ j, IsProbabilityMeasure (bernoulliCell π j) :=
    fun j => isProbabilityMeasure_bernoulliCell π j (fun i c => le_of_lt (hpos i c)) hnorm
  have hcomp := integral_comp_eval (μ := fun j => bernoulliCell π j) (i := i)
    (f := fun a => if a = c then Y i / ((Fintype.card ι : ℝ) * π i c) else 0)
    (Measurable.of_discrete.aestronglyMeasurable)
  exact hcomp.trans (integral_bernoulliCell_ite Y π hpos hN i c)

/-- IPW cell means are integrable over the product law. -/
private theorem integrable_ipwCellMean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Y : ι → ℝ) (π : ι → Fin 4 → ℝ)
    (hpos : ∀ i c, 0 < π i c) (hnorm : ∀ i, ∑ c, π i c = 1)
    (c : Fin 4) :
    Integrable (fun f => ipwCellMean Y π c f)
      (Measure.pi fun i => bernoulliCell π i) := by
  simp only [ipwCellMean_eq_sum]
  exact integrable_finsetSum Finset.univ
    (fun i _ => integrable_ipwCellMean_term Y π hpos hnorm i c)

/-- Halving commutes with integration. -/
private theorem integral_div_two {ι : Type*} {g : (ι → Fin 4) → ℝ}
    {μ : Measure (ι → Fin 4)} :
    (∫ f, g f / 2 ∂μ) = (∫ f, g f ∂μ) / 2 := by
  have hdiv : ∀ f, g f / 2 = (2⁻¹ : ℝ) * g f := fun f => div_eq_inv_mul _ _
  simp only [hdiv, integral_const_mul, div_eq_inv_mul]

/-- IPW cell means are unbiased for the population cell means: the integral of
`ipwCellMean Y π c` over the product assignment law equals `popMean Y`.

Clause map: "independent Bernoulli assignment" → the product law
`Measure.pi fun i => bernoulliCell π i`; "known strictly positive cell
probabilities" → `π` with `hpos : ∀ i c, 0 < π i c`; "per-unit normalization" →
`hnorm : ∀ i, ∑ c, π i c = 1`; "fixed potential outcomes" → `Y`; "finite
population with `N > 0`" → `hN : 0 < Fintype.card ι`; "IPW cell mean" →
`ipwCellMean Y π c f`; "unbiased for the population cell mean" → the equation
with `popMean Y`; "empty realized cells allowed" → no nonempty-cell hypothesis
(see the boundary example with an empty realized cell). -/
theorem integral_ipwCellMean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Y : ι → ℝ) (π : ι → Fin 4 → ℝ)
    (hpos : ∀ i c, 0 < π i c) (hnorm : ∀ i, ∑ c, π i c = 1)
    (hN : 0 < Fintype.card ι) (c : Fin 4) :
    ∫ f, ipwCellMean Y π c f ∂(Measure.pi fun i => bernoulliCell π i) =
      popMean Y := by
  simp only [ipwCellMean_eq_sum]
  rw [integral_finsetSum Finset.univ
    (fun i _ => integrable_ipwCellMean_term Y π hpos hnorm i c)]
  simp only [integral_ipwCellMean_term Y π hpos hnorm hN]
  unfold popMean
  rw [Finset.sum_div]

/-- **The IPW main effect of `A` is unbiased**: under independent assignment with known positive,
normalized cell probabilities, `mainEffectA` of the four IPW cell means has expectation
`mainEffectA` of the population cell means. -/
theorem integral_ipwMainEffectA {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y₀₀ y₀₁ y₁₀ y₁₁ : ι → ℝ) (π : ι → Fin 4 → ℝ)
    (hpos : ∀ i c, 0 < π i c) (hnorm : ∀ i, ∑ c, π i c = 1)
    (hN : 0 < Fintype.card ι) :
    ∫ f, mainEffectA (ipwCellMean y₀₀ π 0 f) (ipwCellMean y₀₁ π 1 f)
      (ipwCellMean y₁₀ π 2 f) (ipwCellMean y₁₁ π 3 f)
      ∂(Measure.pi fun i => bernoulliCell π i) =
      mainEffectA (popMean y₀₀) (popMean y₀₁) (popMean y₁₀)
        (popMean y₁₁) := by
  have hI : ∀ (Y : ι → ℝ) (c : Fin 4),
      Integrable (fun f => ipwCellMean Y π c f)
        (Measure.pi fun i => bernoulliCell π i) :=
    fun Y c => integrable_ipwCellMean Y π hpos hnorm c
  have e1 : (∫ f, ipwCellMean y₁₁ π 3 f + ipwCellMean y₁₀ π 2 f
        ∂(Measure.pi fun i => bernoulliCell π i))
        = (∫ f, ipwCellMean y₁₁ π 3 f ∂(Measure.pi fun i => bernoulliCell π i))
          + ∫ f, ipwCellMean y₁₀ π 2 f ∂(Measure.pi fun i => bernoulliCell π i) :=
    integral_add (hI y₁₁ 3) (hI y₁₀ 2)
  have e2 : (∫ f, ipwCellMean y₁₁ π 3 f + ipwCellMean y₁₀ π 2 f - ipwCellMean y₀₁ π 1 f
        ∂(Measure.pi fun i => bernoulliCell π i))
        = (∫ f, ipwCellMean y₁₁ π 3 f + ipwCellMean y₁₀ π 2 f
          ∂(Measure.pi fun i => bernoulliCell π i))
          - ∫ f, ipwCellMean y₀₁ π 1 f ∂(Measure.pi fun i => bernoulliCell π i) :=
    integral_sub ((hI y₁₁ 3).add (hI y₁₀ 2)) (hI y₀₁ 1)
  have e3 : (∫ f, ipwCellMean y₁₁ π 3 f + ipwCellMean y₁₀ π 2 f - ipwCellMean y₀₁ π 1 f
        - ipwCellMean y₀₀ π 0 f ∂(Measure.pi fun i => bernoulliCell π i))
        = (∫ f, ipwCellMean y₁₁ π 3 f + ipwCellMean y₁₀ π 2 f - ipwCellMean y₀₁ π 1 f
          ∂(Measure.pi fun i => bernoulliCell π i))
          - ∫ f, ipwCellMean y₀₀ π 0 f ∂(Measure.pi fun i => bernoulliCell π i) :=
    integral_sub (((hI y₁₁ 3).add (hI y₁₀ 2)).sub (hI y₀₁ 1)) (hI y₀₀ 0)
  unfold mainEffectA
  rw [integral_div_two, e3, e2, e1,
    integral_ipwCellMean y₁₁ π hpos hnorm hN 3,
    integral_ipwCellMean y₁₀ π hpos hnorm hN 2,
    integral_ipwCellMean y₀₁ π hpos hnorm hN 1,
    integral_ipwCellMean y₀₀ π hpos hnorm hN 0]

/-- **The IPW main effect of `B` is unbiased**: under independent assignment with known positive,
normalized cell probabilities, `mainEffectB` of the four IPW cell means has expectation
`mainEffectB` of the population cell means. -/
theorem integral_ipwMainEffectB {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y₀₀ y₀₁ y₁₀ y₁₁ : ι → ℝ) (π : ι → Fin 4 → ℝ)
    (hpos : ∀ i c, 0 < π i c) (hnorm : ∀ i, ∑ c, π i c = 1)
    (hN : 0 < Fintype.card ι) :
    ∫ f, mainEffectB (ipwCellMean y₀₀ π 0 f) (ipwCellMean y₀₁ π 1 f)
      (ipwCellMean y₁₀ π 2 f) (ipwCellMean y₁₁ π 3 f)
      ∂(Measure.pi fun i => bernoulliCell π i) =
      mainEffectB (popMean y₀₀) (popMean y₀₁) (popMean y₁₀)
        (popMean y₁₁) := by
  have hI : ∀ (Y : ι → ℝ) (c : Fin 4),
      Integrable (fun f => ipwCellMean Y π c f)
        (Measure.pi fun i => bernoulliCell π i) :=
    fun Y c => integrable_ipwCellMean Y π hpos hnorm c
  have e1 : (∫ f, ipwCellMean y₁₁ π 3 f + ipwCellMean y₀₁ π 1 f
        ∂(Measure.pi fun i => bernoulliCell π i))
        = (∫ f, ipwCellMean y₁₁ π 3 f ∂(Measure.pi fun i => bernoulliCell π i))
          + ∫ f, ipwCellMean y₀₁ π 1 f ∂(Measure.pi fun i => bernoulliCell π i) :=
    integral_add (hI y₁₁ 3) (hI y₀₁ 1)
  have e2 : (∫ f, ipwCellMean y₁₁ π 3 f + ipwCellMean y₀₁ π 1 f - ipwCellMean y₁₀ π 2 f
        ∂(Measure.pi fun i => bernoulliCell π i))
        = (∫ f, ipwCellMean y₁₁ π 3 f + ipwCellMean y₀₁ π 1 f
          ∂(Measure.pi fun i => bernoulliCell π i))
          - ∫ f, ipwCellMean y₁₀ π 2 f ∂(Measure.pi fun i => bernoulliCell π i) :=
    integral_sub ((hI y₁₁ 3).add (hI y₀₁ 1)) (hI y₁₀ 2)
  have e3 : (∫ f, ipwCellMean y₁₁ π 3 f + ipwCellMean y₀₁ π 1 f - ipwCellMean y₁₀ π 2 f
        - ipwCellMean y₀₀ π 0 f ∂(Measure.pi fun i => bernoulliCell π i))
        = (∫ f, ipwCellMean y₁₁ π 3 f + ipwCellMean y₀₁ π 1 f - ipwCellMean y₁₀ π 2 f
          ∂(Measure.pi fun i => bernoulliCell π i))
          - ∫ f, ipwCellMean y₀₀ π 0 f ∂(Measure.pi fun i => bernoulliCell π i) :=
    integral_sub (((hI y₁₁ 3).add (hI y₀₁ 1)).sub (hI y₁₀ 2)) (hI y₀₀ 0)
  unfold mainEffectB
  rw [integral_div_two, e3, e2, e1,
    integral_ipwCellMean y₁₁ π hpos hnorm hN 3,
    integral_ipwCellMean y₀₁ π hpos hnorm hN 1,
    integral_ipwCellMean y₁₀ π hpos hnorm hN 2,
    integral_ipwCellMean y₀₀ π hpos hnorm hN 0]

/-- **The IPW interaction is unbiased**: under independent assignment with known positive,
normalized cell probabilities, `interactionAB` of the four IPW cell means has expectation
`interactionAB` of the population cell means. -/
theorem integral_ipwInteractionAB {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y₀₀ y₀₁ y₁₀ y₁₁ : ι → ℝ) (π : ι → Fin 4 → ℝ)
    (hpos : ∀ i c, 0 < π i c) (hnorm : ∀ i, ∑ c, π i c = 1)
    (hN : 0 < Fintype.card ι) :
    ∫ f, interactionAB (ipwCellMean y₀₀ π 0 f) (ipwCellMean y₀₁ π 1 f)
      (ipwCellMean y₁₀ π 2 f) (ipwCellMean y₁₁ π 3 f)
      ∂(Measure.pi fun i => bernoulliCell π i) =
      interactionAB (popMean y₀₀) (popMean y₀₁) (popMean y₁₀)
        (popMean y₁₁) := by
  have hI : ∀ (Y : ι → ℝ) (c : Fin 4),
      Integrable (fun f => ipwCellMean Y π c f)
        (Measure.pi fun i => bernoulliCell π i) :=
    fun Y c => integrable_ipwCellMean Y π hpos hnorm c
  have e1 : (∫ f, ipwCellMean y₁₁ π 3 f - ipwCellMean y₁₀ π 2 f
        ∂(Measure.pi fun i => bernoulliCell π i))
        = (∫ f, ipwCellMean y₁₁ π 3 f ∂(Measure.pi fun i => bernoulliCell π i))
          - ∫ f, ipwCellMean y₁₀ π 2 f ∂(Measure.pi fun i => bernoulliCell π i) :=
    integral_sub (hI y₁₁ 3) (hI y₁₀ 2)
  have e2 : (∫ f, ipwCellMean y₁₁ π 3 f - ipwCellMean y₁₀ π 2 f - ipwCellMean y₀₁ π 1 f
        ∂(Measure.pi fun i => bernoulliCell π i))
        = (∫ f, ipwCellMean y₁₁ π 3 f - ipwCellMean y₁₀ π 2 f
          ∂(Measure.pi fun i => bernoulliCell π i))
          - ∫ f, ipwCellMean y₀₁ π 1 f ∂(Measure.pi fun i => bernoulliCell π i) :=
    integral_sub ((hI y₁₁ 3).sub (hI y₁₀ 2)) (hI y₀₁ 1)
  have e3 : (∫ f, ipwCellMean y₁₁ π 3 f - ipwCellMean y₁₀ π 2 f - ipwCellMean y₀₁ π 1 f
        + ipwCellMean y₀₀ π 0 f ∂(Measure.pi fun i => bernoulliCell π i))
        = (∫ f, ipwCellMean y₁₁ π 3 f - ipwCellMean y₁₀ π 2 f - ipwCellMean y₀₁ π 1 f
          ∂(Measure.pi fun i => bernoulliCell π i))
          + ∫ f, ipwCellMean y₀₀ π 0 f ∂(Measure.pi fun i => bernoulliCell π i) :=
    integral_add (((hI y₁₁ 3).sub (hI y₁₀ 2)).sub (hI y₀₁ 1)) (hI y₀₀ 0)
  unfold interactionAB
  rw [integral_div_two, e3, e2, e1,
    integral_ipwCellMean y₁₁ π hpos hnorm hN 3,
    integral_ipwCellMean y₁₀ π hpos hnorm hN 2,
    integral_ipwCellMean y₀₁ π hpos hnorm hN 1,
    integral_ipwCellMean y₀₀ π hpos hnorm hN 0]

end MathlibExt.Probability.Statistics.Experiment
