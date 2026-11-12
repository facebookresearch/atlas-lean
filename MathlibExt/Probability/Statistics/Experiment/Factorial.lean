/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Experiment.Assignment
public import MathlibExt.Probability.Causality.CausalIdentification

/-!
# Fixed-cell-size 2x2 factorial designs: cell laws and unbiased contrasts

Complete randomization over four cells of fixed positive sizes; observed
main-effect and interaction contrasts are unbiased with no additivity
assumption. Cell sizes need not be equal.
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

/-- Complete randomization over the four cells: uniform on `cellAssignSpace`. -/
noncomputable def cellAssignment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : Fin 4 → ℕ) : Measure (ι → Fin 4) :=
  Measure.uniformOfFinset (cellAssignSpace n)

/-- Observed mean in cell `c` under the assignment `f`. The name is frozen as
`factorialCellMean`: plain `cellMean` already exists in an unrelated namespace
on main. -/
noncomputable def factorialCellMean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y : ι → ℝ) (c : Fin 4) (f : ι → Fin 4) : ℝ :=
  sampleMean y (Finset.univ.filter fun i => f i = c)

/-- Factorial contrasts as explicit averages of the four cell means: each main
effect is the average of one arm's two cell means minus the average of the
other arm's, halved; the interaction is half the diagonal difference. -/
noncomputable def mainEffectA (m₀₀ m₀₁ m₁₀ m₁₁ : ℝ) : ℝ :=
  (m₁₁ + m₁₀ - m₀₁ - m₀₀) / 2

noncomputable def mainEffectB (m₀₀ m₀₁ m₁₀ m₁₁ : ℝ) : ℝ :=
  (m₁₁ + m₀₁ - m₁₀ - m₀₀) / 2

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

end MathlibExt.Probability.Statistics.Experiment
