/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import MathlibExt.Probability.UniformLaws

/-!
# Measurability of sup functionals over pointwise separable classes

For a class of measurable `[0, 1]` losses that contains a
countable pointwise-dense subclass, the four symmetrization
functionals (uniform deviation, ghost deviation, swapped ghost
sums, empirical Rademacher sup) equal their countable-subclass
versions, hence are measurable functions of the sample. This is
the measurability step behind the empirical-process symmetrization
bounds; threshold classes on `ℝ` satisfy the hypothesis via
rational thresholds.
-/

open MeasureTheory Filter Topology

namespace MathlibExt.Probability.UniformLawsWanted

@[expose] public section

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {ι : Type*}

/-- The ghost deviation `D(x, x') = sup_i |(1/n) ∑ₖ (F i (xₖ) -
F i (x'ₖ))|` between a sample and an independent ghost sample. -/
noncomputable def ghostDeviation (F : ι → 𝓧 → ℝ) {n : ℕ}
    (x x' : Fin n → 𝓧) : ℝ :=
  ⨆ i, |(1 / (n : ℝ)) * ∑ k, (F i (x k) - F i (x' k))|

/-- The swapped ghost sums for a sign vector: `sup_i |(1/n) ∑ₖ
εₖ (F i (xₖ) - F i (x'ₖ))|`, with `εₖ = 1` when `s k` holds and
`-1` otherwise. -/
noncomputable def swappedGhost (F : ι → 𝓧 → ℝ) {n : ℕ}
    (s : Fin n → Bool) (x x' : Fin n → 𝓧) : ℝ :=
  ⨆ i, |(1 / (n : ℝ)) * ∑ k, (if s k then (1 : ℝ) else -1) *
      (F i (x k) - F i (x' k))|

/-- The empirical Rademacher sup at a fixed sample and sign
vector: `sup_i |(1/n) ∑ₖ εₖ F i (xₖ)|`. -/
noncomputable def empRademacher (F : ι → 𝓧 → ℝ) {n : ℕ}
    (s : Fin n → Bool) (x : Fin n → 𝓧) : ℝ :=
  ⨆ i, |(1 / (n : ℝ)) * ∑ k, (if s k then (1 : ℝ) else -1) * F i (x k)|

/-- A class is pointwise separable when some countable subclass
is pointwise dense in it along sequences. -/
def PointwiseSeparable (F : ι → 𝓧 → ℝ) : Prop :=
  ∃ s : Set ι, s.Countable ∧ ∀ i, ∃ seq : ℕ → ι,
    (∀ m, seq m ∈ s) ∧ ∀ z, Tendsto (fun m => F (seq m) z) atTop (𝓝 (F i z))

variable {P : Measure 𝓧} [IsProbabilityMeasure P] {F : ι → 𝓧 → ℝ}
  {s : Set ι}

/-- Supremum over an empty index type vanishes. -/
private theorem ciSup_isEmpty_eq_zero {β : Type*} [IsEmpty β] (g : β → ℝ) :
    (⨆ b, g b) = 0 := by
  have hrange : Set.range g = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro _ ⟨b, -, rfl⟩
    exact IsEmpty.false b
  change sSup (Set.range g) = 0
  rw [hrange, Real.sSup_empty]

/-- A scaled average of terms bounded by one in absolute value is at most one. -/
private theorem abs_avg_sum_le_one {n : ℕ} {g : Fin n → ℝ}
    (hg : ∀ k, |g k| ≤ 1) : |(1 / (n : ℝ)) * ∑ k, g k| ≤ 1 := by
  by_cases hn0 : n = 0
  · subst hn0
    simp
  · have hnR : (0 : ℝ) < n := by
      have hpos : 0 < n := Nat.pos_of_ne_zero hn0
      exact_mod_cast hpos
    have hsum : |∑ k, g k| ≤ n := by
      calc |∑ k, g k| ≤ ∑ k, |g k| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k : Fin n, 1 := Finset.sum_le_sum fun k _ => hg k
        _ = n := by simp
    calc |(1 / (n : ℝ)) * ∑ k, g k| = (1 / (n : ℝ)) * |∑ k, g k| := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
        _ ≤ (1 / (n : ℝ)) * n :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = 1 := one_div_mul_cancel (ne_of_gt hnR)

/-- Supremum over a type equals the supremum over a sequentially dense
subtype when every value is a limit of subtype values. -/
private theorem ciSup_eq_subtype {f : ι → ℝ}
    (hnonneg : ∀ i, 0 ≤ f i) (hbdd : ∀ i, f i ≤ 1)
    (hlim : ∀ i, ∃ seq : ℕ → ι, (∀ m, seq m ∈ s) ∧
      Tendsto (fun m => f (seq m)) atTop (𝓝 (f i))) :
    ⨆ i, f i = ⨆ j : s, f ↑j := by
  have hbddI : BddAbove (Set.range f) := ⟨1, by rintro _ ⟨i, rfl⟩; exact hbdd i⟩
  have hbddS : BddAbove (Set.range fun j : s => f ↑j) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨j, rfl⟩
    exact hbdd j
  by_cases hι : Nonempty ι
  · have ⟨i0⟩ := hι
    apply le_antisymm
    · refine ciSup_le fun i => ?_
      obtain ⟨seq, hmem, hconv⟩ := hlim i
      refine le_of_tendsto hconv (Eventually.of_forall fun m => ?_)
      exact le_ciSup hbddS ⟨seq m, hmem m⟩
    · by_cases hs : Nonempty s
      · refine ciSup_le fun j => ?_
        exact le_ciSup hbddI j.1
      · rw [not_nonempty_iff] at hs
        have hRHS : (⨆ j : s, f ↑j) = 0 :=
          ciSup_isEmpty_eq_zero fun j : s => f ↑j
        rw [hRHS]
        calc (0 : ℝ) ≤ f i0 := hnonneg i0
          _ ≤ ⨆ i, f i := le_ciSup hbddI i0
  · rw [not_nonempty_iff] at hι
    have hL : (⨆ i, f i) = 0 := ciSup_isEmpty_eq_zero f
    have hR : (⨆ j : s, f ↑j) = 0 :=
      ciSup_isEmpty_eq_zero fun j : s => f ↑j
    rw [hL, hR]

/-- Uniform deviation over a pointwise separable class equals
its value over any countable pointwise-dense subclass. -/
theorem uniformDeviation_eq_subclass
    (hF : ∀ i, Measurable (F i))
    (hFbound : ∀ i z, F i z ∈ Set.Icc (0 : ℝ) 1)
    (hdense : ∀ i, ∃ seq : ℕ → ι, (∀ m, seq m ∈ s) ∧
      ∀ z, Tendsto (fun m => F (seq m) z) atTop (𝓝 (F i z)))
    {n : ℕ} (hn : 1 ≤ n) (x : Fin n → 𝓧) :
    uniformDeviation P F hn x =
      uniformDeviation P (fun j : s => F j) hn x := by
  have hnR : (0 : ℝ) < n := by
    have hpos : 0 < n := by omega
    exact_mod_cast hpos
  have havg_mem : ∀ i, (1 / (n : ℝ)) * ∑ k, F i (x k) ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    have hsum_nonneg : 0 ≤ ∑ k, F i (x k) :=
      Finset.sum_nonneg fun k _ => (hFbound i (x k)).1
    have hsum_le : ∑ k, F i (x k) ≤ n := by
      calc ∑ k, F i (x k) ≤ ∑ _k : Fin n, 1 :=
            Finset.sum_le_sum fun k _ => (hFbound i (x k)).2
        _ = n := by simp
    have h1n_nonneg : 0 ≤ 1 / (n : ℝ) := by positivity
    rw [Set.mem_Icc]
    refine ⟨mul_nonneg h1n_nonneg hsum_nonneg, ?_⟩
    calc (1 / (n : ℝ)) * ∑ k, F i (x k) ≤ (1 / (n : ℝ)) * n :=
          mul_le_mul_of_nonneg_left hsum_le h1n_nonneg
      _ = 1 := one_div_mul_cancel (ne_of_gt hnR)
  have hint_mem : ∀ i, (∫ y, F i y ∂P) ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    have hFint : Integrable (F i) P := by
      refine Integrable.of_bound (hF i).aestronglyMeasurable 1 ?_
      apply Eventually.of_forall
      intro y
      have hbd := hFbound i y
      rw [Set.mem_Icc] at hbd
      rw [Real.norm_eq_abs, abs_of_nonneg hbd.1]
      exact hbd.2
    rw [Set.mem_Icc]
    refine ⟨integral_nonneg_of_ae (Eventually.of_forall fun y => ?_),
      ?_⟩
    · exact (hFbound i y).1
    · have hle : (∫ y, F i y ∂P) ≤ ∫ _y, (1 : ℝ) ∂P := by
        refine integral_mono_ae hFint (integrable_const 1) ?_
        apply Eventually.of_forall
        intro y
        exact (hFbound i y).2
      have h1 : (∫ _y, (1 : ℝ) ∂P) = 1 := by simp [integral_const]
      rw [h1] at hle
      exact hle
  simp only [uniformDeviation]
  apply ciSup_eq_subtype
  · intro i
    exact abs_nonneg _
  · intro i
    show |((1 / (n : ℝ)) * ∑ k, F i (x k)) - ∫ y, F i y ∂P| ≤ 1
    obtain ⟨ha0, ha1⟩ := havg_mem i
    obtain ⟨hb0, hb1⟩ := hint_mem i
    rw [abs_le]
    constructor <;> linarith
  · intro i
    obtain ⟨seq, hmem, hconv⟩ := hdense i
    refine ⟨seq, hmem, ?_⟩
    show Tendsto (fun m => |((1 / (n : ℝ)) * ∑ k, F (seq m) (x k)) -
        ∫ y, F (seq m) y ∂P|)
      atTop (𝓝 (|((1 / (n : ℝ)) * ∑ k, F i (x k)) - ∫ y, F i y ∂P|))
    have hsum : Tendsto (fun m => ∑ k, F (seq m) (x k)) atTop
        (𝓝 (∑ k, F i (x k))) :=
      tendsto_finsetSum Finset.univ fun k _ => hconv (x k)
    have havg : Tendsto (fun m => (1 / (n : ℝ)) * ∑ k, F (seq m) (x k)) atTop
        (𝓝 ((1 / (n : ℝ)) * ∑ k, F i (x k))) :=
      Tendsto.const_mul _ hsum
    have hint : Tendsto (fun m => ∫ y, F (seq m) y ∂P) atTop
        (𝓝 (∫ y, F i y ∂P)) := by
      refine MeasureTheory.tendsto_integral_of_dominated_convergence
        (F := fun m y => F (seq m) y) (f := F i) (fun _ => 1) ?_ ?_ ?_ ?_
      · intro m
        exact (hF (seq m)).aestronglyMeasurable
      · exact integrable_const 1
      · intro m
        apply Eventually.of_forall
        intro y
        change ‖F (seq m) y‖ ≤ 1
        have hbd := hFbound (seq m) y
        rw [Set.mem_Icc] at hbd
        rw [Real.norm_eq_abs, abs_of_nonneg hbd.1]
        exact hbd.2
      · apply Eventually.of_forall
        intro y
        exact hconv y
    exact (havg.sub hint).abs

section EqSubclass
variable {𝓧 : Type*} {ι : Type*} {F : ι → 𝓧 → ℝ} {s : Set ι}

/-- Ghost deviation over a pointwise separable class equals its
countable-subclass version. -/
theorem ghostDeviation_eq_subclass
    (hFbound : ∀ i z, F i z ∈ Set.Icc (0 : ℝ) 1)
    (hdense : ∀ i, ∃ seq : ℕ → ι, (∀ m, seq m ∈ s) ∧
      ∀ z, Tendsto (fun m => F (seq m) z) atTop (𝓝 (F i z)))
    {n : ℕ} (x x' : Fin n → 𝓧) :
    ghostDeviation F x x' = ghostDeviation (fun j : s => F j) x x' := by
  simp only [ghostDeviation]
  apply ciSup_eq_subtype
  · intro i
    exact abs_nonneg _
  · intro i
    show |(1 / (n : ℝ)) * ∑ k, (F i (x k) - F i (x' k))| ≤ 1
    apply abs_avg_sum_le_one
    intro k
    show |F i (x k) - F i (x' k)| ≤ 1
    have ha := hFbound i (x k)
    have hb := hFbound i (x' k)
    rw [Set.mem_Icc] at ha hb
    obtain ⟨ha0, ha1⟩ := ha
    obtain ⟨hb0, hb1⟩ := hb
    rw [abs_le]
    constructor <;> linarith
  · intro i
    obtain ⟨seq, hmem, hconv⟩ := hdense i
    refine ⟨seq, hmem, ?_⟩
    show Tendsto (fun m => |(1 / (n : ℝ)) *
        ∑ k, (F (seq m) (x k) - F (seq m) (x' k))|)
      atTop (𝓝 (|(1 / (n : ℝ)) * ∑ k, (F i (x k) - F i (x' k))|))
    have hsum : Tendsto (fun m => ∑ k, (F (seq m) (x k) - F (seq m) (x' k)))
        atTop (𝓝 (∑ k, (F i (x k) - F i (x' k)))) :=
      tendsto_finsetSum Finset.univ fun k _ => (hconv (x k)).sub (hconv (x' k))
    have hscale := Tendsto.const_mul (1 / (n : ℝ)) hsum
    exact hscale.abs

/-- Swapped ghost sums over a pointwise separable class equal
their countable-subclass versions. -/
theorem swappedGhost_eq_subclass
    (hFbound : ∀ i z, F i z ∈ Set.Icc (0 : ℝ) 1)
    (hdense : ∀ i, ∃ seq : ℕ → ι, (∀ m, seq m ∈ s) ∧
      ∀ z, Tendsto (fun m => F (seq m) z) atTop (𝓝 (F i z)))
    {n : ℕ} (t : Fin n → Bool) (x x' : Fin n → 𝓧) :
    swappedGhost F t x x' = swappedGhost (fun j : s => F j) t x x' := by
  simp only [swappedGhost]
  apply ciSup_eq_subtype
  · intro i
    exact abs_nonneg _
  · intro i
    show |(1 / (n : ℝ)) * ∑ k, (if t k then (1 : ℝ) else -1) *
        (F i (x k) - F i (x' k))| ≤ 1
    apply abs_avg_sum_le_one
    intro k
    show |(if t k then (1 : ℝ) else -1) * (F i (x k) - F i (x' k))| ≤ 1
    have hε : |if t k then (1 : ℝ) else -1| = 1 := by
      by_cases h : t k = true <;> simp [h]
    have ha := hFbound i (x k)
    have hb := hFbound i (x' k)
    rw [Set.mem_Icc] at ha hb
    obtain ⟨ha0, ha1⟩ := ha
    obtain ⟨hb0, hb1⟩ := hb
    rw [abs_mul, hε, one_mul, abs_le]
    constructor <;> linarith
  · intro i
    obtain ⟨seq, hmem, hconv⟩ := hdense i
    refine ⟨seq, hmem, ?_⟩
    show Tendsto (fun m => |(1 / (n : ℝ)) * ∑ k, (if t k then (1 : ℝ) else -1) *
        (F (seq m) (x k) - F (seq m) (x' k))|)
      atTop (𝓝 (|(1 / (n : ℝ)) * ∑ k, (if t k then (1 : ℝ) else -1) *
        (F i (x k) - F i (x' k))|))
    have hsum : Tendsto (fun m => ∑ k, (if t k then (1 : ℝ) else -1) *
          (F (seq m) (x k) - F (seq m) (x' k)))
        atTop (𝓝 (∑ k, (if t k then (1 : ℝ) else -1) *
          (F i (x k) - F i (x' k)))) :=
      tendsto_finsetSum Finset.univ fun k _ =>
        Tendsto.const_mul _ ((hconv (x k)).sub (hconv (x' k)))
    have hscale := Tendsto.const_mul (1 / (n : ℝ)) hsum
    exact hscale.abs

/-- Empirical Rademacher sup over a pointwise separable class
equals its countable-subclass version. -/
theorem empRademacher_eq_subclass
    (hFbound : ∀ i z, F i z ∈ Set.Icc (0 : ℝ) 1)
    (hdense : ∀ i, ∃ seq : ℕ → ι, (∀ m, seq m ∈ s) ∧
      ∀ z, Tendsto (fun m => F (seq m) z) atTop (𝓝 (F i z)))
    {n : ℕ} (t : Fin n → Bool) (x : Fin n → 𝓧) :
    empRademacher F t x = empRademacher (fun j : s => F j) t x := by
  simp only [empRademacher]
  apply ciSup_eq_subtype
  · intro i
    exact abs_nonneg _
  · intro i
    show |(1 / (n : ℝ)) * ∑ k, (if t k then (1 : ℝ) else -1) * F i (x k)| ≤ 1
    apply abs_avg_sum_le_one
    intro k
    show |(if t k then (1 : ℝ) else -1) * F i (x k)| ≤ 1
    have hε : |if t k then (1 : ℝ) else -1| = 1 := by
      by_cases h : t k = true <;> simp [h]
    have ha := hFbound i (x k)
    rw [Set.mem_Icc] at ha
    obtain ⟨ha0, ha1⟩ := ha
    rw [abs_mul, hε, one_mul, abs_le]
    constructor <;> linarith
  · intro i
    obtain ⟨seq, hmem, hconv⟩ := hdense i
    refine ⟨seq, hmem, ?_⟩
    show Tendsto (fun m => |(1 / (n : ℝ)) * ∑ k,
        (if t k then (1 : ℝ) else -1) * F (seq m) (x k)|)
      atTop (𝓝 (|(1 / (n : ℝ)) * ∑ k,
        (if t k then (1 : ℝ) else -1) * F i (x k)|))
    have hsum : Tendsto (fun m => ∑ k, (if t k then (1 : ℝ) else -1) *
          F (seq m) (x k))
        atTop (𝓝 (∑ k, (if t k then (1 : ℝ) else -1) * F i (x k))) :=
      tendsto_finsetSum Finset.univ fun k _ =>
        Tendsto.const_mul _ (hconv (x k))
    have hscale := Tendsto.const_mul (1 / (n : ℝ)) hsum
    exact hscale.abs
end EqSubclass

/-- Measurability of the uniform deviation for a pointwise
separable class. -/
theorem measurable_uniformDeviation_of_pointwiseSeparable
    (hF : ∀ i, Measurable (F i))
    (hFbound : ∀ i z, F i z ∈ Set.Icc (0 : ℝ) 1)
    (hsep : PointwiseSeparable F) {n : ℕ} (hn : 1 ≤ n) :
    Measurable (uniformDeviation P F hn) := by
  obtain ⟨s, hs, hdense⟩ := hsep
  have hcount := hs.to_subtype
  have heq : ∀ x : Fin n → 𝓧, uniformDeviation P F hn x =
      uniformDeviation P (fun j : s => F ↑j) hn x :=
    fun x => uniformDeviation_eq_subclass hF hFbound hdense hn x
  have hfun : uniformDeviation P F hn =
      uniformDeviation P (fun j : s => F ↑j) hn := funext heq
  rw [hfun]
  exact measurable_uniformDeviation (F := fun j : s => F ↑j) (fun j => hF ↑j) hn

/-- Measurability of the ghost deviation for a pointwise
separable class. -/
theorem measurable_ghostDeviation_of_pointwiseSeparable
    (hF : ∀ i, Measurable (F i))
    (hFbound : ∀ i z, F i z ∈ Set.Icc (0 : ℝ) 1)
    (hsep : PointwiseSeparable F) {n : ℕ} :
    Measurable (fun p : (Fin n → 𝓧) × (Fin n → 𝓧) =>
      ghostDeviation F p.1 p.2) := by
  obtain ⟨s, hs, hdense⟩ := hsep
  have hcount := hs.to_subtype
  have heq : ∀ p : (Fin n → 𝓧) × (Fin n → 𝓧),
      ghostDeviation F p.1 p.2 =
        ghostDeviation (fun j : s => F ↑j) p.1 p.2 :=
    fun p => ghostDeviation_eq_subclass hFbound hdense p.1 p.2
  rw [funext heq]
  simp only [ghostDeviation]
  apply Measurable.iSup
  intro j
  show Measurable fun p : (Fin n → 𝓧) × (Fin n → 𝓧) =>
    |(1 / (n : ℝ)) * ∑ k, (F ↑j (p.1 k) - F ↑j (p.2 k))|
  apply Measurable.abs
  refine Measurable.const_mul ?_ (1 / (n : ℝ))
  refine Finset.measurable_sum Finset.univ fun k _ => ?_
  show Measurable fun p : (Fin n → 𝓧) × (Fin n → 𝓧) =>
    (F ↑j (p.1 k) - F ↑j (p.2 k))
  refine Measurable.sub ?_ ?_
  · exact (hF ↑j).comp ((measurable_pi_apply k).comp measurable_fst)
  · exact (hF ↑j).comp ((measurable_pi_apply k).comp measurable_snd)

/-- Measurability of the empirical Rademacher sup for a pointwise
separable class. -/
theorem measurable_empRademacher_of_pointwiseSeparable
    (hF : ∀ i, Measurable (F i))
    (hFbound : ∀ i z, F i z ∈ Set.Icc (0 : ℝ) 1)
    (hsep : PointwiseSeparable F) {n : ℕ} (t : Fin n → Bool) :
    Measurable (empRademacher F t) := by
  obtain ⟨s, hs, hdense⟩ := hsep
  have hcount := hs.to_subtype
  have heq : ∀ x : Fin n → 𝓧, empRademacher F t x =
      empRademacher (fun j : s => F ↑j) t x :=
    fun x => empRademacher_eq_subclass hFbound hdense t x
  have hfun : empRademacher F t = empRademacher (fun j : s => F ↑j) t :=
    funext heq
  rw [hfun]
  change Measurable fun x : Fin n → 𝓧 => empRademacher (fun j : s => F ↑j) t x
  simp only [empRademacher]
  apply Measurable.iSup
  intro j
  show Measurable fun x : Fin n → 𝓧 =>
    |(1 / (n : ℝ)) * ∑ k, (if t k then (1 : ℝ) else -1) * F ↑j (x k)|
  apply Measurable.abs
  refine Measurable.const_mul ?_ (1 / (n : ℝ))
  refine Finset.measurable_sum Finset.univ fun k _ => ?_
  show Measurable fun x : Fin n → 𝓧 =>
    (if t k then (1 : ℝ) else -1) * F ↑j (x k)
  exact Measurable.const_mul ((hF ↑j).comp (measurable_pi_apply k)) _

/-- Measurability of the swapped ghost sums for a pointwise
separable class. -/
theorem measurable_swappedGhost_of_pointwiseSeparable
    (hF : ∀ i, Measurable (F i))
    (hFbound : ∀ i z, F i z ∈ Set.Icc (0 : ℝ) 1)
    (hsep : PointwiseSeparable F) {n : ℕ} (t : Fin n → Bool) :
    Measurable (fun p : (Fin n → 𝓧) × (Fin n → 𝓧) =>
      swappedGhost F t p.1 p.2) := by
  obtain ⟨s, hs, hdense⟩ := hsep
  have hcount := hs.to_subtype
  have heq : ∀ p : (Fin n → 𝓧) × (Fin n → 𝓧),
      swappedGhost F t p.1 p.2 =
        swappedGhost (fun j : s => F ↑j) t p.1 p.2 :=
    fun p => swappedGhost_eq_subclass hFbound hdense t p.1 p.2
  rw [funext heq]
  simp only [swappedGhost]
  apply Measurable.iSup
  intro j
  show Measurable fun p : (Fin n → 𝓧) × (Fin n → 𝓧) =>
    |(1 / (n : ℝ)) * ∑ k, (if t k then (1 : ℝ) else -1) *
      (F ↑j (p.1 k) - F ↑j (p.2 k))|
  apply Measurable.abs
  refine Measurable.const_mul ?_ (1 / (n : ℝ))
  refine Finset.measurable_sum Finset.univ fun k _ => ?_
  show Measurable fun p : (Fin n → 𝓧) × (Fin n → 𝓧) =>
    (if t k then (1 : ℝ) else -1) * (F ↑j (p.1 k) - F ↑j (p.2 k))
  refine Measurable.const_mul ?_ _
  refine Measurable.sub ?_ ?_
  · exact (hF ↑j).comp ((measurable_pi_apply k).comp measurable_fst)
  · exact (hF ↑j).comp ((measurable_pi_apply k).comp measurable_snd)

/-- Threshold classes on `ℝ` are pointwise separable. -/
theorem pointwiseSeparable_threshold :
    PointwiseSeparable (𝓧 := ℝ) (fun t : ℝ => fun z : ℝ =>
      if z ≤ t then (1 : ℝ) else 0) := by
  refine ⟨Set.range ((↑) : ℚ → ℝ), Set.countable_range _, fun t => ?_⟩
  obtain ⟨u, -, hgt, hlim⟩ := Real.exists_seq_rat_strictAnti_tendsto t
  refine ⟨fun m => (↑(u m) : ℝ), fun m => ⟨u m, rfl⟩, fun z => ?_⟩
  change Tendsto (fun m => if z ≤ (↑(u m) : ℝ) then (1 : ℝ) else 0)
    atTop (𝓝 (if z ≤ t then (1 : ℝ) else 0))
  by_cases hz : z ≤ t
  · rw [ite_eq_left hz]
    have hev : (fun _ : ℕ => (1 : ℝ)) =ᶠ[atTop]
        (fun m => if z ≤ (↑(u m) : ℝ) then (1 : ℝ) else 0) := by
      filter_upwards with m
      show (1 : ℝ) = if z ≤ (↑(u m) : ℝ) then (1 : ℝ) else 0
      rw [ite_eq_left (le_trans hz (le_of_lt (hgt m)))]
    exact Tendsto.congr' hev tendsto_const_nhds
  · rw [ite_eq_right hz]
    have htz : t < z := lt_of_not_ge hz
    have hev : (fun _ : ℕ => (0 : ℝ)) =ᶠ[atTop]
        (fun m => if z ≤ (↑(u m) : ℝ) then (1 : ℝ) else 0) := by
      filter_upwards [hlim.eventually (gt_mem_nhds htz)] with m hm
      show (0 : ℝ) = if z ≤ (↑(u m) : ℝ) then (1 : ℝ) else 0
      rw [ite_eq_right (not_le_of_gt hm)]
    exact Tendsto.congr' hev tendsto_const_nhds

end

end UniformLawsWanted

end Probability

end MathlibExt
