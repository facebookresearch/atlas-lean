/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Int.Interval
public import Mathlib.Basic.Real.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted

/-!
Source: Optimization Problems, Constant 1b, frozen at commit
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`, `constants/1b.md`, SHA-256
`1c51678108c90a2e841e1b49fa97940e4e1870324e1d949ddcb5b4345a0153ec`.
Complete continuous and discrete model API, adapted from the retained Codex
C1b source repair. The legacy namespace is preserved for declaration identity.
The source-specific known-result requests live in the downstream Wanted leaf.
-/

/-- The number of solutions to `a - b = k` with `a ∈ A` and `b ∈ B`. -/
def Overlap (A B : Finset ℤ) (k : ℤ) : ℕ :=
  ((A.product B).filter fun (a, b) => a - b = k).card

/-- The maximum overlap over all integer differences. -/
noncomputable def MaxOverlap (A B : Finset ℤ) : ℕ :=
  iSup (Overlap A B)

/-- `M(n)`: the minimum maximum overlap over balanced splittings of `{1, …, 2n}`. -/
noncomputable def M (n : ℕ) : ℕ :=
  sInf {MaxOverlap A B | (A : Finset ℤ) (B : Finset ℤ)
    (_disjoint : Disjoint A B)
    (_union : A ∪ B = Finset.Icc (1 : ℤ) (2 * n))
    (_same_card : A.card = B.card)}

 /-- Every overlap count is bounded by the maximum overlap. -/
theorem Overlap_le_MaxOverlap (A B : Finset ℤ) (k : ℤ) :
    Overlap A B k ≤ MaxOverlap A B := by
  apply le_ciSup
  refine ⟨(A.product B).card, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact Finset.card_filter_le _ _

/-- The maximum overlap is attained at some difference. -/
theorem MaxOverlap_attained (A B : Finset ℤ) :
    ∃ k : ℤ, MaxOverlap A B = Overlap A B k := by
  have hbdd : BddAbove (Set.range (Overlap A B)) := by
    refine ⟨(A.product B).card, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact Finset.card_filter_le _ _
  have hne : (Set.range (Overlap A B)).Nonempty :=
    ⟨Overlap A B 0, 0, rfl⟩
  obtain ⟨k, hk⟩ := Nat.sSup_mem hne hbdd
  exact ⟨k, hk.symm⟩

/-- Balanced partitions exist at every size: split `Icc 1 (2n)` in half. -/
theorem balancedPartition_nonempty (n : ℕ) :
    {MaxOverlap A B | (A : Finset ℤ) (B : Finset ℤ)
      (_disjoint : Disjoint A B)
      (_union : A ∪ B = Finset.Icc (1 : ℤ) (2 * n))
      (_same_card : A.card = B.card)}.Nonempty := by
  refine ⟨MaxOverlap (Finset.Icc (1 : ℤ) (n : ℤ))
    (Finset.Icc ((n : ℤ) + 1) (2 * n)), Finset.Icc (1 : ℤ) (n : ℤ),
    Finset.Icc ((n : ℤ) + 1) (2 * n), ?_, ?_, ?_, rfl⟩
  · apply Finset.disjoint_left.mpr
    rintro x hx1 hx2
    simp only [Finset.mem_Icc] at hx1 hx2
    omega
  · ext x
    simp only [Finset.mem_union, Finset.mem_Icc]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
    · intro h
      by_cases hx : x ≤ (n : ℤ)
      · exact Or.inl ⟨h.1, hx⟩
      · exact Or.inr ⟨by omega, h.2⟩
  · simp only [Int.card_Icc]
    congr 1 <;> omega

/-- `M n` is attained by a balanced partition. -/
theorem M_attained (n : ℕ) :
    ∃ (A B : Finset ℤ), Disjoint A B ∧
      A ∪ B = Finset.Icc (1 : ℤ) (2 * n) ∧ A.card = B.card ∧
      M n = MaxOverlap A B := by
  obtain ⟨A, B, hd, hu, hc, hv⟩ :=
    Nat.sInf_mem (balancedPartition_nonempty n)
  exact ⟨A, B, hd, hu, hc, hv.symm⟩

/-- `M n` bounds every balanced partition from below. -/
theorem M_le_MaxOverlap (n : ℕ) (A B : Finset ℤ) (hd : Disjoint A B)
    (hu : A ∪ B = Finset.Icc (1 : ℤ) (2 * n)) (hc : A.card = B.card) :
    M n ≤ MaxOverlap A B :=
  Nat.sInf_le ⟨A, B, hd, hu, hc, rfl⟩

/-- The normalized minimum overlap `M(N) / N`. -/
noncomputable def MinOverlapQuotient (N : ℕ) : ℝ :=
  (M N : ℝ) / N

/-- Uniform asymptotic lower bounds for every balanced integer partition.
The positive size threshold is chosen before the size and partition. -/
def DiscreteUniversalLowerBound (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 0 < N₀ ∧
    ∀ N : ℕ, N₀ ≤ N → ∀ A B : Finset ℤ,
      Disjoint A B → A ∪ B = Finset.Icc (1 : ℤ) (2 * N) → A.card = B.card →
        ∃ x : ℤ, (c - ε) * (N : ℝ) ≤ (Overlap A B x : ℝ)

theorem discreteUniversalLowerBound_zero : DiscreteUniversalLowerBound 0 := by
  intro ε hε
  refine ⟨1, by norm_num, ?_⟩
  intro N _ A B _ _ _
  refine ⟨0, le_trans ?_ (Nat.cast_nonneg _)⟩
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg N)

/-- The source support interval for zero-extended continuous-model functions. -/
def continuousSupportInterval : Set ℝ := Icc (-1) 1

/-- The source translation interval. -/
def continuousTranslationInterval : Set ℝ := Icc (-2) 2

/-- The overlap integrand `f(t) * g(x+t)`. -/
def continuousOverlapIntegrand (f g : ℝ → ℝ) (x t : ℝ) : ℝ :=
  f t * g (x + t)

/-- The overlap at translation `x`. -/
noncomputable def continuousOverlap (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in continuousSupportInterval, continuousOverlapIntegrand f g x t

/-- Overlap values over all source translations. -/
def continuousOverlapValues (f g : ℝ → ℝ) : Set ℝ :=
  continuousOverlap f g '' continuousTranslationInterval

/--
The continuous source family, including Lebesgue-null modifications of Borel
functions. Integrability and all overlap-range properties are consequences below,
never caller-supplied assumptions.
-/
structure ContinuousAdmissible (f g : ℝ → ℝ) : Prop where
  measurable_f : AEMeasurable f volume
  measurable_g : AEMeasurable g volume
  range_f : ∀ t : ℝ, f t ∈ Icc (0 : ℝ) 1
  range_g : ∀ t : ℝ, g t ∈ Icc (0 : ℝ) 1
  zero_outside_f : ∀ t : ℝ, t ∉ continuousSupportInterval → f t = 0
  zero_outside_g : ∀ t : ℝ, t ∉ continuousSupportInterval → g t = 0
  complementary : ∀ t ∈ continuousSupportInterval, f t + g t = 1
  integral_f : (∫ t : ℝ, f t) = 1

theorem ContinuousAdmissible.integrable_f {f g : ℝ → ℝ}
    (h : ContinuousAdmissible f g) : Integrable f := by
  apply IntegrableOn.integrable_of_forall_notMem_eq_zero ?_ h.zero_outside_f
  apply Measure.integrableOn_of_bounded (M := 1) measure_Icc_lt_top.ne
      h.measurable_f.aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (h.range_f t).1]
  exact (h.range_f t).2

theorem ContinuousAdmissible.integrable_g {f g : ℝ → ℝ}
    (h : ContinuousAdmissible f g) : Integrable g := by
  apply IntegrableOn.integrable_of_forall_notMem_eq_zero ?_ h.zero_outside_g
  apply Measure.integrableOn_of_bounded (M := 1) measure_Icc_lt_top.ne
      h.measurable_g.aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (h.range_g t).1]
  exact (h.range_g t).2

theorem ContinuousAdmissible.overlap_integrable {f g : ℝ → ℝ}
    (h : ContinuousAdmissible f g) (x : ℝ) :
    IntegrableOn (continuousOverlapIntegrand f g x) continuousSupportInterval := by
  apply Measure.integrableOn_of_bounded (M := 1) measure_Icc_lt_top.ne
      (h.measurable_f.mul
        (h.measurable_g.comp_quasiMeasurePreserving
          (measurePreserving_add_left volume x).quasiMeasurePreserving)).aestronglyMeasurable
  filter_upwards with t
  change |f t * g (x + t)| ≤ 1
  rw [abs_of_nonneg (mul_nonneg (h.range_f t).1 (h.range_g (x + t)).1)]
  nlinarith [(h.range_f t).2, (h.range_g (x + t)).2, (h.range_f t).1,
    (h.range_g (x + t)).1]

theorem continuousOverlap_nonneg {f g : ℝ → ℝ}
    (h : ContinuousAdmissible f g) (x : ℝ) : 0 ≤ continuousOverlap f g x := by
  apply setIntegral_nonneg measurableSet_Icc
  intro t _
  exact mul_nonneg (h.range_f t).1 (h.range_g (x + t)).1

theorem continuousOverlap_le_one {f g : ℝ → ℝ}
    (h : ContinuousAdmissible f g) (x : ℝ) : continuousOverlap f g x ≤ 1 := by
  calc
    continuousOverlap f g x ≤ ∫ t in continuousSupportInterval, f t := by
      apply setIntegral_mono_on (h.overlap_integrable x) h.integrable_f.integrableOn
        measurableSet_Icc
      intro t _
      dsimp [continuousOverlapIntegrand]
      nlinarith [(h.range_f t).1, (h.range_g (x + t)).1,
        (h.range_g (x + t)).2]
    _ = ∫ t, f t := setIntegral_eq_integral_of_forall_compl_eq_zero h.zero_outside_f
    _ = 1 := h.integral_f

theorem continuousOverlapValues_nonempty (f g : ℝ → ℝ) :
    (continuousOverlapValues f g).Nonempty := by
  refine ⟨continuousOverlap f g 0, ?_⟩
  exact ⟨0, by norm_num [continuousTranslationInterval], rfl⟩

theorem ContinuousAdmissible.overlapValues_mem_unit {f g : ℝ → ℝ}
    (h : ContinuousAdmissible f g) :
    ∀ y ∈ continuousOverlapValues f g, y ∈ Icc (0 : ℝ) 1 := by
  rintro y ⟨x, _, rfl⟩
  exact ⟨continuousOverlap_nonneg h x, continuousOverlap_le_one h x⟩

theorem ContinuousAdmissible.overlapValues_bddAbove {f g : ℝ → ℝ}
    (h : ContinuousAdmissible f g) : BddAbove (continuousOverlapValues f g) := by
  refine ⟨1, ?_⟩
  intro y hy
  exact (h.overlapValues_mem_unit y hy).2

/-- The source supremum over translations. -/
noncomputable def continuousPairScore (f g : ℝ → ℝ) : ℝ :=
  sSup (continuousOverlapValues f g)

theorem continuousPairScore_mem_unit {f g : ℝ → ℝ}
    (h : ContinuousAdmissible f g) : continuousPairScore f g ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨y, hy⟩ := continuousOverlapValues_nonempty f g
  constructor
  · exact le_trans (h.overlapValues_mem_unit y hy).1
      (le_csSup h.overlapValues_bddAbove hy)
  · exact csSup_le ⟨y, hy⟩ fun z hz => (h.overlapValues_mem_unit z hz).2

/-- A constant lower-bounds the score of every source-admissible pair. -/
def ContinuousUniversalLowerBound (c : ℝ) : Prop :=
  ∀ (f g : ℝ → ℝ), ContinuousAdmissible f g → c ≤ continuousPairScore f g

def continuousValidLowerBounds : Set ℝ :=
  {c | ContinuousUniversalLowerBound c}

theorem continuousValidLowerBounds_nonempty : continuousValidLowerBounds.Nonempty := by
  refine ⟨0, ?_⟩
  intro f g h
  exact (continuousPairScore_mem_unit h).1

private noncomputable def continuousHalfIndicator (t : ℝ) : ℝ :=
  (continuousSupportInterval.indicator fun _ => (1 : ℝ) / 2) t

private theorem continuousHalfIndicator_admissible :
    ContinuousAdmissible continuousHalfIndicator continuousHalfIndicator := by
  have hmeas : Measurable continuousHalfIndicator :=
    measurable_const.indicator measurableSet_Icc
  have hrange : ∀ t, continuousHalfIndicator t ∈ Icc (0 : ℝ) 1 := by
    intro t
    by_cases ht : t ∈ continuousSupportInterval
    · simp [continuousHalfIndicator, ht]
      norm_num
    · simp [continuousHalfIndicator, ht]
  have hzero : ∀ t, t ∉ continuousSupportInterval → continuousHalfIndicator t = 0 := by
    intro t ht
    simp [continuousHalfIndicator, ht]
  refine ⟨hmeas.aemeasurable, hmeas.aemeasurable, hrange, hrange, hzero, hzero, ?_, ?_⟩
  · intro t ht
    simp [continuousHalfIndicator, ht]
    norm_num
  · simp [continuousHalfIndicator, continuousSupportInterval,
      MeasureTheory.integral_indicator]
    norm_num

theorem continuousValidLowerBounds_bddAbove : BddAbove continuousValidLowerBounds := by
  refine ⟨1, ?_⟩
  intro c hc
  exact le_trans (hc continuousHalfIndicator continuousHalfIndicator
    continuousHalfIndicator_admissible)
    (continuousPairScore_mem_unit continuousHalfIndicator_admissible).2

/-- The continuous Erdős minimum-overlap constant from Optimization Problem 1b. -/
noncomputable def continuousMinimumOverlapConstant : ℝ :=
  sSup continuousValidLowerBounds

/-- Source notation `C₁ᵦ`. -/
noncomputable abbrev C₁ᵦ : ℝ := continuousMinimumOverlapConstant

theorem continuousMinimumOverlapConstant_isLUB :
    IsLUB continuousValidLowerBounds C₁ᵦ :=
  isLUB_csSup continuousValidLowerBounds_nonempty continuousValidLowerBounds_bddAbove

theorem continuousMinimumOverlapConstant_isUniversalLowerBound :
    ContinuousUniversalLowerBound C₁ᵦ := by
  intro f g h
  apply csSup_le continuousValidLowerBounds_nonempty
  intro c hc
  exact hc f g h

theorem continuousMinimumOverlapConstant_isGreatest :
    IsGreatest continuousValidLowerBounds C₁ᵦ :=
  ⟨continuousMinimumOverlapConstant_isUniversalLowerBound,
    continuousMinimumOverlapConstant_isLUB.1⟩

private theorem continuousHalfIndicator_overlap_le_half (x : ℝ) :
    continuousOverlap continuousHalfIndicator continuousHalfIndicator x ≤ (1 : ℝ) / 2 := by
  have h := continuousHalfIndicator_admissible
  have hhalf (t : ℝ) : continuousHalfIndicator t ≤ (1 : ℝ) / 2 := by
    by_cases ht : t ∈ continuousSupportInterval
    · norm_num [continuousHalfIndicator, ht]
    · norm_num [continuousHalfIndicator, ht]
  calc
    continuousOverlap continuousHalfIndicator continuousHalfIndicator x ≤
        ∫ t in continuousSupportInterval, ((1 : ℝ) / 2) * continuousHalfIndicator t := by
      apply setIntegral_mono_on (h.overlap_integrable x)
        (h.integrable_f.const_mul ((1 : ℝ) / 2)).integrableOn measurableSet_Icc
      intro t _
      dsimp [continuousOverlapIntegrand]
      nlinarith [(h.range_f t).1, hhalf (x + t)]
    _ = (1 : ℝ) / 2 := by
      rw [integral_const_mul,
        setIntegral_eq_integral_of_forall_compl_eq_zero h.zero_outside_f, h.integral_f]
      norm_num

/-- The half-height support indicator bounds the universal minimum-overlap constant. -/
theorem continuousMinimumOverlapConstant_le_half : C₁ᵦ ≤ (1 : ℝ) / 2 := by
  refine le_trans (continuousMinimumOverlapConstant_isUniversalLowerBound
    continuousHalfIndicator continuousHalfIndicator continuousHalfIndicator_admissible) ?_
  apply csSup_le (continuousOverlapValues_nonempty continuousHalfIndicator continuousHalfIndicator)
  rintro y ⟨x, _, rfl⟩
  exact continuousHalfIndicator_overlap_le_half x



end MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted
