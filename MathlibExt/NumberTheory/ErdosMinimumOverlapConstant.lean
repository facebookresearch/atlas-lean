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

/-- **Overlap count of two finite sets of integers.** For finite sets $A, B \subseteq \mathbb{Z}$
and an integer $k$, the overlap of $A$ and $B$ at $k$ is the number of pairs
$(a, b) \in A \times B$ with $a - b = k$. -/
def Overlap (A B : Finset ℤ) (k : ℤ) : ℕ :=
  ((A.product B).filter fun (a, b) => a - b = k).card

/-- **Maximum overlap.** For finite sets $A, B \subseteq \mathbb{Z}$, the maximum overlap of $A$
and $B$ is the natural number obtained as the supremum over all integers $k$ of
$\#\{(a, b) \in A \times B : a - b = k\}$. -/
noncomputable def MaxOverlap (A B : Finset ℤ) : ℕ :=
  iSup (Overlap A B)

/-- **Erdős minimum overlap function.** For a natural number $n$, $M(n)$ is the least value of
the maximum overlap of $A$ and $B$, the supremum over $k \in \mathbb{Z}$ of
$\#\{(a, b) \in A \times B : a - b = k\}$, taken over all pairs of disjoint finite sets
$A, B \subseteq \mathbb{Z}$ with $A \cup B = \{1, \dots, 2n\}$ and $|A| = |B|$. -/
noncomputable def M (n : ℕ) : ℕ :=
  sInf {MaxOverlap A B | (A : Finset ℤ) (B : Finset ℤ)
    (_disjoint : Disjoint A B)
    (_union : A ∪ B = Finset.Icc (1 : ℤ) (2 * n))
    (_same_card : A.card = B.card)}

/-- **Overlaps are bounded by the maximum overlap.** For finite sets $A, B \subseteq \mathbb{Z}$
and every integer $k$, the overlap $\#\{(a, b) \in A \times B : a - b = k\}$ is at most the
maximum overlap of $A$ and $B$. -/
theorem Overlap_le_MaxOverlap (A B : Finset ℤ) (k : ℤ) :
    Overlap A B k ≤ MaxOverlap A B := by
  apply le_ciSup
  refine ⟨(A.product B).card, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact Finset.card_filter_le _ _

/-- **The maximum overlap is attained.** For finite sets $A, B \subseteq \mathbb{Z}$ there is an
integer $k$ such that the maximum overlap of $A$ and $B$, the supremum over $j \in \mathbb{Z}$
of $\#\{(a, b) \in A \times B : a - b = j\}$, equals
$\#\{(a, b) \in A \times B : a - b = k\}$. -/
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

/-- **Balanced partitions of $\{1, \dots, 2n\}$ exist.** For every natural number $n$, the set of
maximum overlaps of $A$ and $B$, taken over all pairs of disjoint finite sets of integers $A$ and
$B$ with $A \cup B = \{1, \dots, 2n\}$ and $|A| = |B|$, is nonempty.

For example, $A = \{1, \dots, n\}$ and $B = \{n + 1, \dots, 2n\}$ is such a pair. -/
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

/-- **The minimum overlap is attained.** For every natural number $n$ there are disjoint finite
sets $A, B \subseteq \mathbb{Z}$ with $A \cup B = \{1, \dots, 2n\}$ and $|A| = |B|$ such that
the minimum overlap $M(n)$ equals the maximum overlap of $A$ and $B$, the supremum over
$k \in \mathbb{Z}$ of $\#\{(a, b) \in A \times B : a - b = k\}$. -/
theorem M_attained (n : ℕ) :
    ∃ (A B : Finset ℤ), Disjoint A B ∧
      A ∪ B = Finset.Icc (1 : ℤ) (2 * n) ∧ A.card = B.card ∧
      M n = MaxOverlap A B := by
  obtain ⟨A, B, hd, hu, hc, hv⟩ :=
    Nat.sInf_mem (balancedPartition_nonempty n)
  exact ⟨A, B, hd, hu, hc, hv.symm⟩

/-- **The minimum overlap bounds every balanced partition.** Let $n$ be a natural number and let
$A, B \subseteq \mathbb{Z}$ be disjoint finite sets with $A \cup B = \{1, \dots, 2n\}$ and
$|A| = |B|$. Then the minimum overlap $M(n)$ is at most the maximum overlap of $A$ and $B$,
the supremum over $k \in \mathbb{Z}$ of $\#\{(a, b) \in A \times B : a - b = k\}$. -/
theorem M_le_MaxOverlap (n : ℕ) (A B : Finset ℤ) (hd : Disjoint A B)
    (hu : A ∪ B = Finset.Icc (1 : ℤ) (2 * n)) (hc : A.card = B.card) :
    M n ≤ MaxOverlap A B :=
  Nat.sInf_le ⟨A, B, hd, hu, hc, rfl⟩

/-- **Normalized minimum overlap.** For a natural number $N$, the normalized minimum overlap is
the real number $M(N) / N$, where $M(N)$ is the Erdős minimum overlap function; for $N = 0$
the quotient is $0$ by the convention $x / 0 = 0$. -/
noncomputable def MinOverlapQuotient (N : ℕ) : ℝ :=
  (M N : ℝ) / N

/-- **Universal asymptotic lower bound for discrete overlaps.** A real number $c$ is a
universal asymptotic lower bound when for every $\varepsilon > 0$ there is a positive integer
$N_0$ such that for every $N \ge N_0$ and all disjoint finite sets $A, B \subseteq \mathbb{Z}$
with $A \cup B = \{1, \dots, 2N\}$ and $|A| = |B|$, some integer $x$ satisfies
$(c - \varepsilon) N \le \#\{(a, b) \in A \times B : a - b = x\}$.

The positive size threshold $N_0$ is chosen before the size $N$ and the partition. -/
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

/-- **Continuous support interval.** The support interval of the continuous minimum-overlap
problem is the closed interval $[-1, 1]$ of real numbers.

Functions in the continuous model are extended by zero outside this interval. -/
def continuousSupportInterval : Set ℝ := Icc (-1) 1

/-- **Translation interval of the continuous overlap model.** The translation interval of the
continuous minimum-overlap model is the closed interval $[-2, 2] \subseteq \mathbb{R}$. -/
def continuousTranslationInterval : Set ℝ := Icc (-2) 2

/-- **Continuous overlap integrand.** For functions $f, g : \mathbb{R} \to \mathbb{R}$ and real
numbers $x$ and $t$, the overlap integrand is $f(t)\,g(x + t)$. -/
def continuousOverlapIntegrand (f g : ℝ → ℝ) (x t : ℝ) : ℝ :=
  f t * g (x + t)

/-- **Continuous overlap.** For functions $f, g : \mathbb{R} \to \mathbb{R}$ and a translation
$x \in \mathbb{R}$, the overlap of $f$ and $g$ at $x$ is $\int_{-1}^{1} f(t)\,g(x + t)\,dt$, the
integral of the overlap integrand over the support interval $[-1, 1]$.

The integral is the Lebesgue (Bochner) integral, which is $0$ when the integrand is not
integrable. -/
noncomputable def continuousOverlap (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in continuousSupportInterval, continuousOverlapIntegrand f g x t

/-- **Continuous overlap values.** For functions $f, g : \mathbb{R} \to \mathbb{R}$, the set of
overlap values of $f$ and $g$ is the image of the translation interval $[-2, 2]$ under the overlap
$x \mapsto \int_{-1}^{1} f(t)\,g(x + t)\,dt$. -/
def continuousOverlapValues (f g : ℝ → ℝ) : Set ℝ :=
  continuousOverlap f g '' continuousTranslationInterval

/-- **Admissible pairs for the continuous minimum-overlap problem.** A pair of functions
$f, g : \mathbb{R} \to \mathbb{R}$ is admissible when $f$ and $g$ are almost everywhere measurable
with respect to Lebesgue measure, take values in $[0, 1]$ at every point, vanish at every point
outside the support interval $[-1, 1]$, satisfy $f(t) + g(t) = 1$ for every $t \in [-1, 1]$, and
satisfy $\int_{\mathbb{R}} f(t)\,dt = 1$.

Since measurability is only required almost everywhere, Lebesgue-null modifications of Borel
functions are included. Integrability and the bounds on the overlap follow from these conditions.
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

/-- **Continuous pair score.** For functions $f, g : \mathbb{R} \to \mathbb{R}$, the pair score of
$f$ and $g$ is the supremum of the overlap values $\int_{-1}^{1} f(t)\,g(x + t)\,dt$ over the
translations $x \in [-2, 2]$.

As with every supremum of real numbers here, it is $0$ when the set is not bounded above; for
admissible pairs the overlap values lie in $[0, 1]$. -/
noncomputable def continuousPairScore (f g : ℝ → ℝ) : ℝ :=
  sSup (continuousOverlapValues f g)

theorem continuousPairScore_mem_unit {f g : ℝ → ℝ}
    (h : ContinuousAdmissible f g) : continuousPairScore f g ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨y, hy⟩ := continuousOverlapValues_nonempty f g
  constructor
  · exact le_trans (h.overlapValues_mem_unit y hy).1
      (le_csSup h.overlapValues_bddAbove hy)
  · exact csSup_le ⟨y, hy⟩ fun z hz => (h.overlapValues_mem_unit z hz).2

/-- **Universal lower bound in the continuous overlap model.** Call a pair of functions
$f, g : \mathbb{R} \to \mathbb{R}$ admissible when $f$ and $g$ are almost everywhere measurable,
take values in $[0, 1]$, vanish outside $[-1, 1]$, satisfy $f + g = 1$ on $[-1, 1]$, and
$\int_{\mathbb{R}} f = 1$, and let the pair score $S(f, g)$ be the supremum over $x \in [-2, 2]$
of $\int_{-1}^{1} f(t)\, g(x + t)\, dt$. A real number $c$ is a universal lower bound when
$c \le S(f, g)$ for every admissible pair $(f, g)$. -/
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

/-- **The continuous Erdős minimum-overlap constant.** For an admissible pair $(f, g)$ let
$S(f, g)$ be its pair score, the supremum over $x \in [-2, 2]$ of
$\int_{-1}^{1} f(t)\,g(x + t)\,dt$. The continuous minimum-overlap constant $C_{1b}$ is the
supremum of the set of real numbers $c$ such that $c \le S(f, g)$ for every admissible pair
$(f, g)$.

Source: Optimization Problems, Constant 1b. -/
noncomputable def continuousMinimumOverlapConstant : ℝ :=
  sSup continuousValidLowerBounds

/-- **Notation $C_{1b}$.** We write $C_{1b}$ for the continuous Erdős minimum-overlap constant. -/
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

/-- **The continuous minimum-overlap constant is at most $1/2$.** The continuous Erdős
minimum-overlap constant $C_{1b}$ satisfies $C_{1b} \le 1/2$.

The bound is witnessed by the admissible pair $f = g$ with value $1/2$ on $[-1, 1]$ and $0$
elsewhere. -/
theorem continuousMinimumOverlapConstant_le_half : C₁ᵦ ≤ (1 : ℝ) / 2 := by
  refine le_trans (continuousMinimumOverlapConstant_isUniversalLowerBound
    continuousHalfIndicator continuousHalfIndicator continuousHalfIndicator_admissible) ?_
  apply csSup_le (continuousOverlapValues_nonempty continuousHalfIndicator continuousHalfIndicator)
  rintro y ⟨x, _, rfl⟩
  exact continuousHalfIndicator_overlap_le_half x



end MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted
