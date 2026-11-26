/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MathlibExt.GameTheory.Regret
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import MathlibExt.InformationTheory.FiniteEntropy

/-!
# Proper scoring rules: quadratic, logarithmic and linear rules

Definitions, statements and proofs for scoring rules on a finite outcome
type, following Roughgarden, Scoring Rules and Peer Prediction, 2016.

Clause map (specification clause to declaration and back):

- P1 (scoring rule, expected score, proper, strictly proper):
  `ScoringRule`, `expectedScore`, `IsProper`, `IsStrictlyProper`;
  beliefs and reports range over the probability simplex
  `MathlibExt.GameTheory.Regret.IsSimplex`.
- P2 (quadratic rule is strictly proper, Proposition 1.3):
  `quadraticRule`, `quadraticRule_isStrictlyProper`.
- P3 (log-score disjunction, Proposition 1.5, real statement):
  `logScore_disjunction`, `logScore_lt_of_fullSupport`.
- P3n (real whole-simplex log rule is not strictly proper):
  `logRule`, `logRule_notStrictlyProper`.
- P4 (linear rule is not proper):
  `linearRule`, `linearRule_notProper`.

Each declaration docstring names the clause it belongs to.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.GameTheory.ProperScoring

open scoped BigOperators
open MathlibExt.GameTheory.Regret (IsSimplex isSimplex_iff)

/-- P1: a scoring rule maps a reported distribution and an outcome to a score. -/
abbrev ScoringRule (X : Type*) : Type _ := (X → ℝ) → X → ℝ

/-- P1: the score `∑ i, p i * S q i` of reporting `q` under the weights `p`; when `p` is a
probability distribution on `X` (the belief), it is the expected score of reporting `q`. -/
noncomputable def expectedScore (X : Type*) [Fintype X]
    (S : ScoringRule X) (p q : X → ℝ) : ℝ :=
  ∑ i, p i * S q i

/-- P1: properness. For all probability distributions `p` (the belief) and `q` (the report) on
`X`, reporting `q` scores at most truthful reporting:
`expectedScore X S p q ≤ expectedScore X S p p`. -/
def IsProper (X : Type*) [Fintype X] (S : ScoringRule X) : Prop :=
  ∀ p q, IsSimplex p → IsSimplex q →
    expectedScore X S p q ≤ expectedScore X S p p

/-- P1: strict properness. `S` is proper, and for probability distributions `p` and `q` on `X`,
`expectedScore X S p q = expectedScore X S p p` forces `q = p`: truthful reporting is the unique
maximizer. -/
def IsStrictlyProper (X : Type*) [Fintype X] (S : ScoringRule X) : Prop :=
  IsProper X S ∧ ∀ p q, IsSimplex p → IsSimplex q →
    expectedScore X S p q = expectedScore X S p p → q = p

/-- P2: the quadratic scoring rule, `quadraticRule X q i = q i - (1 / 2) * ∑ j, q j ^ 2`
(form (2) of the source). -/
noncomputable def quadraticRule (X : Type*) [Fintype X] : ScoringRule X :=
  fun q i => q i - (1 / 2) * ∑ j, q j ^ 2

/-- P2: the quadratic rule is strictly proper (Proposition 1.3). -/
theorem quadraticRule_isStrictlyProper (X : Type*) [Fintype X] :
    IsStrictlyProper X (quadraticRule X) := by
  constructor
  · intro p q hp _hq
    obtain ⟨-, hp_sum⟩ := (isSimplex_iff p).mp hp
    have hEq : ∀ r : X → ℝ, (∑ i, p i * (r i - (1 / 2) * ∑ j, r j ^ 2))
        = (∑ i, p i * r i) - (1 / 2) * ∑ j, r j ^ 2 := by
      intro r
      simp only [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp_sum, one_mul]
    have hSq : ∀ i, (p i - q i) ^ 2
        = p i ^ 2 - 2 * (p i * q i) + q i ^ 2 := by
      intro i; ring
    have hSum : (∑ i, (p i - q i) ^ 2)
        = (∑ i, p i ^ 2) - 2 * (∑ i, p i * q i)
          + (∑ i, q i ^ 2) := by
      simp only [hSq]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hNonneg : 0 ≤ (∑ i, (p i - q i) ^ 2) := by
      apply Finset.sum_nonneg
      intro i _
      exact sq_nonneg _
    simp only [expectedScore, quadraticRule]
    rw [hEq q, hEq p]
    simp only [← pow_two]
    linarith [hSum, hNonneg]
  · intro p q hp _hq heq
    obtain ⟨-, hp_sum⟩ := (isSimplex_iff p).mp hp
    have hEq : ∀ r : X → ℝ, (∑ i, p i * (r i - (1 / 2) * ∑ j, r j ^ 2))
        = (∑ i, p i * r i) - (1 / 2) * ∑ j, r j ^ 2 := by
      intro r
      simp only [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp_sum, one_mul]
    have hSq : ∀ i, (p i - q i) ^ 2
        = p i ^ 2 - 2 * (p i * q i) + q i ^ 2 := by
      intro i; ring
    have hSum : (∑ i, (p i - q i) ^ 2)
        = (∑ i, p i ^ 2) - 2 * (∑ i, p i * q i)
          + (∑ i, q i ^ 2) := by
      simp only [hSq]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [expectedScore, quadraticRule] at heq
    rw [hEq q, hEq p] at heq
    simp only [← pow_two] at heq
    have hZero : (∑ i, (p i - q i) ^ 2) = 0 := by
      linarith [hSum, heq]
    have hEach := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => sq_nonneg (p i - q i))).mp hZero
    have hPt : ∀ i, p i = q i := by
      intro i
      have h0 := hEach i (Finset.mem_univ i)
      rw [sq_eq_zero_iff] at h0
      exact sub_eq_zero.mp h0
    exact (funext hPt).symm

/-- P3: log-score disjunction. For probability distributions `p` and `q` on the same finite
outcome set with `q ≠ p`, either `q` misses part of the support of `p`, that is `0 < p i` and
`q i = 0` for some outcome `i`, or the expected log score of reporting `q` is strictly below
that of truthful reporting: `∑ i, p i * Real.log (q i) < ∑ i, p i * Real.log (p i)`. -/
theorem logScore_disjunction (X : Type*) [Fintype X]
    (p q : X → ℝ) (hp : IsSimplex p) (hq : IsSimplex q)
    (hne : q ≠ p) :
    (∃ i, 0 < p i ∧ q i = 0) ∨
      ∑ i, p i * Real.log (q i) < ∑ i, p i * Real.log (p i) := by
  classical
  by_cases hsupp : ∃ i, 0 < p i ∧ q i = 0
  · exact Or.inl hsupp
  · right
    push Not at hsupp
    obtain ⟨hp0, hpsum⟩ := (isSimplex_iff p).mp hp
    obtain ⟨hq0, hqsum⟩ := (isSimplex_iff q).mp hq
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hple1 : ∀ a, p a ≤ 1 := fun a => by
      calc p a ≤ ∑ i, p i :=
            Finset.single_le_sum (fun i _ => hp0 i) (Finset.mem_univ a)
        _ = 1 := hpsum
    have hqle1 : ∀ a, q a ≤ 1 := fun a => by
      calc q a ≤ ∑ i, q i :=
            Finset.single_le_sum (fun i _ => hq0 i) (Finset.mem_univ a)
        _ = 1 := hqsum
    -- Local discrete measurable structure; not part of the statement.
    let mX : MeasurableSpace X := ⊤
    have hmX : @MeasurableSingletonClass X mX := ⟨fun _ => trivial⟩
    -- Coordinate-preserving simplex-to-PMF conversion.
    have hPsum : ∑ a, ENNReal.ofReal (p a) = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hp0 a), hpsum,
        ENNReal.ofReal_one]
    have hQsum : ∑ a, ENNReal.ofReal (q a) = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hq0 a), hqsum,
        ENNReal.ofReal_one]
    set P : PMF X :=
      PMF.ofFintype (fun a => ENNReal.ofReal (p a)) hPsum
    set Q : PMF X :=
      PMF.ofFintype (fun a => ENNReal.ofReal (q a)) hQsum
    have hPa : ∀ a, P a = ENNReal.ofReal (p a) := fun a => rfl
    have hQa : ∀ a, Q a = ENNReal.ofReal (q a) := fun a => rfl
    have hPto : ∀ a, (P a).toReal = p a := fun a => by
      rw [hPa a]
      exact ENNReal.toReal_ofReal (hp0 a)
    have hQto : ∀ a, (Q a).toReal = q a := fun a => by
      rw [hQa a]
      exact ENNReal.toReal_ofReal (hq0 a)
    have hQ0 : ∀ a, Q a = 0 ↔ q a = 0 := fun a => by
      rw [hQa a, ENNReal.ofReal_eq_zero]
      exact ⟨fun h => le_antisymm h (hq0 a), fun h => le_of_eq h⟩
    -- On the finite branch, vanishing `q` forces vanishing `p`.
    have hsupp' : ∀ a, Q a = 0 → p a = 0 := by
      intro a hQa0
      have hqa0 : q a = 0 := (hQ0 a).mp hQa0
      by_contra hne0
      exact hsupp a (lt_of_le_of_ne' (hp0 a) hne0) hqa0
    -- Hence the cross-entropy is finite.
    have hCENE : InformationTheory.crossEntropy P Q ≠ ⊤ := by
      rw [Ne, InformationTheory.crossEntropy_eq_top_iff]
      rintro ⟨a, hQa0, hPa0⟩
      have hpa : 0 < p a := by
        by_contra h
        push Not at h
        have h0 : p a = 0 := le_antisymm h (hp0 a)
        exact hPa0 (by rw [hPa a, h0]; exact ENNReal.ofReal_zero)
      exact hsupp a hpa ((hQ0 a).mp hQa0)
    have hQP : Q ≠ P := by
      intro hcon
      apply hne
      apply funext
      intro a
      rw [← hQto a, ← hPto a, hcon]
    -- Gibbs' inequality, strict since the PMFs differ.
    have hGibbs : ENNReal.ofReal (InformationTheory.shannonEntropy P)
        ≤ InformationTheory.crossEntropy P Q :=
      @InformationTheory.shannonEntropy_le_crossEntropy X inferInstance
        mX hmX P Q
    have hEq : InformationTheory.crossEntropy P Q
          = ENNReal.ofReal (InformationTheory.shannonEntropy P) ↔ Q = P :=
      @InformationTheory.crossEntropy_eq_shannonEntropy_iff X inferInstance
        mX hmX P Q
    have hlt : ENNReal.ofReal (InformationTheory.shannonEntropy P)
        < InformationTheory.crossEntropy P Q :=
      lt_of_le_of_ne hGibbs (fun h => hQP (hEq.mp h.symm))
    have hToReal :
        (ENNReal.ofReal (InformationTheory.shannonEntropy P)).toReal
          < (InformationTheory.crossEntropy P Q).toReal :=
      (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hCENE).mpr hlt
    -- Entropy side: negative expected log-score in bits.
    have hS : InformationTheory.shannonEntropy P
        = -(∑ a, p a * Real.log (p a)) / Real.log 2 := by
      have hdef : InformationTheory.shannonEntropy P
          = (∑ a, Real.negMulLog (P a).toReal) / Real.log 2 := rfl
      rw [hdef]
      congr 1
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro a _
      rw [hPto a]
      change -p a * Real.log (p a) = _
      ring
    have hSnn : 0 ≤ InformationTheory.shannonEntropy P := by
      rw [hS]
      apply div_nonneg (neg_nonneg.mpr ?_) (le_of_lt hlog2)
      apply Finset.sum_nonpos
      intro a _
      apply mul_nonpos_of_nonneg_of_nonpos (hp0 a)
      exact Real.log_nonpos (hp0 a) (hple1 a)
    -- Cross-entropy side, per term.
    have hterm : ∀ a, (P a * InformationTheory.surprisal (Q a)).toReal
        = -(p a * Real.log (q a)) / Real.log 2 := by
      intro a
      by_cases hQa0 : Q a = 0
      · have hpa0 : p a = 0 := hsupp' a hQa0
        have hPa0 : P a = 0 := by
          rw [hPa a, hpa0]
          exact ENNReal.ofReal_zero
        rw [hPa0, zero_mul, ENNReal.toReal_zero, hpa0, zero_mul, neg_zero,
          zero_div]
      · have hsurp := InformationTheory.surprisal_of_ne_zero hQa0
        have hnn : 0 ≤ -Real.logb 2 (q a) :=
          neg_nonneg.mpr (Real.logb_nonpos one_lt_two (hq0 a) (hqle1 a))
        have hlogb : Real.logb 2 (q a) = Real.log (q a) / Real.log 2 := rfl
        rw [hsurp, hPa, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hp0 a),
          hQto a, ENNReal.toReal_ofReal hnn, hlogb]
        ring
    have hCE : (InformationTheory.crossEntropy P Q).toReal
        = -(∑ a, p a * Real.log (q a)) / Real.log 2 := by
      have hdef : InformationTheory.crossEntropy P Q
          = ∑ a, P a * InformationTheory.surprisal (Q a) := rfl
      rw [hdef]
      have hfin : ∀ a ∈ Finset.univ,
          P a * InformationTheory.surprisal (Q a) ≠ ⊤ := by
        intro a _
        by_cases hQa0 : Q a = 0
        · have hPa0 : P a = 0 := by
            rw [hPa a, hsupp' a hQa0]
            exact ENNReal.ofReal_zero
          rw [hPa0, zero_mul]
          exact ENNReal.zero_ne_top
        · rw [InformationTheory.surprisal_of_ne_zero hQa0, hPa]
          exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            ENNReal.ofReal_ne_top
      rw [ENNReal.toReal_sum hfin]
      simp only [hterm]
      rw [← Finset.sum_div]
      congr 1
      exact Finset.sum_neg_distrib _
    rw [ENNReal.toReal_ofReal hSnn, hS, hCE] at hToReal
    rw [div_lt_div_iff_of_pos_right hlog2] at hToReal
    exact neg_lt_neg_iff.mp hToReal

/-- P3 corollary. For probability distributions `p` and `q` on the same finite outcome set with
`q ≠ p` and `0 < q i` for every outcome `i`, the expected log score of reporting `q` is strictly
below that of truthful reporting: `∑ i, p i * Real.log (q i) < ∑ i, p i * Real.log (p i)`. -/
theorem logScore_lt_of_fullSupport (X : Type*) [Fintype X]
    (p q : X → ℝ) (hp : IsSimplex p)
    (hq : IsSimplex q) (hne : q ≠ p)
    (hsupp : ∀ i, 0 < q i) :
    ∑ i, p i * Real.log (q i) < ∑ i, p i * Real.log (p i) := by
  rcases logScore_disjunction X p q hp hq hne with ⟨i, _, hqi⟩ | hgap
  · exact absurd hqi (ne_of_gt (hsupp i))
  · exact hgap

/-- P3n: the real log rule, `logRule X q i = Real.log (q i)`, with `Real.log 0 = 0` at zero
mass. -/
noncomputable def logRule (X : Type*) : ScoringRule X :=
  fun q i => Real.log (q i)

/-- P3n: the real whole-simplex log rule is not strictly proper.

Witness on two outcomes: at belief `p = (1 / 2, 1 / 2)`, reporting
`q = (1, 0)` scores strictly above truthful reporting. -/
theorem logRule_notStrictlyProper :
    ¬ IsStrictlyProper (Fin 2) (logRule (Fin 2)) ∧
      expectedScore (Fin 2) (logRule (Fin 2)) (fun _ => 1 / 2)
        (fun _ => 1 / 2) <
      expectedScore (Fin 2) (logRule (Fin 2)) (fun _ => 1 / 2)
        (fun i => if i = 0 then 1 else 0) := by
  have hp : IsSimplex (fun _ : Fin 2 => (1 / 2 : ℝ)) := by
    refine (isSimplex_iff _).mpr ⟨?_, ?_⟩
    · intro _
      norm_num
    · norm_num [Fin.sum_univ_two]
  have hq : IsSimplex (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) := by
    refine (isSimplex_iff _).mpr ⟨?_, ?_⟩
    · rw [Fin.forall_fin_two]
      constructor <;> norm_num
    · norm_num [Fin.sum_univ_two]
  have hq0 : (if True then (1 : ℝ) else 0) = 1 := by simp
  have hq1 : (if (1 : Fin 2) = 0 then (1 : ℝ) else 0) = 0 := by simp
  have hpp : expectedScore (Fin 2) (logRule (Fin 2)) (fun _ => 1 / 2)
      (fun _ => 1 / 2) = Real.log (1 / 2) := by
    simp only [expectedScore, logRule, Fin.sum_univ_two]
    ring
  have hpq : expectedScore (Fin 2) (logRule (Fin 2)) (fun _ => 1 / 2)
      (fun i => if i = 0 then 1 else 0) = 0 := by
    simp only [expectedScore, logRule, Fin.sum_univ_two, hq0, hq1,
      Real.log_one, Real.log_zero]
    ring
  have hneg : Real.log ((1 / 2 : ℝ)) < 0 := by
    rw [Real.log_neg_iff (by norm_num)]
    norm_num
  have hgap : expectedScore (Fin 2) (logRule (Fin 2)) (fun _ => 1 / 2)
      (fun _ => 1 / 2) <
      expectedScore (Fin 2) (logRule (Fin 2)) (fun _ => 1 / 2)
        (fun i => if i = 0 then 1 else 0) := by
    rw [hpp, hpq]
    exact hneg
  constructor
  · intro hStrict
    obtain ⟨hProper, -⟩ := hStrict
    have hle := hProper _ _ hp hq
    linarith [hle, hgap]
  · exact hgap

/-- P4: the linear scoring rule, `linearRule X q i = q i`. -/
noncomputable def linearRule (X : Type*) : ScoringRule X :=
  fun q i => q i

/-- P4: the linear rule is not proper.

Witness on two outcomes: at belief `p = (3 / 4, 1 / 4)`, reporting
`q = (1, 0)` scores strictly above truthful reporting. -/
theorem linearRule_notProper :
    ¬ IsProper (Fin 2) (linearRule (Fin 2)) ∧
      expectedScore (Fin 2) (linearRule (Fin 2))
        (fun i => if i = 0 then 3 / 4 else 1 / 4)
        (fun i => if i = 0 then 3 / 4 else 1 / 4) <
      expectedScore (Fin 2) (linearRule (Fin 2))
        (fun i => if i = 0 then 3 / 4 else 1 / 4)
        (fun i => if i = 0 then 1 else 0) := by
  have hp : IsSimplex
      (fun i : Fin 2 => if i = 0 then (3 / 4 : ℝ) else 1 / 4) := by
    refine (isSimplex_iff _).mpr ⟨?_, ?_⟩
    · rw [Fin.forall_fin_two]
      constructor <;> norm_num
    · norm_num [Fin.sum_univ_two]
  have hq : IsSimplex (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) := by
    refine (isSimplex_iff _).mpr ⟨?_, ?_⟩
    · rw [Fin.forall_fin_two]
      constructor <;> norm_num
    · norm_num [Fin.sum_univ_two]
  have hp0 : (if True then (3 / 4 : ℝ) else 1 / 4) = 3 / 4 := by simp
  have hp1 : (if (1 : Fin 2) = 0 then (3 / 4 : ℝ) else 1 / 4) = 1 / 4 := by
    simp
  have hq0 : (if True then (1 : ℝ) else 0) = 1 := by simp
  have hq1 : (if (1 : Fin 2) = 0 then (1 : ℝ) else 0) = 0 := by simp
  have hpp : expectedScore (Fin 2) (linearRule (Fin 2))
      (fun i => if i = 0 then 3 / 4 else 1 / 4)
      (fun i => if i = 0 then 3 / 4 else 1 / 4) = 5 / 8 := by
    simp only [expectedScore, linearRule, Fin.sum_univ_two, hp0, hp1]
    norm_num
  have hpq : expectedScore (Fin 2) (linearRule (Fin 2))
      (fun i => if i = 0 then 3 / 4 else 1 / 4)
      (fun i => if i = 0 then 1 else 0) = 3 / 4 := by
    simp only [expectedScore, linearRule, Fin.sum_univ_two, hp0, hp1, hq0,
      hq1]
    norm_num
  have hgap : expectedScore (Fin 2) (linearRule (Fin 2))
      (fun i => if i = 0 then 3 / 4 else 1 / 4)
      (fun i => if i = 0 then 3 / 4 else 1 / 4) <
      expectedScore (Fin 2) (linearRule (Fin 2))
        (fun i => if i = 0 then 3 / 4 else 1 / 4)
        (fun i => if i = 0 then 1 else 0) := by
    rw [hpp, hpq]
    norm_num
  constructor
  · intro hProper
    have hle := hProper _ _ hp hq
    linarith [hle, hgap]
  · exact hgap

end MathlibExt.GameTheory.ProperScoring
