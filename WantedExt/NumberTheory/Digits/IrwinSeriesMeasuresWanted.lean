/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Digits.Defs

namespace MetaMathlibExt

@[expose] public section

open scoped BigOperators ENNReal
open Filter MeasureTheory Set

/-- `digitCount b d n` is the number of occurrences of `d` in the minimal
base-`b` representation of `n`; `Nat.digits b 0 = []`, so zero has length and
digit count zero. Source: Jean-François Burnol, *Measures for the Summation of
Irwin Series*, INTEGERS 26 (2026), Article A11, Notation and Terminology. -/
public def digitCount (b d n : ℕ) : ℕ :=
  (Nat.digits b n).count d

/-- `integerLength b n` is the length of the minimal base-`b` representation
of `n`. Source: Jean-François Burnol, *Measures for the Summation of Irwin Series*,
INTEGERS 26 (2026), Article A11, Notation and Terminology. -/
public def integerLength (b n : ℕ) : ℕ :=
  (Nat.digits b n).length

/-- The Irwin sum `H^{(k)}_{b,d}`. The prescribed `tsum` encoding is used;
positivity and convergence are mathematical results rather than fields of the
definition. Source: Jean-François Burnol, *Measures for the Summation of Irwin
Series*, INTEGERS 26 (2026), Article A11, Notation and Terminology. -/
public noncomputable def irwinSum (b d k : ℕ) : ℝ :=
  ∑' n : ℕ, if 0 < n ∧ digitCount b d n = k then (1 : ℝ) / n else 0

/-- The integer value `n(X)` of a digit string. Strings are stored most
significant digit first, and the fold therefore gives the final digit weight
`b^0`; this also corrects the displayed exponent typo identified in the task. Source:
Jean-François Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26
(2026), Article A11, Notation and Terminology. -/
public def stringValue (b : ℕ) (X : List (Fin b)) : ℕ :=
  X.foldl (fun n a => b * n + a.val) 0

/-- The point `n(X) / b^{|X|}` associated with a most-significant-digit-first
string. Source: Jean-François Burnol, *Measures for the Summation of Irwin
Series*, INTEGERS 26 (2026), Article A11, definition of `μ_k`. -/
public noncomputable def normalizedStringValue (b : ℕ) (X : List (Fin b)) : ℝ :=
  (stringValue b X : ℝ) / (b : ℝ) ^ X.length

/-- The extended-nonnegative weight `b^{-|X|}` assigned to a string. It is
written through `ENNReal.ofReal`, as required for scalar multiplication of a
measure. Source: Jean-François Burnol, *Measures for the Summation of Irwin
Series*, INTEGERS 26 (2026), Article A11, definition of `μ_k`. -/
public noncomputable def stringWeight (b : ℕ) (X : List (Fin b)) : ℝ≥0∞ :=
  ENNReal.ofReal ((b : ℝ) ^ (-(X.length : ℤ)))

/-- The weighted Dirac summand contributed by one string. This helper exposes
the concrete atoms used by `irwinMeasure`; it is not separately named in the
paper. Source: Jean-François Burnol, *Measures for the Summation of Irwin
Series*, INTEGERS 26 (2026), Article A11, definition of `μ_k`. -/
public noncomputable def stringAtom (b : ℕ) (X : List (Fin b)) : Measure ℝ :=
  stringWeight b X • Measure.dirac (normalizedStringValue b X)

/-- The discrete measure `μ_k`, summed over all most-significant-digit-first
strings containing exactly `k` copies of `d`. The proof `hd` realizes `d` as a
member of `Fin b`. Source: Jean-François Burnol, *Measures for the Summation of
Irwin Series*, INTEGERS 26 (2026), Article A11, definition of `μ_k`. -/
public noncomputable def irwinMeasure (b d k : ℕ) (hd : d < b) : Measure ℝ :=
  Measure.sum (fun X : {X : List (Fin b) // X.count ⟨d, hd⟩ = k} =>
    stringAtom b X.1)

/-- `leadingDigits b l m` is the integer obtained by retaining the first `l`
digits of `m`; statements using it separately impose that `m` has at least `l`
digits. Source: Jean-François
Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26 (2026),
Article A11, notation before Proposition 4. -/
public def leadingDigits (b l m : ℕ) : ℕ :=
  m / b ^ (integerLength b m - l)

/-- The `m`-indexed reciprocal family for denominators having prefix `n` and
exactly `k` occurrences of `d`. Its conditions explicitly include positivity
and sufficient length. Source: Jean-François Burnol, *Measures for the
Summation of Irwin Series*, INTEGERS 26 (2026), Article A11, notation before
Proposition 4. -/
public noncomputable def leadingReciprocalTerm (b d k n m : ℕ) : ℝ :=
  if 0 < m ∧ integerLength b n ≤ integerLength b m ∧
      leadingDigits b (integerLength b n) m = n ∧ digitCount b d m = k then
    (1 : ℝ) / m
  else
    0

/-- The sum of reciprocals with prefix `n` and exactly `k` occurrences of `d`.
The accompanying results assert summability when this `tsum` is used in a
limit. Source: Jean-François Burnol, *Measures for the Summation of Irwin
Series*, INTEGERS 26 (2026), Article A11, Theorem 3. -/
public noncomputable def leadingIrwinSum (b d k n : ℕ) : ℝ :=
  ∑' m : ℕ, leadingReciprocalTerm b d k n m

/-- The ordinary moment `u_{k;m}`, integrated over `[0,1)`. Source:
Jean-François Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26
(2026), Article A11, definition before Corollary 1. -/
public noncomputable def ordinaryMoment (b d k m : ℕ) (hd : d < b) : ℝ :=
  ∫ x in Set.Ico (0 : ℝ) 1, x ^ m ∂irwinMeasure b d k hd

/-- The complementary moment `v_{k;m}`, integrated over `[0,1)`. Source:
Jean-François Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26
(2026), Article A11, definition before Corollary 2. -/
public noncomputable def complementaryMoment (b d k m : ℕ) (hd : d < b) : ℝ :=
  ∫ x in Set.Ico (0 : ℝ) 1, (1 - x) ^ m ∂irwinMeasure b d k hd

/-- `γ_j` is the sum of the `j`-th powers of all base-`b` digits other than
`d`. Source: Jean-François Burnol, *Measures for the Summation of Irwin Series*,
INTEGERS 26 (2026), Article A11, Theorem 1. -/
public def digitPowerSum (b d j : ℕ) : ℝ :=
  ∑ a ∈ Finset.range b, if a = d then 0 else (a : ℝ) ^ j

/-- `γ'_j` excludes the complementary digit `b - 1 - d`. Natural subtraction
is harmless under the digit hypotheses used by every result. Source:
Jean-François Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26
(2026), Article A11, Theorem 2. -/
public def complementaryDigitPowerSum (b d j : ℕ) : ℝ :=
  digitPowerSum b (b - 1 - d) j

/-- The recurrence assumptions for the arbitrary family `u` in Theorem 1. The
first conjunct is `u_{0;0}=b`; the next is the `k=0`, `m≥1` recurrence; and the
last is the `k≥1`, `m≥0` recurrence, with `i` replacing the paper's reused
summation letter `j`. Source: Jean-François Burnol, *Measures for the Summation
of Irwin Series*, INTEGERS 26 (2026), Article A11, Theorem 1. -/
public def OrdinaryMomentRecurrence (b d : ℕ) (u : ℕ → ℕ → ℝ) : Prop :=
  u 0 0 = b ∧
    (∀ m, 1 ≤ m →
      (((b : ℝ) ^ (m + 1) - b + 1) * u 0 m =
        ∑ i ∈ Finset.Icc 1 m,
          (Nat.choose m i : ℝ) * digitPowerSum b d i * u 0 (m - i))) ∧
    (∀ j, 1 ≤ j → ∀ m,
      (((b : ℝ) ^ (m + 1) - b + 1) * u j m =
        (∑ i ∈ Finset.Icc 1 m,
          (Nat.choose m i : ℝ) * digitPowerSum b d i * u j (m - i)) +
        ∑ i ∈ Finset.range (m + 1),
          (Nat.choose m i : ℝ) * (d : ℝ) ^ i * u (j - 1) (m - i)))

/-- The recurrence assumptions for the arbitrary family `v` in Theorem 2.
The `j=0` recurrence includes its `b^{m+1}` term and is valid from `m=0`; the
second recurrence applies for `j≥1` and uses the complementary digit. Source:
Jean-François Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26
(2026), Article A11, Theorem 2. -/
public def ComplementaryMomentRecurrence (b d : ℕ) (v : ℕ → ℕ → ℝ) : Prop :=
  (∀ m,
    (((b : ℝ) ^ (m + 1) - b + 1) * v 0 m =
      (b : ℝ) ^ (m + 1) +
        ∑ i ∈ Finset.Icc 1 m,
          (Nat.choose m i : ℝ) * complementaryDigitPowerSum b d i * v 0 (m - i))) ∧
    (∀ j, 1 ≤ j → ∀ m,
      (((b : ℝ) ^ (m + 1) - b + 1) * v j m =
        (∑ i ∈ Finset.Icc 1 m,
          (Nat.choose m i : ℝ) * complementaryDigitPowerSum b d i * v j (m - i)) +
        ∑ i ∈ Finset.range (m + 1),
          (Nat.choose m i : ℝ) * (b - 1 - d : ℕ) ^ i * v (j - 1) (m - i)))

/-- `HasBaseDepth b x l` says that `l` is the least denominator exponent
representing the `b`-imal number `x`. This expands the paper's “depth” into an
existence clause and exclusion of every smaller exponent. Source: Jean-François
Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26 (2026),
Article A11, Notation and Terminology. -/
public def HasBaseDepth (b : ℕ) (x : ℝ) (l : ℕ) : Prop :=
  (∃ z : ℤ, x = (z : ℝ) / (b : ℝ) ^ l) ∧
    ∀ q < l, ¬ ∃ z : ℤ, x = (z : ℝ) / (b : ℝ) ^ q

/-- The affine image `b^l U - b^l x` appearing in the local mass formulas. Source: Jean-François Burnol,
*Measures for the Summation of Irwin Series*, INTEGERS 26 (2026), Article A11,
Lemma 2. -/
public def affineScaleSet (b l : ℕ) (x : ℝ) (U : Set ℝ) : Set ℝ :=
  (fun y : ℝ => (b : ℝ) ^ l * y - (b : ℝ) ^ l * x) '' U

/-- Zero has no digits in the minimal representation, hence no occurrences of
any chosen digit. Source: Jean-François Burnol, *Measures for the Summation of
Irwin Series*, INTEGERS 26 (2026), Article A11, Notation and Terminology. -/
public theorem digitCount_zero (b d : ℕ) : digitCount b d 0 = 0 := by
  simp [digitCount]

/-- The empty string evaluates to zero, in every base. Source: Jean-François Burnol, *Measures for the Summation of Irwin
Series*, INTEGERS 26 (2026), Article A11, Notation and Terminology. -/
public theorem stringValue_nil (b : ℕ) : stringValue b [] = 0 := by
  rfl

/-- The empty string contributes a unit Dirac mass at the origin. This is the
small concrete characteristic fact proved in place of the substantially deeper
total-mass computation `μ_k([0,1))=b`; it concerns the empty-string summand,
not the full atom after coincident strings are combined. Source: Jean-François
Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26 (2026),
Article A11, definition of `μ_k` and Remark `rem:zero`. -/
public theorem stringAtom_nil (b : ℕ) : stringAtom b [] = Measure.dirac 0 := by
  simp [stringAtom, stringWeight, normalizedStringValue, stringValue]

/-- Theorem 1(a): under exactly the two displayed recurrences (packaged in
`OrdinaryMomentRecurrence`), the family indexed by `m≥1` has sum equal to the
Irwin sum minus the exact short block and `b` times the at-most-`k` length-`l`
block. `HasSum` is used so a divergent `tsum` cannot make the identity vacuous.
Source: Jean-François Burnol, *Measures for the Summation of Irwin Series*,
INTEGERS 26 (2026), Article A11, Theorem 1. -/
public theorem_wanted irwinSum_hasSum_alternating
    (b d : ℕ) (hb : 1 < b) (hd : d < b) (u : ℕ → ℕ → ℝ)
    (hu : OrdinaryMomentRecurrence b d u) (k l : ℕ) (hl : 1 ≤ l) :
    HasSum
      (fun m : ℕ =>
        if 1 ≤ m then
          (-1 : ℝ) ^ m *
            ∑ n ∈ Finset.Ico (b ^ (l - 1)) (b ^ l),
              if digitCount b d n ≤ k then
                u (k - digitCount b d n) m / (n : ℝ) ^ (m + 1)
              else 0
        else 0)
      (irwinSum b d k -
        (∑ n ∈ Finset.Ico 1 (b ^ (l - 1)),
          if digitCount b d n = k then (1 : ℝ) / n else 0) -
        (b : ℝ) *
          ∑ n ∈ Finset.Ico (b ^ (l - 1)) (b ^ l),
            if digitCount b d n ≤ k then (1 : ℝ) / n else 0)

/-- Theorem 1(b–d): every zeroth moment is `b`; for `m≥1`, the recurrence family is nonnegative and has
the stated unique zero case; it decreases in `m`, strictly when nonzero; it
increases strictly in `j`; and its `j`-limit is `b/(m+1)`. The arbitrary-family
form follows the paper. Source: Jean-François Burnol, *Measures for the
Summation of Irwin Series*, INTEGERS 26 (2026), Article A11, Theorem 1. -/
public theorem_wanted ordinaryMomentRecurrence_properties
    (b d : ℕ) (hb : 1 < b) (hd : d < b) (u : ℕ → ℕ → ℝ)
    (hu : OrdinaryMomentRecurrence b d u) :
    (∀ j, u j 0 = b) ∧
    (∀ j m, 1 ≤ m →
      0 ≤ u j m ∧ (u j m = 0 ↔ j = 0 ∧ b = 2 ∧ d = 1)) ∧
    (∀ j m, 1 ≤ m →
      u j (m + 1) ≤ u j m ∧ (u j m ≠ 0 → u j (m + 1) < u j m)) ∧
    (∀ j m, 1 ≤ m → u j m < u (j + 1) m) ∧
    (∀ m, 1 ≤ m →
      Tendsto (fun j : ℕ => u j m) atTop (nhds ((b : ℝ) / (m + 1))))

/-- Theorem 2(a): under the complementary recurrences, the nonnegative
`m≥1` series has sum equal to the Irwin sum minus the exact short block and the
shifted at-most-`k` block. The paper's ambient assumption `b>1` is used instead
of its isolated `b>0` typo. Source: Jean-François Burnol, *Measures for the
Summation of Irwin Series*, INTEGERS 26 (2026), Article A11, Theorem 2. -/
public theorem_wanted irwinSum_hasSum_positive
    (b d : ℕ) (hb : 1 < b) (hd : d < b) (v : ℕ → ℕ → ℝ)
    (hv : ComplementaryMomentRecurrence b d v) (k l : ℕ) (hl : 1 ≤ l) :
    HasSum
      (fun m : ℕ =>
        if 1 ≤ m then
          ∑ n ∈ Finset.Ico (b ^ (l - 1)) (b ^ l),
            if digitCount b d n ≤ k then
              v (k - digitCount b d n) m / ((n : ℝ) + 1) ^ (m + 1)
            else 0
        else 0)
      (irwinSum b d k -
        (∑ n ∈ Finset.Ico 1 (b ^ (l - 1)),
          if digitCount b d n = k then (1 : ℝ) / n else 0) -
        (b : ℝ) *
          ∑ n ∈ Finset.Ico (b ^ (l - 1)) (b ^ l),
            if digitCount b d n ≤ k then (1 : ℝ) / ((n : ℝ) + 1) else 0)

/-- Theorem 2(b–d): every zeroth moment is `b`, complementary moments lie in `(0,b]`; they strictly
decrease in `m` outside `(b,d,j)=(2,1,0)`, where they equal two; they strictly
decrease in `j`; and their `j`-limit is `b/(m+1)`. Source: Jean-François
Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26 (2026),
Article A11, Theorem 2. -/
public theorem_wanted complementaryMomentRecurrence_properties
    (b d : ℕ) (hb : 1 < b) (hd : d < b) (v : ℕ → ℕ → ℝ)
    (hv : ComplementaryMomentRecurrence b d v) :
    (∀ j, v j 0 = b) ∧
    (∀ j m, 1 ≤ m → 0 < v j m ∧ v j m ≤ b) ∧
    (∀ j m, 1 ≤ m →
      ((b = 2 ∧ d = 1 ∧ j = 0) → v j m = 2) ∧
      (¬(b = 2 ∧ d = 1 ∧ j = 0) → v j (m + 1) < v j m)) ∧
    (∀ j m, 1 ≤ m → v (j + 1) m < v j m) ∧
    (∀ m, 1 ≤ m →
      Tendsto (fun j : ℕ => v j m) atTop (nhds ((b : ℝ) / (m + 1))))

/-- Proposition 1: for nonzero `d`, `k ↦ H^{(k)}` is strictly decreasing on
`[1,∞)`; for `d=0` it is strictly decreasing on all naturals; and in both
cases it tends to `b log b`. Source: Jean-François Burnol, *Measures for the
Summation of Irwin Series*, INTEGERS 26 (2026), Article A11, Proposition 1. -/
public theorem_wanted irwinSum_strictAnti_and_tendsto
    (b d : ℕ) (hb : 1 < b) (hd : d < b) :
    (d ≠ 0 → StrictAntiOn (irwinSum b d) (Set.Ici 1)) ∧
    (d = 0 → StrictAnti (irwinSum b d)) ∧
    Tendsto (irwinSum b d) atTop (nhds ((b : ℝ) * Real.log b))

/-- Proposition 2: if `b>2` and `d≠0`, `H^{(0)}` exceeds both
`b log b - b log(1+1/d)` and its consequence `b log(b/2)`. Source:
Jean-François Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26
(2026), Article A11, Proposition 2. -/
public theorem_wanted irwinSum_zero_lowerBounds
    (b d : ℕ) (hb : 2 < b) (hd : d < b) (hd0 : d ≠ 0) :
    (b : ℝ) * Real.log b - (b : ℝ) * Real.log (1 + 1 / (d : ℝ)) <
      irwinSum b d 0 ∧
    (b : ℝ) * Real.log ((b : ℝ) / 2) < irwinSum b d 0

/-- Proposition 4: for positive `n`, the reciprocal family whose denominators
start with `n` and have `k(n)+k` selected digits has sum equal to the integral
of `1/(n+x)` against `μ_k`. `HasSum` makes convergence part of the statement.
Source: Jean-François Burnol, *Measures for the Summation of Irwin Series*,
INTEGERS 26 (2026), Article A11, Proposition 4. -/
public theorem_wanted integral_eq_leadingReciprocal_hasSum
    (b d : ℕ) (hb : 1 < b) (hd : d < b) (n k : ℕ) (hn : 0 < n) :
    HasSum (leadingReciprocalTerm b d (digitCount b d n + k) n)
      (∫ x in Set.Ico (0 : ℝ) 1, ((n : ℝ) + x)⁻¹ ∂irwinMeasure b d k hd)

/-- Corollary 1: when `k(n)≤k`, the prefix-restricted reciprocal series and
the alternating ordinary-moment series have a common sum. The existential
common value plus two `HasSum` assertions avoids any divergent-`tsum`
vacuity; the length is `integerLength b n`. Source: Jean-François Burnol,
*Measures for the Summation of Irwin Series*, INTEGERS 26 (2026), Article A11,
Corollary 1. -/
public theorem_wanted leadingReciprocal_hasSum_ordinaryMoments
    (b d : ℕ) (hb : 1 < b) (hd : d < b) (k n : ℕ)
    (hn : 0 < n) (hnk : digitCount b d n ≤ k) :
    ∃ S : ℝ,
      HasSum (leadingReciprocalTerm b d k n) S ∧
      HasSum
        (fun m : ℕ =>
          (-1 : ℝ) ^ m * ordinaryMoment b d (k - digitCount b d n) m hd /
            (n : ℝ) ^ (m + 1)) S

/-- Corollary 2: the prefix reciprocal family and the complementary-moment
series have a common sum; every term on the right is positive and that family
is summable. Positivity plus summability is the task-permitted formalization of
the paper's phrase “positive series with geometric convergence”; no explicit
ratio is asserted. Source: Jean-François Burnol, *Measures for the Summation of
Irwin Series*, INTEGERS 26 (2026), Article A11, Corollary 2. -/
public theorem_wanted leadingReciprocal_hasSum_complementaryMoments
    (b d : ℕ) (hb : 1 < b) (hd : d < b) (k n : ℕ)
    (hn : 0 < n) (hnk : digitCount b d n ≤ k) :
    ∃ S : ℝ,
      HasSum (leadingReciprocalTerm b d k n) S ∧
      HasSum
        (fun m : ℕ =>
          complementaryMoment b d (k - digitCount b d n) m hd /
            ((n : ℝ) + 1) ^ (m + 1)) S ∧
      (∀ m : ℕ, 0 <
        complementaryMoment b d (k - digitCount b d n) m hd /
          ((n : ℝ) + 1) ^ (m + 1)) ∧
      Summable (fun m : ℕ =>
        complementaryMoment b d (k - digitCount b d n) m hd /
          ((n : ℝ) + 1) ^ (m + 1))

/-- Lemma 1, positive index: integration after `x ↦ bx` splits into the
digits unequal to `d` using `μ_k` and the digit `d` using `μ_{k-1}`. The paper's
boundedness is encoded as bounded image on `[0,b)`, and measurability is added
to give the Lebesgue integrals their standard meaning. Source: Jean-François
Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26 (2026),
Article A11, Lemma 1. -/
public theorem_wanted integral_irwinMeasure_succ
    (b d : ℕ) (hb : 1 < b) (hd : d < b) (f : ℝ → ℝ)
    (hf_measurable : Measurable f)
    (hf_bounded : Bornology.IsBounded (f '' Set.Ico (0 : ℝ) b))
    (k : ℕ) (hk : 1 ≤ k) :
    (∫ x in Set.Ico (0 : ℝ) 1, f (b * x) ∂irwinMeasure b d k hd) =
      (1 / (b : ℝ)) *
        (∑ a ∈ Finset.range b,
          if a = d then 0 else
            ∫ x in Set.Ico (0 : ℝ) 1, f (a + x) ∂irwinMeasure b d k hd) +
      (1 / (b : ℝ)) *
        ∫ x in Set.Ico (0 : ℝ) 1, f (d + x) ∂irwinMeasure b d (k - 1) hd

/-- Lemma 1, zero index: the same digit decomposition has the empty-string
term `f(0)` and no `μ_{-1}` term. Measurability is an added analytic hypothesis,
while boundedness remains restricted to `[0,b)` as in the paper. Source:
Jean-François Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26
(2026), Article A11, Lemma 1. -/
public theorem_wanted integral_irwinMeasure_zero
    (b d : ℕ) (hb : 1 < b) (hd : d < b) (f : ℝ → ℝ)
    (hf_measurable : Measurable f)
    (hf_bounded : Bornology.IsBounded (f '' Set.Ico (0 : ℝ) b)) :
    (∫ x in Set.Ico (0 : ℝ) 1, f (b * x) ∂irwinMeasure b d 0 hd) =
      f 0 + (1 / (b : ℝ)) *
        ∑ a ∈ Finset.range b,
          if a = d then 0 else
            ∫ x in Set.Ico (0 : ℝ) 1, f (a + x) ∂irwinMeasure b d 0 hd

/-- Lemma 2: if `x` has depth `l` and is represented by the length-`l` string
`X`, then an open subinterval at scale `l'` has zero `μ_k` mass below the
adjusted digit count `j'`, and otherwise rescales to `μ_{k-j'}`. Here `j'` is
the displayed conditional, `affineScaleSet` is `b^{l'}U-b^{l'}x`, and masses
are converted from `ENNReal` with `.toReal`. Source: Jean-François Burnol,
*Measures for the Summation of Irwin Series*, INTEGERS 26 (2026), Article A11,
Lemma 2. -/
public theorem_wanted irwinMeasure_open_local_mass
    (b d : ℕ) (hb : 1 < b) (hd : d < b) (x : ℝ) (l : ℕ)
    (hx : x ∈ Set.Ico (0 : ℝ) 1) (hdepth : HasBaseDepth b x l)
    (X : List (Fin b)) (hXlen : X.length = l)
    (hXval : normalizedStringValue b X = x) (j : ℕ)
    (hj : j = X.count ⟨d, hd⟩) (l' : ℕ) (hll' : l ≤ l')
    (U : Set ℝ)
    (hU : U ⊆ Set.Ioo x (x + (b : ℝ) ^ (-(l' : ℤ)))) (k : ℕ) :
    (k < (if 0 < d then j else j + l' - l) →
      irwinMeasure b d k hd U = 0) ∧
    ((if 0 < d then j else j + l' - l) ≤ k →
      (irwinMeasure b d k hd U).toReal =
        (b : ℝ) ^ (-(l' : ℤ)) *
          (irwinMeasure b d (k - (if 0 < d then j else j + l' - l)) hd
            (affineScaleSet b l' x U)).toReal)

/-- Lemma 3: under the same depth, string, adjusted digit-count, and scale
hypotheses as Lemma 2, the rescaling identity also holds for every subset of
the half-open interval. Masses use `.toReal`. Source: Jean-François Burnol,
*Measures for the Summation of Irwin Series*, INTEGERS 26 (2026), Article A11,
Lemma 3. -/
public theorem_wanted irwinMeasure_halfOpen_deeper_local_mass
    (b d : ℕ) (hb : 1 < b) (hd : d < b) (x : ℝ) (l : ℕ)
    (hx : x ∈ Set.Ico (0 : ℝ) 1) (hdepth : HasBaseDepth b x l)
    (X : List (Fin b)) (hXlen : X.length = l)
    (hXval : normalizedStringValue b X = x) (j : ℕ)
    (hj : j = X.count ⟨d, hd⟩) (l' : ℕ) (hll' : l ≤ l')
    (k : ℕ) (hk : (if 0 < d then j else j + l' - l) ≤ k)
    (U : Set ℝ)
    (hU : U ⊆ Set.Ico x (x + (b : ℝ) ^ (-(l' : ℤ)))) :
    (irwinMeasure b d k hd U).toReal =
      (b : ℝ) ^ (-(l' : ℤ)) *
        (irwinMeasure b d (k - (if 0 < d then j else j + l' - l)) hd
          (affineScaleSet b l' x U)).toReal

/-- Proposition 8: at the exact depth scale, the restriction of `μ_k` is zero
for `k<j`; for `k≥j`, every subset of the half-open cylinder rescales by
`b^{-l}` to `μ_{k-j}`. The first clause uses measure restriction and the second
uses real masses via `.toReal`. Source: Jean-François Burnol, *Measures for the
Summation of Irwin Series*, INTEGERS 26 (2026), Article A11, Proposition 8. -/
public theorem_wanted irwinMeasure_halfOpen_local_mass
    (b d : ℕ) (hb : 1 < b) (hd : d < b) (x : ℝ) (l : ℕ)
    (hx : x ∈ Set.Ico (0 : ℝ) 1) (hdepth : HasBaseDepth b x l)
    (X : List (Fin b)) (hXlen : X.length = l)
    (hXval : normalizedStringValue b X = x) (j : ℕ)
    (hj : j = X.count ⟨d, hd⟩) :
    (∀ k, k < j →
      (irwinMeasure b d k hd).restrict
        (Set.Ico x (x + (b : ℝ) ^ (-(l : ℤ)))) = 0) ∧
    (∀ k, j ≤ k → ∀ U : Set ℝ,
      U ⊆ Set.Ico x (x + (b : ℝ) ^ (-(l : ℤ))) →
      (irwinMeasure b d k hd U).toReal =
        (b : ℝ) ^ (-(l : ℤ)) *
          (irwinMeasure b d (k - j) hd
            (affineScaleSet b l x U)).toReal)

/-- Proposition 9: aligned `b`-imal endpoints have exact mass `bu-bt` once
`k≥l'`; for every nonempty order-connected subset of `[0,1)`, real masses tend
to `b(sSup I-sInf I)`. The integrality clauses spell out “`b^{l'}t` and
`b^{l'}u` are integers” (which makes `t`, `u` `b`-imal). Source: Jean-François Burnol, *Measures for the
Summation of Irwin Series*, INTEGERS 26 (2026), Article A11, Proposition 9. -/
public theorem_wanted irwinMeasure_interval_convergence
    (b d : ℕ) (hb : 1 < b) (hd : d < b) :
    (∀ t u : ℝ, t < u → t ∈ Set.Icc (0 : ℝ) 1 → u ∈ Set.Icc (0 : ℝ) 1 →
      ∀ l' : ℕ,
        (∃ z : ℤ, (b : ℝ) ^ l' * t = z) →
        (∃ z : ℤ, (b : ℝ) ^ l' * u = z) →
        ∀ k : ℕ, l' ≤ k →
          (irwinMeasure b d k hd (Set.Ico t u)).toReal = b * u - b * t) ∧
    (∀ I : Set ℝ, I.Nonempty → Set.OrdConnected I → I ⊆ Set.Ico (0 : ℝ) 1 →
      Tendsto (fun k : ℕ => (irwinMeasure b d k hd I).toReal) atTop
        (nhds ((b : ℝ) * (sSup I - sInf I))))

/-- Theorem 3: for every positive prefix `n`, each exact-digit prefix family
is summable and the corresponding sums tend to `b log(1+1/n)`. The explicit
summability conjunct prevents the `tsum`-defined `leadingIrwinSum` from hiding
divergence. Source: Jean-François Burnol, *Measures for the Summation of Irwin
Series*, INTEGERS 26 (2026), Article A11, Theorem 3. -/
public theorem_wanted leadingIrwinSum_tendsto
    (b d : ℕ) (hb : 1 < b) (hd : d < b) (n : ℕ) (hn : 0 < n) :
    (∀ k : ℕ, Summable (leadingReciprocalTerm b d k n)) ∧
    Tendsto (fun k : ℕ => leadingIrwinSum b d k n) atTop
      (nhds ((b : ℝ) * Real.log (1 + 1 / (n : ℝ))))

end

end MetaMathlibExt
