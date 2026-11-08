/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.ContinuedFractions.Computation.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

namespace MetaMathlibExt

@[expose] public section

open MeasureTheory Filter Topology Real

/-- The convergent matrix `C(a) = ∏ᵢ [[0, 1], [1, aᵢ]] = [[p', p], [q', q]]` of a string
`a = (a₁, …, aₙ)`, where `p/q = [0; a₁, …, aₙ]` and `p'/q'` are its last two convergents
(`p' = C 0 0`, `p = C 0 1`, `q' = C 1 0`, `q = C 1 1`).

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Definition 2.1 and equation (2.8). -/
def convergentMatrix (a : List ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  (a.map fun t => !![0, 1; 1, (t : ℤ)]).prod

/-- The empty string has the identity convergent matrix.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Section 2.2. -/
theorem convergentMatrix_nil : convergentMatrix [] = 1 := rfl

/-- Prepending a digit multiplies the convergent matrix on the left by `[[0, 1], [1, t]]`.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
equation (2.8). -/
theorem convergentMatrix_cons (t : ℕ) (a : List ℕ) :
    convergentMatrix (t :: a) = !![0, 1; 1, (t : ℤ)] * convergentMatrix a := by
  simp [convergentMatrix]

/-- The fundamental interval `I(a)`: the numbers `x ∈ [0, 1)` whose continued fraction
digits begin with `a₁, …, aₙ`. Digits are those of Mathlib's `GenContFract.of x`, so a rational
`x` uses the expansion whose last digit exceeds `1` (the resolution in the paper's footnote 2).

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
equation (1.4). -/
def cfCylinder (a : List ℕ) : Set ℝ :=
  {x | x ∈ Set.Ico 0 1 ∧
    ∀ i (hi : i < a.length), (GenContFract.of x).partDens.get? i = some (a[i] : ℝ)}

/-- The empty string gives `I(()) = [0, 1)`.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
equation (1.4). -/
theorem cfCylinder_nil : cfCylinder [] = Set.Ico 0 1 := by
  ext x
  simp [cfCylinder]

/-- The interval `⟨α, β⟩`, equal to `[α, β)` if `α < β` and to `(β, α]` otherwise.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Section 2.3 (interval notation). -/
def fundInterval (α β : ℝ) : Set ℝ :=
  if α < β then Set.Ico α β else Set.Ioc β α

/-- `⟨α, β⟩ = [α, β)` when `α < β`.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Section 2.3. -/
theorem fundInterval_of_lt {α β : ℝ} (h : α < β) : fundInterval α β = Set.Ico α β := by
  simp [fundInterval, h]

/-- The Gauss-Kuzmin measure `P_GK(a) = μ_GK(I(a)) = (1/log 2) ∫_{I(a)} dx/(1 + x)` of a string.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
equations (1.5) and (1.6). -/
noncomputable def gaussKuzminMass (a : List ℕ) : ℝ :=
  (∫ x in cfCylinder a, 1 / (1 + x)) / log 2

/-- `P_GK(a)` unfolded at the empty string: `(1/log 2) ∫_{[0,1)} dx/(1 + x)`.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
equation (1.6). -/
theorem gaussKuzminMass_nil :
    gaussKuzminMass [] = (∫ x in Set.Ico (0 : ℝ) 1, 1 / (1 + x)) / log 2 := by
  rw [gaussKuzminMass, cfCylinder_nil]

/-- The characteristic number `χ(a) = (p + q)(q' + q)` of a string.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Definition 5.1, equation (5.2). -/
def characteristicNumber (a : List ℕ) : ℤ :=
  (convergentMatrix a 0 1 + convergentMatrix a 1 1) *
    (convergentMatrix a 1 0 + convergentMatrix a 1 1)

/-- `χ(()) = 1`.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Definition 5.1. -/
theorem characteristicNumber_nil : characteristicNumber [] = 1 := by
  simp [characteristicNumber, convergentMatrix_nil]

/-- A string is stable if its convergent matrix satisfies `p = 2q'`.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Definition 5.4, equation (5.9). -/
def IsStableString (a : List ℕ) : Prop :=
  convergentMatrix a 0 1 = 2 * convergentMatrix a 1 0

/-- The empty string is stable (`p = q' = 0`).

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Definition 5.4. -/
theorem isStableString_nil : IsStableString [] := by
  simp [IsStableString, convergentMatrix_nil]

/-- A string `a` has a nontrivial symmetry if some rearrangement `σ(a)`, different from `a` and from
its reverse, has the same Gauss-Kuzmin measure.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Definition 1.4. -/
def HasNontrivialSymmetry (a : List ℕ) : Prop :=
  ∃ b : List ℕ, b.Perm a ∧ b ≠ a ∧ b ≠ a.reverse ∧ gaussKuzminMass b = gaussKuzminMass a

/-- The empty string has no nontrivial symmetry.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Definition 1.4. -/
theorem not_hasNontrivialSymmetry_nil : ¬ HasNontrivialSymmetry [] := by
  rintro ⟨b, hb, hne, -⟩
  exact hne (List.perm_nil.mp hb)

/-- Generalized Gauss-Kuzmin theorem: for almost every real `x` and every string `a` of positive
integers, the frequency of the indices `i` with `a_{i+1}(x) = a₁, …, a_{i+n}(x) = aₙ` tends to
`P_GK(a)`.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Proposition 1.2 (`integers-2025-A89-prop-1-2`), quoted from Iosifescu and Kraaikamp,
Proposition 4.1.2. -/
public theorem_wanted gaussKuzmin_string_frequency :
    ∀ᵐ x : ℝ, ∀ a : List ℕ, (∀ x ∈ a, 0 < x) →
      Tendsto (fun N : ℕ =>
          (((Finset.range N).filter (fun i => ∀ j (hj : j < a.length),
              (GenContFract.of x).partDens.get? (i + j) = some (a[j] : ℝ))).card : ℝ) / N)
        atTop (𝓝 (gaussKuzminMass a))

/-- Symmetry property: `μ_GK(I(a)) = μ_GK(I(a⃖))`, i.e. `P_GK(a) = P_GK(a⃖)`, where `a⃖` is the reverse
of `a`.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Proposition 1.3 (`integers-2025-A89-prop-1-3`), equations (1.8) and (1.9). -/
public theorem_wanted gaussKuzminMass_reverse (a : List ℕ) (ha : (∀ x ∈ a, 0 < x)) :
    gaussKuzminMass a.reverse = gaussKuzminMass a

/-- Characterization of the Gauss-Kuzmin measure: if a probability density `f` continuous on
`[0, 1]` satisfies `μ(I(a)) = μ(I(a⃖))` for all strings of positive integers whose length lies in an
infinite set `S`, then `f(x) = 1/(log 2 · (1 + x))` on `[0, 1]`.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Theorem 1 (`integers-2025-A89-thm-1`). -/
public theorem_wanted density_eq_gaussKuzmin_of_reverse_symmetric (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 1)) (hf0 : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f x)
    (hf1 : ∫ x in (0 : ℝ)..1, f x = 1) (S : Set ℕ) (hS : S.Infinite)
    (hsym : ∀ a : List ℕ, (∀ x ∈ a, 0 < x) → a.length ∈ S →
      ∫ x in cfCylinder a, f x = ∫ x in cfCylinder a.reverse, f x) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, f x = 1 / (log 2 * (1 + x))

/-- Optimality: for every `N` there is a probability density `f`, continuous on `[0, 1]`, with
`μ(I(a)) = μ(I(a⃖))` for all strings of positive integers of length at most `N`, whose measure is
not `μ_GK`.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Theorem 2 (`integers-2025-A89-thm-2`). -/
public theorem_wanted exists_reverse_symmetric_density_ne_gaussKuzmin (N : ℕ) (hN : 1 ≤ N) :
    ∃ f : ℝ → ℝ, ContinuousOn f (Set.Icc 0 1) ∧ (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f x) ∧
      ∫ x in (0 : ℝ)..1, f x = 1 ∧
      (∀ a : List ℕ, (∀ x ∈ a, 0 < x) → a.length ≤ N →
        ∫ x in cfCylinder a, f x = ∫ x in cfCylinder a.reverse, f x) ∧
      ∃ x ∈ Set.Icc (0 : ℝ) 1, f x ≠ 1 / (log 2 * (1 + x))

/-- Explicit formulas for convergent matrices: with `C(a) = [[p', p], [q', q]]` and `t ∈ ℕ`,
(i) `C(a⃖) = [[p', q'], [p, q]]`; (ii) `C(a, t) = [[p, p' + tp], [q, q' + tq]]`;
(iii) `C(t, a) = [[q', q], [p' + tq', p + tq]]`; (iv) `C(t, a⃖) = [[p, q], [p' + tp, q' + tq]]`.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 2.2 (`integers-2025-A89-lem-2-2`). -/
public theorem_wanted convergentMatrix_reverse_append_cons (a : List ℕ) (ha : (∀ x ∈ a, 0 < x))
    (t : ℕ) (ht : 1 ≤ t) :
    convergentMatrix a.reverse = !![convergentMatrix a 0 0,
        convergentMatrix a 1 0; convergentMatrix a 0 1, convergentMatrix a 1 1] ∧
      convergentMatrix (a ++ [t]) = !![convergentMatrix a 0 1, convergentMatrix a 0 0 + t *
          convergentMatrix a 0 1; convergentMatrix a 1 1, convergentMatrix a 1 0 + t *
          convergentMatrix a 1 1] ∧
      convergentMatrix (t :: a) = !![convergentMatrix a 1 0,
          convergentMatrix a 1 1; convergentMatrix a 0 0 + t *
          convergentMatrix a 1 0, convergentMatrix a 0 1 + t * convergentMatrix a 1 1] ∧
      convergentMatrix (t :: a.reverse) =
        !![convergentMatrix a 0 1, convergentMatrix a 1 1; convergentMatrix a 0 0 + t *
            convergentMatrix a 0 1, convergentMatrix a 1 0 + t * convergentMatrix a 1 1]

/-- Explicit formulas for fundamental intervals, up to Lebesgue-null sets: with `n = |a|`,
`C(a) = [[p', p], [q', q]]` and `t ∈ ℕ`,
(i) `I(a⃖) = ⟨q'/q, q'/q + (-1)ⁿ/(q(p + q))⟩`;
(ii) `I(a, t) = ⟨(p' + tp)/(q' + tq), (p' + tp)/(q' + tq) + (-1)ⁿ⁺¹/((q' + tq)(q' + (t+1)q))⟩`;
(iii) `I(t, a) = ⟨q/(p + tq), q/(p + tq) + (-1)ⁿ⁺¹/((p + tq)(p' + p + t(q' + q)))⟩`;
(iv) `I(t, a⃖) = ⟨q/(q' + tq), q/(q' + tq) + (-1)ⁿ⁺¹/((q' + tq)(p' + q' + t(p + q)))⟩`.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 2.4 (`integers-2025-A89-lem-2-4`). -/
public theorem_wanted cfCylinder_reverse_append_cons_ae_eq (a : List ℕ) (ha : (∀ x ∈ a, 0 < x))
    (t : ℕ) (ht : 1 ≤ t) :
    cfCylinder a.reverse =ᵐ[volume]
        fundInterval ((convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ))
          ((convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ) + (-1) ^ a.length /
              ((convergentMatrix a 1 1 : ℝ) * ((convergentMatrix a 0 1 : ℝ) +
              (convergentMatrix a 1 1 : ℝ)))) ∧
      cfCylinder (a ++ [t]) =ᵐ[volume]
        fundInterval (((convergentMatrix a 0 0 : ℝ) + t * (convergentMatrix a 0 1 : ℝ)) /
            ((convergentMatrix a 1 0 : ℝ) + t * (convergentMatrix a 1 1 : ℝ)))
          (((convergentMatrix a 0 0 : ℝ) + t * (convergentMatrix a 0 1 : ℝ)) /
              ((convergentMatrix a 1 0 : ℝ) + t * (convergentMatrix a 1 1 : ℝ)) +
            (-1) ^ (a.length + 1) / (((convergentMatrix a 1 0 : ℝ) + t *
                (convergentMatrix a 1 1 : ℝ)) * ((convergentMatrix a 1 0 : ℝ) + (t + 1) *
                (convergentMatrix a 1 1 : ℝ)))) ∧
      cfCylinder (t :: a) =ᵐ[volume]
        fundInterval ((convergentMatrix a 1 1 : ℝ) / ((convergentMatrix a 0 1 : ℝ) + t *
            (convergentMatrix a 1 1 : ℝ)))
          ((convergentMatrix a 1 1 : ℝ) / ((convergentMatrix a 0 1 : ℝ) + t *
              (convergentMatrix a 1 1 : ℝ)) +
            (-1) ^ (a.length + 1) / (((convergentMatrix a 0 1 : ℝ) + t *
                (convergentMatrix a 1 1 : ℝ)) * ((convergentMatrix a 0 0 : ℝ) +
                (convergentMatrix a 0 1 : ℝ) + t * ((convergentMatrix a 1 0 : ℝ) +
                (convergentMatrix a 1 1 : ℝ))))) ∧
      cfCylinder (t :: a.reverse) =ᵐ[volume]
        fundInterval ((convergentMatrix a 1 1 : ℝ) / ((convergentMatrix a 1 0 : ℝ) + t *
            (convergentMatrix a 1 1 : ℝ)))
          ((convergentMatrix a 1 1 : ℝ) / ((convergentMatrix a 1 0 : ℝ) + t *
              (convergentMatrix a 1 1 : ℝ)) +
            (-1) ^ (a.length + 1) / (((convergentMatrix a 1 0 : ℝ) + t *
                (convergentMatrix a 1 1 : ℝ)) * ((convergentMatrix a 0 0 : ℝ) +
                (convergentMatrix a 1 0 : ℝ) + t * ((convergentMatrix a 0 1 : ℝ) +
                (convergentMatrix a 1 1 : ℝ)))))

/-- Explicit formula: `P_GK(a) = P_GK(a⃖) = |log₂(1 + (-1)ⁿ/((p + q)(q' + q)))|` with `n = |a|`.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 2.5 (`integers-2025-A89-lem-2-5`), equation (2.13). -/
public theorem_wanted gaussKuzminMass_eq_abs_logb (a : List ℕ) (ha : (∀ x ∈ a, 0 < x)) :
    gaussKuzminMass a = gaussKuzminMass a.reverse ∧
      gaussKuzminMass a = |logb 2 (1 + (-1) ^ a.length / (((convergentMatrix a 0 1 : ℝ) +
          (convergentMatrix a 1 1 : ℝ)) * ((convergentMatrix a 1 0 : ℝ) +
          (convergentMatrix a 1 1 : ℝ))))|

/-- If a probability density `f`, continuous on `[0, 1]`, satisfies `μ(I(a, t)) = μ(I(t, a⃖))` for
all `t ∈ ℕ`, then `f(r) = f(0)/(1 + r)` for `r = [0; a₁, …, aₙ] = p/q`.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 3.1 (`integers-2025-A89-lem-3-1`). -/
public theorem_wanted density_cfValue_eq_of_append_symmetric (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 1)) (hf0 : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f x)
    (hf1 : ∫ x in (0 : ℝ)..1, f x = 1) (a : List ℕ) (ha : (∀ x ∈ a, 0 < x))
    (hsym : ∀ t : ℕ, 1 ≤ t →
      ∫ x in cfCylinder (a ++ [t]), f x = ∫ x in cfCylinder (t :: a.reverse), f x) :
    f ((convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ)) = f 0 / (1 +
        (convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ))

/-- If a probability measure `μ` agrees with `μ_GK` on `I(a)` for all strings of positive integers of
length exactly `N`, then `μ(I(a)) = μ(I(a⃖))` for all strings of length `n ≤ N`.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 4.1 (`integers-2025-A89-lem-4-1`). -/
public theorem_wanted reverse_symmetric_of_eq_gaussKuzmin_at_length (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (N : ℕ) (hN : 1 ≤ N)
    (hμ : ∀ a : List ℕ, (∀ x ∈ a, 0 < x) → a.length = N →
      μ (cfCylinder a) = ENNReal.ofReal (gaussKuzminMass a)) :
    ∀ a : List ℕ, (∀ x ∈ a, 0 < x) → a.length ≤ N → μ (cfCylinder a) = μ (cfCylinder a.reverse)

/-- For strings of positive integers whose lengths have the same parity, `P_GK(a) = P_GK(b)` if and
only if `χ(a) = χ(b)`.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 5.2 (`integers-2025-A89-lem-5-2`). -/
public theorem_wanted gaussKuzminMass_eq_iff_characteristicNumber_eq (a b : List ℕ)
    (ha : (∀ x ∈ a, 0 < x)) (hb : ∀ x ∈ b, 0 < x) (hpar : a.length % 2 = b.length % 2) :
    gaussKuzminMass a = gaussKuzminMass b ↔ characteristicNumber a = characteristicNumber b

/-- For positive integers `a ≠ b` and `c`, `χ(a, b, c) ≠ χ(b, a, c)`.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 5.3 (`integers-2025-A89-lem-5-3`). -/
public theorem_wanted characteristicNumber_swap_ne (a b c : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hab : a ≠ b) :
    characteristicNumber [a, b, c] ≠ characteristicNumber [b, a, c]

/-- Stable families: (i) `(t, 2t)` and `(t, 1, 2t + 1)` are stable for `t ∈ ℕ`; (ii) if `a` is
stable then so is `(t, a⃖, 2t)`; (iii) for each `n ≥ 2` there are infinitely many stable strings of
length `n`.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 5.5 (`integers-2025-A89-lem-5-5`). -/
public theorem_wanted isStableString_families :
    (∀ t : ℕ, 1 ≤ t → IsStableString [t, 2 * t] ∧ IsStableString [t, 1, 2 * t + 1]) ∧
      (∀ a : List ℕ, (∀ x ∈ a, 0 < x) → IsStableString a → ∀ t : ℕ, 1 ≤ t →
        IsStableString (t :: a.reverse ++ [2 * t])) ∧
      ∀ n : ℕ, 2 ≤ n →
        {a : List ℕ | a.length = n ∧ (∀ x ∈ a, 0 < x) ∧ IsStableString a}.Infinite

/-- If `a = (a₁, …, aₙ)` is a stable string of positive integers, then
`a⁺ = (2, 1, a₁, …, aₙ₋₁, aₙ + 1)` has the nontrivial symmetry
`σ(a⁺) = (2, aₙ + 1, aₙ₋₁, …, a₁, 1)`.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 5.7 (`integers-2025-A89-lem-5-7`), equations (5.12) and (5.13). -/
public theorem_wanted stable_plus_nontrivial_symmetry (a : List ℕ) (ha : (∀ x ∈ a, 0 < x)) (h : a ≠
    [])
    (hst : IsStableString a) :
    let ap := 2 :: 1 :: (a.dropLast ++ [a.getLast h + 1])
    let sg := 2 :: (a.getLast h + 1) :: (a.dropLast.reverse ++ [1])
    sg.Perm ap ∧ sg ≠ ap ∧ sg ≠ ap.reverse ∧ gaussKuzminMass sg = gaussKuzminMass ap

/-- (i) No string of three positive integers has a nontrivial symmetry; (ii) for each `n ≥ 4` there
are infinitely many strings of `n` positive integers with a nontrivial symmetry.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Theorem 3 (`integers-2025-A89-thm-3`). -/
public theorem_wanted nontrivialSymmetry_length_three_and_infinite :
    (∀ a : List ℕ, (∀ x ∈ a, 0 < x) → a.length = 3 → ¬ HasNontrivialSymmetry a) ∧
      ∀ n : ℕ, 4 ≤ n →
        {a : List ℕ | a.length = n ∧ (∀ x ∈ a, 0 < x) ∧ HasNontrivialSymmetry a}.Infinite

end

end MetaMathlibExt
