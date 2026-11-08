/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.FieldTheory.Minpoly.Basic
public import MathlibExt.Dynamics.EventuallyPeriodicSequence
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Int.Star
import Mathlib.Data.Seq.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Euler–Lagrange theorem on eventually periodic continued fractions

This file proves the Lagrange direction of the Euler–Lagrange characterization
of eventually periodic continued fractions: a real quadratic irrational has an
eventually periodic continued fraction
(`continuedFractionEventuallyPeriodic_of_isRealQuadraticIrrational`).

The canonical biconditional
(`continuedFractionEventuallyPeriodic_iff_isRealQuadraticIrrational`) and the
Euler direction
(`isRealQuadraticIrrational_of_continuedFractionEventuallyPeriodic`) are proved
in `MathlibExt.NumberTheory.ContinuedFractions.EulerPeriodic`.

## Sources

* Amrik Singh Nimbran and Paul Levrie, "Patterns in Continued Fractions of
  Square Roots," Journal of Integer Sequences 26 (2023),
  <https://cs.uwaterloo.ca/journals/JIS/VOL26/Nimbran/nimbran14.tex>.
* The eventual-periodicity definition is lines 130–134; exact newline-terminated
  raw span SHA-256:
  `6d3b24948521d4d3fa03d6e17261c9442aa6cdf875126db573c9575a66623a7e`.
* The Euler–Lagrange statement is line 136; exact newline-terminated raw span
  SHA-256:
  `5be80578f3e620afa4d20050b29627a4c251e6ff852720806a9a42a0ff884b42`.
* Complete source file SHA-256:
  `08f38fd112c2dedb3802fe71799b670f6d2dbf5f49a89afdc0828156b8f56180`.
* Archive: `lagrange_periodic_cf_release_v2_D119163759`.
-/

namespace MetaMathlibExt

section
/-- Eventual periodicity of the continued fraction of `x`: the expansion does not
terminate, and the tail partial denominators `partDens` (which omits the head
coefficient `a₀`) are eventually periodic. Nontermination rules out a
vacuous `Option.none` tail. Source: Nimbran–Levrie lines 130–134. -/
def ContinuedFractionEventuallyPeriodic (x : ℝ) : Prop :=
  ¬ (GenContFract.of x).Terminates ∧
    IsEventuallyPeriodic (fun n => (GenContFract.of x).partDens.get? n)

/-- Real quadratic irrationality: `x` is integral over `ℚ` with minimal polynomial
of degree two. Degree two over `ℚ` captures real quadratic irrationality.
Source: Nimbran–Levrie line 136 (Euler–Lagrange statement). -/
def IsRealQuadraticIrrational (x : ℝ) : Prop :=
  IsIntegral ℚ x ∧ (minpoly ℚ x).natDegree = 2

/-- Complete quotients of `x`: `cfXi x 0 = x`, `cfXi x (n+1) = (fract (cfXi x n))⁻¹`. -/
private noncomputable def cfXi (x : ℝ) : ℕ → ℝ
  | 0 => x
  | (n + 1) => (Int.fract (cfXi x n))⁻¹

private theorem cfXi_zero (x : ℝ) : cfXi x 0 = x := rfl

private theorem cfXi_succ (x : ℝ) (n : ℕ) : cfXi x (n + 1) = (Int.fract (cfXi x n))⁻¹ := rfl

/-- The fractional part of an irrational is irrational. -/
private theorem irr_fract (y : ℝ) (hy : Irrational y) : Irrational (Int.fract y) := by
  unfold Irrational
  intro hmem
  obtain ⟨q, hq⟩ := hmem
  apply hy
  exact ⟨(⌊y⌋ : ℚ) + q, by
    push_cast
    rw [hq]
    exact Int.floor_add_fract y⟩

/-- Every complete quotient of an irrational is irrational. -/
private theorem irr_cfXi (x : ℝ) (hx : Irrational x) : ∀ n : ℕ, Irrational (cfXi x n)
  | 0 => by rwa [cfXi_zero]
  | (n + 1) => by rw [cfXi_succ]; exact (irr_fract _ (irr_cfXi x hx n)).inv

/-- The fractional part of a complete quotient never vanishes. -/
private theorem fract_cfXi_ne (x : ℝ) (hx : Irrational x) (n : ℕ) :
    Int.fract (cfXi x n) ≠ 0 := by
  intro h0
  apply (irr_cfXi x hx n)
  exact ⟨(⌊cfXi x n⌋ : ℚ), by
    push_cast
    have h1 := Int.floor_add_fract (cfXi x n)
    rw [h0, add_zero] at h1
    exact h1⟩

private theorem fract_cfXi_pos (x : ℝ) (hx : Irrational x) (n : ℕ) :
    0 < Int.fract (cfXi x n) :=
  lt_of_le_of_ne' (Int.fract_nonneg _) (fract_cfXi_ne x hx n)

private theorem fract_cfXi_lt_one (x : ℝ) (_hx : Irrational x) (n : ℕ) :
    Int.fract (cfXi x n) < 1 :=
  Int.fract_lt_one _

/-- Complete quotients from index one on exceed one. -/
private theorem one_lt_cfXi_succ (x : ℝ) (hx : Irrational x) (n : ℕ) :
    1 < cfXi x (n + 1) :=
  (one_lt_inv₀ (fract_cfXi_pos x hx n)).mpr (fract_cfXi_lt_one x hx n)

private theorem floor_cfXi_ge_one (x : ℝ) (hx : Irrational x) (n : ℕ) :
    1 ≤ ⌊cfXi x (n + 1)⌋ := by
  rw [Int.le_floor]
  exact_mod_cast le_of_lt (one_lt_cfXi_succ x hx n)

/-- Splitting a complete quotient into integer and fractional parts. -/
private theorem cfXi_eq_floor_add_inv (x : ℝ) (_hx : Irrational x) (n : ℕ) :
    cfXi x (n + 1) = ↑⌊cfXi x (n + 1)⌋ + (cfXi x (n + 2))⁻¹ := by
  have h2 : cfXi x (n + 2) = (Int.fract (cfXi x (n + 1)))⁻¹ := cfXi_succ x (n + 1)
  have h1 := Int.floor_add_fract (cfXi x (n + 1))
  rw [h2, inv_inv]
  exact h1.symm

private theorem minpoly_coeff_two (x : ℝ) (hint : IsIntegral ℚ x)
    (hdeg : (minpoly ℚ x).natDegree = 2) : (minpoly ℚ x).coeff 2 = 1 := by
  have hmo := minpoly.monic hint
  have h2 := hmo.coeff_natDegree
  rwa [hdeg] at h2

/-- Numerator convergents: `P 0 = 1`, `P 1 = ⌊x⌋`, `P (n+2) = ⌊ξ (n+1)⌋ P (n+1) + P n`. -/
private noncomputable def cfP (x : ℝ) : ℕ → ℤ
  | 0 => 1
  | 1 => ⌊x⌋
  | (n + 2) => ⌊cfXi x (n + 1)⌋ * cfP x (n + 1) + cfP x n

/-- Denominator convergents: `Q 0 = 0`, `Q 1 = 1`, `Q (n+2) = ⌊ξ (n+1)⌋ Q (n+1) + Q n`. -/
private noncomputable def cfQ (x : ℝ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (n + 2) => ⌊cfXi x (n + 1)⌋ * cfQ x (n + 1) + cfQ x n

private theorem cfP_zero (x : ℝ) : cfP x 0 = 1 := rfl

private theorem cfP_one (x : ℝ) : cfP x 1 = ⌊x⌋ := rfl

private theorem cfP_add_two (x : ℝ) (n : ℕ) : cfP x (n + 2)
    = ⌊cfXi x (n + 1)⌋ * cfP x (n + 1) + cfP x n := rfl

private theorem cfQ_zero (x : ℝ) : cfQ x 0 = 0 := rfl

private theorem cfQ_one (x : ℝ) : cfQ x 1 = 1 := rfl

private theorem cfQ_add_two (x : ℝ) (n : ℕ) : cfQ x (n + 2)
    = ⌊cfXi x (n + 1)⌋ * cfQ x (n + 1) + cfQ x n := rfl

/-- The convergent determinant is `±1`. -/
private theorem cfDet (x : ℝ) (n : ℕ) :
    cfP x (n + 1) * cfQ x n - cfP x n * cfQ x (n + 1) = (-1) ^ (n + 1) := by
  induction n with
  | zero =>
    change cfP x 1 * cfQ x 0 - cfP x 0 * cfQ x 1 = (-1) ^ (0 + 1)
    rw [cfP_one, cfP_zero, cfQ_one, cfQ_zero]
    norm_num
  | succ n ih =>
    have e : n + 1 + 1 = n + 2 := by omega
    rw [e, cfP_add_two x n, cfQ_add_two x n]
    linear_combination -ih

/-- Denominators are nonnegative and at least one from index one on. -/
private theorem cfQ_nonneg_pos (x : ℝ) (hx : Irrational x) (n : ℕ) :
    0 ≤ cfQ x n ∧ 1 ≤ cfQ x (n + 1) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [cfQ_zero]
    · change (1 : ℤ) ≤ cfQ x 1
      rw [cfQ_one]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨zero_le_one.trans h2, ?_⟩
    have e : n + 1 + 1 = n + 2 := by omega
    rw [e, cfQ_add_two x n]
    have ha1 := floor_cfXi_ge_one x hx n
    have hmul : (1 : ℤ) ≤ ⌊cfXi x (n + 1)⌋ * cfQ x (n + 1) :=
      one_le_mul_of_one_le_of_one_le ha1 h2
    linarith

/-- The Möbius identity: `x = (P (n+1) ξ (n+1) + P n) / (Q (n+1) ξ (n+1) + Q n)`. -/
private theorem cfMobius (x : ℝ) (hx : Irrational x) (n : ℕ) :
    x = ((cfP x (n + 1) : ℝ) * cfXi x (n + 1) + (cfP x n : ℝ))
      / ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ)) := by
  induction n with
  | zero =>
    change x = ((cfP x 1 : ℝ) * cfXi x 1 + (cfP x 0 : ℝ))
      / ((cfQ x 1 : ℝ) * cfXi x 1 + (cfQ x 0 : ℝ))
    have hfx : Int.fract x ≠ 0 := by
      have h := fract_cfXi_ne x hx 0
      rwa [cfXi_zero] at h
    have hxi : cfXi x 1 = (Int.fract x)⁻¹ := cfXi_succ x 0
    rw [cfP_one, cfP_zero, cfQ_one, cfQ_zero, hxi]
    have h1 := Int.floor_add_fract x
    have hden : ((1 : ℤ) : ℝ) * (Int.fract x)⁻¹ + ((0 : ℤ) : ℝ) ≠ 0 := by
      have hne := inv_ne_zero hfx
      simpa using hne
    have hfinv : (Int.fract x)⁻¹ * Int.fract x = 1 := inv_mul_cancel₀ hfx
    rw [eq_div_iff hden]
    linear_combination hfinv - (Int.fract x)⁻¹ * h1
  | succ n ih =>
    have e : n + 1 + 1 = n + 2 := by omega
    rw [e, cfP_add_two x n, cfQ_add_two x n]
    have hgt : (1 : ℝ) < cfXi x (n + 2) := one_lt_cfXi_succ x hx (n + 1)
    have ht : cfXi x (n + 2) ≠ 0 := by linarith
    have hs := cfXi_eq_floor_add_inv x hx n
    have hts : cfXi x (n + 2) * cfXi x (n + 1)
        = cfXi x (n + 2) * ↑⌊cfXi x (n + 1)⌋ + 1 := by
      conv_lhs => rw [hs]
      rw [mul_add, mul_inv_cancel₀ ht]
    have hnum : ((⌊cfXi x (n + 1)⌋ * cfP x (n + 1) + cfP x n : ℤ) : ℝ)
          * cfXi x (n + 2) + (cfP x (n + 1) : ℝ)
        = cfXi x (n + 2)
          * ((cfP x (n + 1) : ℝ) * cfXi x (n + 1) + (cfP x n : ℝ)) := by
      push_cast
      linear_combination -((cfP x (n + 1) : ℝ)) * hts
    have hden : ((⌊cfXi x (n + 1)⌋ * cfQ x (n + 1) + cfQ x n : ℤ) : ℝ)
          * cfXi x (n + 2) + (cfQ x (n + 1) : ℝ)
        = cfXi x (n + 2)
          * ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ)) := by
      push_cast
      linear_combination -((cfQ x (n + 1) : ℝ)) * hts
    rw [hnum, hden, mul_div_mul_left _ _ ht]
    exact ih

/-- Approximation quality: `|Q (n+1) x - P (n+1)| = 1 / (Q (n+1) ξ (n+1) + Q n)`. -/
private theorem cfApprox (x : ℝ) (hx : Irrational x) (n : ℕ) :
    |(cfQ x (n + 1) : ℝ) * x - (cfP x (n + 1) : ℝ)|
      = 1 / ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ))
    ∧ |(cfQ x (n + 1) : ℝ) * x - (cfP x (n + 1) : ℝ)|
      ≤ 1 / (cfQ x (n + 1) : ℝ) := by
  obtain ⟨hQ0, hQ1⟩ := cfQ_nonneg_pos x hx n
  have hs : (1 : ℝ) < cfXi x (n + 1) := one_lt_cfXi_succ x hx n
  have hQ1R : (1 : ℝ) ≤ (cfQ x (n + 1) : ℝ) := by exact_mod_cast hQ1
  have hQ0R : (0 : ℝ) ≤ (cfQ x n : ℝ) := by exact_mod_cast hQ0
  have hden_pos : (0 : ℝ)
      < (cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ) := by
    have hpos : (0 : ℝ) < (cfQ x (n + 1) : ℝ) * cfXi x (n + 1) :=
      mul_pos (by linarith) (by linarith)
    linarith
  have hden_ne : (cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ) ≠ 0 :=
    ne_of_gt hden_pos
  have hmob := cfMobius x hx n
  have hdet := cfDet x n
  have heq : (cfQ x (n + 1) : ℝ) * x - (cfP x (n + 1) : ℝ)
      = -((cfP x (n + 1) : ℝ) * (cfQ x n : ℝ)
          - (cfP x n : ℝ) * (cfQ x (n + 1) : ℝ))
        / ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ)) := by
    have h2 : ((cfP x (n + 1) : ℝ) * cfXi x (n + 1) + (cfP x n : ℝ))
          / ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ))
          * ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ))
        = (cfP x (n + 1) : ℝ) * cfXi x (n + 1) + (cfP x n : ℝ) :=
      div_mul_cancel₀ _ hden_ne
    rw [← hmob] at h2
    rw [eq_div_iff hden_ne]
    linear_combination (cfQ x (n + 1) : ℝ) * h2
  have habs : |(cfQ x (n + 1) : ℝ) * x - (cfP x (n + 1) : ℝ)|
      = 1 / ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ)) := by
    rw [heq, abs_div, abs_of_pos hden_pos]
    congr 1
    have hdetR : (cfP x (n + 1) : ℝ) * (cfQ x n : ℝ)
          - (cfP x n : ℝ) * (cfQ x (n + 1) : ℝ) = (-1) ^ (n + 1) := by
      exact_mod_cast hdet
    rw [hdetR, abs_neg]
    simp
  refine ⟨habs, ?_⟩
  rw [habs]
  apply one_div_le_one_div_of_le (by linarith : (0 : ℝ) < cfQ x (n + 1))
  have hQs : (cfQ x (n + 1) : ℝ) * 1
      ≤ (cfQ x (n + 1) : ℝ) * cfXi x (n + 1) :=
    mul_le_mul_of_nonneg_left (le_of_lt hs) (by linarith)
  rw [mul_one] at hQs
  linarith

/-- Leading coefficient of the auxiliary quadratic at level `n`. -/
private noncomputable def triA (a b c : ℤ) (x : ℝ) (n : ℕ) : ℤ :=
  a * cfP x (n + 1) ^ 2 + b * cfP x (n + 1) * cfQ x (n + 1) + c * cfQ x (n + 1) ^ 2

/-- Constant coefficient of the auxiliary quadratic at level `n`. -/
private noncomputable def triC (a b c : ℤ) (x : ℝ) (n : ℕ) : ℤ :=
  a * cfP x n ^ 2 + b * cfP x n * cfQ x n + c * cfQ x n ^ 2

/-- Middle coefficient of the auxiliary quadratic at level `n`. -/
private noncomputable def triB (a b c : ℤ) (x : ℝ) (n : ℕ) : ℤ :=
  2 * a * cfP x (n + 1) * cfP x n
    + b * (cfP x (n + 1) * cfQ x n + cfP x n * cfQ x (n + 1))
    + 2 * c * cfQ x (n + 1) * cfQ x n

private theorem triC_succ (a b c : ℤ) (x : ℝ) (n : ℕ) :
    triC a b c x (n + 1) = triA a b c x n := rfl

private theorem triA_cast (a b c : ℤ) (x : ℝ) (n : ℕ) : ((triA a b c x n : ℤ) : ℝ)
    = (a : ℝ) * (cfP x (n + 1) : ℝ) ^ 2 + (b : ℝ) * (cfP x (n + 1) : ℝ)
      * (cfQ x (n + 1) : ℝ) + (c : ℝ) * (cfQ x (n + 1) : ℝ) ^ 2 := by
  simp only [triA]
  push_cast
  ring

private theorem triB_cast (a b c : ℤ) (x : ℝ) (n : ℕ) : ((triB a b c x n : ℤ) : ℝ)
    = 2 * (a : ℝ) * (cfP x (n + 1) : ℝ) * (cfP x n : ℝ)
      + (b : ℝ) * ((cfP x (n + 1) : ℝ) * (cfQ x n : ℝ)
        + (cfP x n : ℝ) * (cfQ x (n + 1) : ℝ))
      + 2 * (c : ℝ) * (cfQ x (n + 1) : ℝ) * (cfQ x n : ℝ) := by
  simp only [triB]
  push_cast
  ring

private theorem triC_cast (a b c : ℤ) (x : ℝ) (n : ℕ) : ((triC a b c x n : ℤ) : ℝ)
    = (a : ℝ) * (cfP x n : ℝ) ^ 2 + (b : ℝ) * (cfP x n : ℝ) * (cfQ x n : ℝ)
      + (c : ℝ) * (cfQ x n : ℝ) ^ 2 := by
  simp only [triC]
  push_cast
  ring

/-- Each complete quotient is a root of its auxiliary integer quadratic. -/
private theorem tri_root (x : ℝ) (hx : Irrational x) (a b c : ℤ) (n : ℕ)
    (hquad : (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0) :
    ((triA a b c x n : ℤ) : ℝ) * (cfXi x (n + 1)) ^ 2
      + ((triB a b c x n : ℤ) : ℝ) * (cfXi x (n + 1))
      + ((triC a b c x n : ℤ) : ℝ) = 0 := by
  obtain ⟨hQ0, hQ1⟩ := cfQ_nonneg_pos x hx n
  have hQ1R : (1 : ℝ) ≤ (cfQ x (n + 1) : ℝ) := by exact_mod_cast hQ1
  have hQ0R : (0 : ℝ) ≤ (cfQ x n : ℝ) := by exact_mod_cast hQ0
  have hs : (1 : ℝ) < cfXi x (n + 1) := one_lt_cfXi_succ x hx n
  have hden_ne : (cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < (cfQ x (n + 1) : ℝ) * cfXi x (n + 1) :=
      mul_pos (by linarith) (by linarith)
    have hlt : (0 : ℝ) < (cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ) := by
      linarith
    exact ne_of_gt hlt
  have hmob := cfMobius x hx n
  have h2 : x * ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ))
      = (cfP x (n + 1) : ℝ) * cfXi x (n + 1) + (cfP x n : ℝ) := by
    have h3 : ((cfP x (n + 1) : ℝ) * cfXi x (n + 1) + (cfP x n : ℝ))
          / ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ))
          * ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ))
        = (cfP x (n + 1) : ℝ) * cfXi x (n + 1) + (cfP x n : ℝ) :=
      div_mul_cancel₀ _ hden_ne
    rw [← hmob] at h3
    exact h3
  have e1 : ((triA a b c x n : ℤ) : ℝ) * (cfXi x (n + 1)) ^ 2
        + ((triB a b c x n : ℤ) : ℝ) * (cfXi x (n + 1))
        + ((triC a b c x n : ℤ) : ℝ)
      = (a : ℝ) * ((cfP x (n + 1) : ℝ) * cfXi x (n + 1) + (cfP x n : ℝ)) ^ 2
        + (b : ℝ) * ((cfP x (n + 1) : ℝ) * cfXi x (n + 1) + (cfP x n : ℝ))
          * ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ))
        + (c : ℝ) * ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ)) ^ 2 := by
    simp only [triA, triB, triC]
    push_cast
    ring
  have e2 : (a : ℝ) * ((cfP x (n + 1) : ℝ) * cfXi x (n + 1) + (cfP x n : ℝ)) ^ 2
        + (b : ℝ) * ((cfP x (n + 1) : ℝ) * cfXi x (n + 1) + (cfP x n : ℝ))
          * ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ))
        + (c : ℝ) * ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ)) ^ 2
      = ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ)) ^ 2
        * ((a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ)) := by
    rw [← h2]
    ring
  rw [e1, e2, hquad, mul_zero]

/-- The leading coefficient never vanishes, since the quadratic has no rational root. -/
private theorem triA_ne (x : ℝ) (hx : Irrational x) (a b c : ℤ) (n : ℕ)
    (noroot : ∀ q : ℚ, (a : ℝ) * (((q : ℚ)) : ℝ) ^ 2 + (b : ℝ) * (((q : ℚ)) : ℝ)
      + (c : ℝ) ≠ 0) :
    triA a b c x n ≠ 0 := by
  intro hA
  obtain ⟨hQ0, hQ1⟩ := cfQ_nonneg_pos x hx n
  have hQ' : (cfQ x (n + 1) : ℚ) ≠ 0 := by
    have hne : cfQ x (n + 1) ≠ 0 := by omega
    exact_mod_cast hne
  have htri : ((triA a b c x n : ℤ) : ℚ) = 0 := by exact_mod_cast hA
  set q : ℚ := (cfP x (n + 1) : ℚ) / (cfQ x (n + 1) : ℚ) with hq
  have hfactor : ((triA a b c x n : ℤ) : ℚ)
      = (cfQ x (n + 1) : ℚ) ^ 2 * ((a : ℚ) * q ^ 2 + (b : ℚ) * q + (c : ℚ)) := by
    rw [hq]
    simp only [triA]
    push_cast
    field_simp
  rw [htri] at hfactor
  have hQ2 : (cfQ x (n + 1) : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hQ'
  have h0 : (a : ℚ) * q ^ 2 + (b : ℚ) * q + (c : ℚ) = 0 :=
    (mul_eq_zero.mp hfactor.symm).resolve_left hQ2
  have h0R : (a : ℝ) * (((q : ℚ)) : ℝ) ^ 2 + (b : ℝ) * (((q : ℚ)) : ℝ)
      + (c : ℝ) = 0 := by
    exact_mod_cast h0
  exact noroot q h0R

/-- Discriminant invariance: `B² - 4AC` equals the base discriminant times `det²`. -/
private theorem triDisc (a b c : ℤ) (x : ℝ) (n : ℕ) :
    (triB a b c x n) ^ 2 - 4 * (triA a b c x n) * (triC a b c x n)
      = (b ^ 2 - 4 * a * c)
        * (cfP x (n + 1) * cfQ x n - cfP x n * cfQ x (n + 1)) ^ 2 := by
  simp only [triA, triB, triC]
  ring

private theorem cfDet_sq (x : ℝ) (n : ℕ) :
    (cfP x (n + 1) * cfQ x n - cfP x n * cfQ x (n + 1)) ^ 2 = 1 := by
  rw [cfDet, ← pow_mul]
  exact Even.neg_one_pow ⟨n + 1, by ring⟩

/-- Auxiliary rewriting of the leading coefficient via the approximation error. -/
private theorem triA_eq_form (x : ℝ) (a b c : ℤ) (n : ℕ)
    (hquad : (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0)
    (F : ℝ) (hF : F = ((cfQ x (n + 1) : ℤ) : ℝ) * x - ((cfP x (n + 1) : ℤ) : ℝ)) :
    ((triA a b c x n : ℤ) : ℝ)
      = (a : ℝ) * F ^ 2 - F * ((cfQ x (n + 1) : ℤ) : ℝ)
        * (2 * (a : ℝ) * x + (b : ℝ)) := by
  have hP : ((cfP x (n + 1) : ℤ) : ℝ)
      = ((cfQ x (n + 1) : ℤ) : ℝ) * x - F := by rw [hF]; ring
  rw [triA_cast]
  linear_combination ((cfQ x (n + 1) : ℤ) : ℝ) ^ 2 * hquad
    + ((a : ℝ) * (((cfP x (n + 1) : ℤ) : ℝ) + ((cfQ x (n + 1) : ℤ) : ℝ) * x - F)
      + (b : ℝ) * ((cfQ x (n + 1) : ℤ) : ℝ)) * hP

/-- Uniform real bound on the leading coefficients. -/
private theorem triA_real_le (x : ℝ) (hx : Irrational x) (a b c : ℤ)
    (hquad : (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0) (n : ℕ) :
    |((triA a b c x n : ℤ) : ℝ)|
      ≤ |(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)| := by
  obtain ⟨hQ0, hQ1⟩ := cfQ_nonneg_pos x hx n
  have hQ1R : (1 : ℝ) ≤ ((cfQ x (n + 1) : ℤ) : ℝ) := by exact_mod_cast hQ1
  have hQnn : (0 : ℝ) ≤ ((cfQ x (n + 1) : ℤ) : ℝ) := by linarith
  set Q' : ℝ := ((cfQ x (n + 1) : ℤ) : ℝ) with hQ'def
  set P' : ℝ := ((cfP x (n + 1) : ℤ) : ℝ) with hP'def
  set F : ℝ := Q' * x - P' with hFdef
  have hFle : |Q' * x - P'| ≤ 1 / Q' := by
    rw [hQ'def, hP'def]
    exact (cfApprox x hx n).2
  have hFleF : |F| ≤ 1 / Q' := by rw [hFdef]; exact hFle
  have hQne : Q' ≠ 0 := ne_of_gt (by linarith)
  have hFQ : |F| * Q' ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hFleF hQnn
    rwa [one_div_mul_cancel hQne] at h
  have hF1 : |F| ≤ 1 := by
    calc |F| = |F| * 1 := (mul_one _).symm
      _ ≤ |F| * Q' := mul_le_mul_of_nonneg_left hQ1R (abs_nonneg _)
      _ ≤ 1 := hFQ
  have hF2 : F ^ 2 ≤ 1 := by
    have h := mul_le_mul hF1 hF1 (abs_nonneg F) zero_le_one
    rw [one_mul, ← pow_two, sq_abs] at h
    exact h
  have hFproof : F = ((cfQ x (n + 1) : ℤ) : ℝ) * x - ((cfP x (n + 1) : ℤ) : ℝ) := by
    rw [hFdef, hQ'def, hP'def]
  have hform := triA_eq_form x a b c n hquad F hFproof
  rw [hform]
  calc |((a : ℝ)) * F ^ 2 - F * Q' * (2 * (a : ℝ) * x + (b : ℝ))|
      ≤ |((a : ℝ)) * F ^ 2| + |F * Q' * (2 * (a : ℝ) * x + (b : ℝ))| := by
        have h := abs_add_le ((a : ℝ) * F ^ 2)
          (-(F * Q' * (2 * (a : ℝ) * x + (b : ℝ))))
        rwa [← sub_eq_add_neg, abs_neg] at h
    _ ≤ |(a : ℝ)| * 1 + 1 * |2 * (a : ℝ) * x + (b : ℝ)| := by
        refine add_le_add ?_ ?_
        · simp only [abs_mul, abs_of_nonneg (sq_nonneg F)]
          exact mul_le_mul_of_nonneg_left hF2 (abs_nonneg _)
        · simp only [abs_mul, abs_of_nonneg hQnn]
          exact mul_le_mul_of_nonneg_right hFQ (abs_nonneg _)
    _ = |(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)| := by rw [mul_one, one_mul]

/-- The leading coefficients take finitely many values. -/
private theorem triA_bound (x : ℝ) (hx : Irrational x) (a b c : ℤ)
    (hquad : (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0) :
    ∃ M : ℕ, ∀ n : ℕ, (triA a b c x n).natAbs ≤ M := by
  refine ⟨⌈|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|⌉₊, fun n => ?_⟩
  have hA := triA_real_le x hx a b c hquad n
  have hM : |(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|
      ≤ ((⌈|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|⌉₊ : ℕ) : ℝ) :=
    Nat.le_ceil _
  have hle : |((triA a b c x n : ℤ) : ℝ)|
      ≤ ((⌈|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|⌉₊ : ℕ) : ℝ) :=
    le_trans hA hM
  have g1 : triA a b c x n
      ≤ ((⌈|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|⌉₊ : ℕ) : ℤ) := by
    exact_mod_cast (abs_le.mp hle).2
  have g2 : -((⌈|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|⌉₊ : ℕ) : ℤ)
      ≤ triA a b c x n := by
    exact_mod_cast (abs_le.mp hle).1
  omega

/-- Uniform real bound on the constant coefficients. -/
private theorem triC_real_le (x : ℝ) (hx : Irrational x) (a b c : ℤ)
    (hquad : (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0) (n : ℕ) :
    |((triC a b c x n : ℤ) : ℝ)|
      ≤ |(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)| := by
  cases n with
  | zero =>
    have hC0 : triC a b c x 0 = a := by simp [triC, cfP_zero, cfQ_zero]
    rw [hC0]
    exact le_add_of_nonneg_right (abs_nonneg _)
  | succ n =>
    rw [triC_succ]
    exact triA_real_le x hx a b c hquad n

/-- The constant coefficients take finitely many values. -/
private theorem triC_bound (x : ℝ) (hx : Irrational x) (a b c : ℤ)
    (hquad : (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0) :
    ∃ M : ℕ, ∀ n : ℕ, (triC a b c x n).natAbs ≤ M := by
  refine ⟨⌈|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|⌉₊, fun n => ?_⟩
  have hC := triC_real_le x hx a b c hquad n
  have hM : |(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|
      ≤ ((⌈|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|⌉₊ : ℕ) : ℝ) :=
    Nat.le_ceil _
  have hle : |((triC a b c x n : ℤ) : ℝ)|
      ≤ ((⌈|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|⌉₊ : ℕ) : ℝ) :=
    le_trans hC hM
  have g1 : triC a b c x n
      ≤ ((⌈|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|⌉₊ : ℕ) : ℤ) := by
    exact_mod_cast (abs_le.mp hle).2
  have g2 : -((⌈|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|⌉₊ : ℕ) : ℤ)
      ≤ triC a b c x n := by
    exact_mod_cast (abs_le.mp hle).1
  omega

/-- Discriminant identity over ℝ: `B² = D + 4AC`. -/
private theorem triB_sq (x : ℝ) (a b c : ℤ) (n : ℕ) :
    ((triB a b c x n : ℤ) : ℝ) ^ 2
      = ((b ^ 2 - 4 * a * c : ℤ) : ℝ)
        + 4 * ((triA a b c x n : ℤ) : ℝ) * ((triC a b c x n : ℤ) : ℝ) := by
  have hdisc : ((triB a b c x n : ℤ) : ℝ) ^ 2
        - 4 * ((triA a b c x n : ℤ) : ℝ) * ((triC a b c x n : ℤ) : ℝ)
      = ((b ^ 2 - 4 * a * c : ℤ) : ℝ)
        * ((((cfP x (n + 1) * cfQ x n - cfP x n * cfQ x (n + 1) : ℤ))) : ℝ) ^ 2 := by
    exact_mod_cast triDisc a b c x n
  have hdet : ((((cfP x (n + 1) * cfQ x n - cfP x n * cfQ x (n + 1) : ℤ))) : ℝ) ^ 2
      = 1 := by
    exact_mod_cast cfDet_sq x n
  linear_combination hdisc + ((b ^ 2 - 4 * a * c : ℤ) : ℝ) * hdet

/-- The middle coefficients take finitely many values. -/
private theorem triB_bound (x : ℝ) (hx : Irrational x) (a b c : ℤ)
    (hquad : (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0) :
    ∃ K : ℕ, ∀ n : ℕ, (triB a b c x n).natAbs ≤ K := by
  have hA : ∀ n, |((triA a b c x n : ℤ) : ℝ)|
      ≤ |(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)| :=
    fun n => triA_real_le x hx a b c hquad n
  have hC : ∀ n, |((triC a b c x n : ℤ) : ℝ)|
      ≤ |(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)| :=
    fun n => triC_real_le x hx a b c hquad n
  have hRnn : (0 : ℝ) ≤ |(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)| :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  refine ⟨⌈|((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
      + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
        * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) + 1⌉₊, fun n => ?_⟩
  have hBn := triB_sq x a b c n
  have hAn := hA n
  have hCn := hC n
  have hAC : ((triA a b c x n : ℤ) : ℝ) * ((triC a b c x n : ℤ) : ℝ)
      ≤ (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
        * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|) :=
    calc ((triA a b c x n : ℤ) : ℝ) * ((triC a b c x n : ℤ) : ℝ)
        ≤ |((triA a b c x n : ℤ) : ℝ) * ((triC a b c x n : ℤ) : ℝ)| :=
          le_abs_self _
      _ = |((triA a b c x n : ℤ) : ℝ)| * |((triC a b c x n : ℤ) : ℝ)| :=
          abs_mul _ _
      _ ≤ (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
          * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|) :=
          mul_le_mul hAn hCn (abs_nonneg _) hRnn
  have hB2 : ((triB a b c x n : ℤ) : ℝ) ^ 2
      ≤ |((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
        + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
          * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) := by
    have hDle : ((b ^ 2 - 4 * a * c : ℤ) : ℝ)
        ≤ |((b ^ 2 - 4 * a * c : ℤ) : ℝ)| := le_abs_self _
    rw [hBn]
    linear_combination hDle + 4 * hAC
  have hBb : |((triB a b c x n : ℤ) : ℝ)|
      ≤ |((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
        + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
          * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) + 1 := by
    by_cases h1 : |((triB a b c x n : ℤ) : ℝ)| ≤ 1
    · calc |((triB a b c x n : ℤ) : ℝ)| ≤ 1 := h1
        _ ≤ |((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
            + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
              * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) + 1 := by
            have h1' : (0 : ℝ) ≤ |((b ^ 2 - 4 * a * c : ℤ) : ℝ)| := abs_nonneg _
            have h2' : (0 : ℝ) ≤ (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
                * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|) :=
              mul_nonneg hRnn hRnn
            linarith
    · push Not at h1
      calc |((triB a b c x n : ℤ) : ℝ)| ≤ ((triB a b c x n : ℤ) : ℝ) ^ 2 := by
            calc |((triB a b c x n : ℤ) : ℝ)|
                = |((triB a b c x n : ℤ) : ℝ)| * 1 := (mul_one _).symm
              _ ≤ |((triB a b c x n : ℤ) : ℝ)|
                  * |((triB a b c x n : ℤ) : ℝ)| :=
                  mul_le_mul_of_nonneg_left h1.le (abs_nonneg _)
              _ = ((triB a b c x n : ℤ) : ℝ) ^ 2 := by rw [← pow_two, sq_abs]
        _ ≤ |((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
            + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
              * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) := hB2
        _ ≤ |((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
            + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
              * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) + 1 :=
            le_add_of_nonneg_right zero_le_one
  have hK : |((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
        + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
          * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) + 1
      ≤ ((⌈|((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
        + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
          * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) + 1⌉₊ : ℕ) : ℝ) :=
    Nat.le_ceil _
  have hle : |((triB a b c x n : ℤ) : ℝ)|
      ≤ ((⌈|((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
        + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
          * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) + 1⌉₊ : ℕ) : ℝ) :=
    le_trans hBb hK
  have g1 : triB a b c x n
      ≤ ((⌈|((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
        + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
          * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) + 1⌉₊ : ℕ) : ℤ) := by
    exact_mod_cast (abs_le.mp hle).2
  have g2 : -((⌈|((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
        + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
          * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) + 1⌉₊ : ℕ) : ℤ)
      ≤ triB a b c x n := by
    exact_mod_cast (abs_le.mp hle).1
  omega

/-- Each complete quotient determines the next via the floor. -/
private theorem cfXi_step (x : ℝ) (k : ℕ) :
    cfXi x (k + 2) = 1 / (cfXi x (k + 1) - ⌊cfXi x (k + 1)⌋) := by
  have hfr : cfXi x (k + 1) - ⌊cfXi x (k + 1)⌋
      = Int.fract (cfXi x (k + 1)) := by
    have h := Int.floor_add_fract (cfXi x (k + 1))
    linarith
  rw [hfr, cfXi_succ]
  exact (one_div _).symm

/-- Shifting the partial-denominator stream past one coefficient. -/
private theorem partDens_shift (v : ℝ) (k : ℕ) :
    (GenContFract.of v).partDens.get? (k + 1)
      = (GenContFract.of (Int.fract v)⁻¹).partDens.get? k := by
  change (Stream'.Seq.map GenContFract.Pair.b (GenContFract.of v).s).get? (k + 1)
    = (Stream'.Seq.map GenContFract.Pair.b
        (GenContFract.of (Int.fract v)⁻¹).s).get? k
  rw [Stream'.Seq.map_get?, Stream'.Seq.map_get?, GenContFract.of_s_succ]

/-- Complete quotients commute with shifting past one step. -/
private theorem cfXi_shift (v : ℝ) (k : ℕ) :
    cfXi ((Int.fract v)⁻¹) k = cfXi v (k + 1) := by
  induction k with
  | zero => rw [cfXi_zero, cfXi_succ, cfXi_zero]
  | succ k ih => rw [cfXi_succ, cfXi_succ, ih]

/-- The `n`-th partial denominator is the head coefficient of `ξₙ`. -/
private theorem partDens_eq_head (x : ℝ) (n : ℕ) :
    (GenContFract.of x).partDens.get? n
      = (GenContFract.of (cfXi x n)).partDens.get? 0 := by
  revert x
  induction n with
  | zero => intro x; rw [cfXi_zero]
  | succ n ih =>
    intro v
    have e : cfXi ((Int.fract v)⁻¹) n = (Int.fract (cfXi v n))⁻¹ := by
      rw [cfXi_shift, cfXi_succ]
    rw [partDens_shift v n, cfXi_succ, ← e]
    exact ih ((Int.fract v)⁻¹)

/-- The degree-two minimal polynomial has the expected expanded form. -/
private theorem minpoly_eq_form (x : ℝ) (hint : IsIntegral ℚ x)
    (hdeg : (minpoly ℚ x).natDegree = 2) :
    minpoly ℚ x = Polynomial.X ^ 2 + Polynomial.C ((minpoly ℚ x).coeff 1) * Polynomial.X
      + Polynomial.C ((minpoly ℚ x).coeff 0) := by
  conv_lhs => rw [Polynomial.as_sum_range (minpoly ℚ x), hdeg]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    ← Polynomial.C_mul_X_pow_eq_monomial]
  rw [minpoly_coeff_two x hint hdeg, Polynomial.C_1, one_mul]
  ring

private theorem eval_minpoly_at_rat (x : ℝ) (hint : IsIntegral ℚ x)
    (hdeg : (minpoly ℚ x).natDegree = 2) (q : ℚ) :
    (minpoly ℚ x).eval q =
      q ^ 2 + (minpoly ℚ x).coeff 1 * q + (minpoly ℚ x).coeff 0 := by
  conv_lhs => rw [minpoly_eq_form x hint hdeg]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]

private theorem aeval_minpoly_at_real (x : ℝ) (hint : IsIntegral ℚ x)
    (hdeg : (minpoly ℚ x).natDegree = 2) :
    x ^ 2 + ((minpoly ℚ x).coeff 1 : ℝ) * x + ((minpoly ℚ x).coeff 0 : ℝ) = 0 := by
  have h0 := minpoly.aeval ℚ x
  rw [minpoly_eq_form x hint hdeg] at h0
  simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at h0
  exact h0

/-- Clearing denominators in the monic quadratic gives an integer relation
with no rational root. -/
private theorem quad_int_of_minpoly (x : ℝ) (hint : IsIntegral ℚ x)
    (hdeg : (minpoly ℚ x).natDegree = 2) :
    ∃ a b c : ℤ, a ≠ 0 ∧ (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0
      ∧ ∀ q : ℚ, (a : ℝ) * (((q : ℚ)) : ℝ) ^ 2 + (b : ℝ) * (((q : ℚ)) : ℝ)
        + (c : ℝ) ≠ 0 := by
  set B := (minpoly ℚ x).coeff 1 with hB
  set C := (minpoly ℚ x).coeff 0 with hC
  have hBC : x ^ 2 + (B : ℝ) * x + (C : ℝ) = 0 := aeval_minpoly_at_real x hint hdeg
  have hnoroot : ∀ q : ℚ, q ^ 2 + B * q + C ≠ 0 := by
    intro q hq
    have hroot : (minpoly ℚ x).IsRoot q := by
      change (minpoly ℚ x).eval q = 0
      rw [eval_minpoly_at_rat x hint hdeg]
      exact hq
    have hirr := minpoly.irreducible hint
    have hdeg1 := Polynomial.degree_eq_one_of_irreducible_of_root hirr hroot
    have hnat : (minpoly ℚ x).natDegree = 1 :=
      Polynomial.natDegree_eq_of_degree_eq_some hdeg1
    omega
  set a : ℤ := (B.den : ℤ) * C.den with ha_def
  set b : ℤ := B.num * C.den with hb_def
  set c : ℤ := C.num * B.den with hc_def
  have hdenB : B.den ≠ 0 := Rat.den_nz B
  have hdenC : C.den ≠ 0 := Rat.den_nz C
  have hposB : (0 : ℤ) < B.den := by exact_mod_cast Nat.pos_of_ne_zero hdenB
  have hposC : (0 : ℤ) < C.den := by exact_mod_cast Nat.pos_of_ne_zero hdenC
  have ha : a ≠ 0 := ne_of_gt (mul_pos hposB hposC)
  have hBB : B * (B.den : ℚ) = (B.num : ℚ) := Rat.mul_den_eq_num B
  have hCC : C * (C.den : ℚ) = (C.num : ℚ) := Rat.mul_den_eq_num C
  have hDB : (a : ℚ) * B = (b : ℚ) := by
    rw [ha_def, hb_def]
    push_cast
    linear_combination (C.den : ℚ) * hBB
  have hDC : (a : ℚ) * C = (c : ℚ) := by
    rw [ha_def, hc_def]
    push_cast
    linear_combination (B.den : ℚ) * hCC
  have hDBR : (a : ℝ) * (B : ℝ) = (b : ℝ) := by exact_mod_cast hDB
  have hDCR : (a : ℝ) * (C : ℝ) = (c : ℝ) := by exact_mod_cast hDC
  have heq : (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0 := by
    have hcast : (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ)
        = (a : ℝ) * (x ^ 2 + (B : ℝ) * x + (C : ℝ)) := by
      rw [← hDBR, ← hDCR]; ring
    rw [hcast, hBC, mul_zero]
  refine ⟨a, b, c, ha, heq, ?_⟩
  intro q hq
  apply hnoroot q
  have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have h0 : (a : ℚ) * q ^ 2 + (b : ℚ) * q + (c : ℚ) = 0 := by exact_mod_cast hq
  have hQ : (a : ℚ) * (q ^ 2 + B * q + C)
      = (a : ℚ) * q ^ 2 + (b : ℚ) * q + (c : ℚ) := by
    rw [mul_add, mul_add, ← mul_assoc, hDB, hDC]
  have hX : (a : ℚ) * (q ^ 2 + B * q + C) = 0 := by rw [hQ]; exact h0
  exact (mul_eq_zero.mp hX).resolve_left haQ

/-- The auxiliary quadratic polynomial for a coefficient triple. -/
private noncomputable def triPoly (A B C : ℝ) : Polynomial ℝ :=
  Polynomial.C C + Polynomial.C B * Polynomial.X + Polynomial.C A * Polynomial.X ^ 2

private theorem triPoly_coeff_two (A B C : ℝ) : (triPoly A B C).coeff 2 = A := by
  simp [triPoly]

private theorem triPoly_eval (A B C : ℝ) (y : ℝ) :
    (triPoly A B C).eval y = A * y ^ 2 + B * y + C := by
  simp only [triPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]
  ring

/-- The finite box containing all auxiliary coefficient triples. -/
private def triBox (M K : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  Finset.Icc (-((M : ℤ))) ((M : ℤ)) ×ˢ Finset.Icc (-((K : ℤ))) ((K : ℤ))
    ×ˢ Finset.Icc (-((M : ℤ))) ((M : ℤ))

/-- The finite set of all roots of auxiliary polynomials over the box. -/
private noncomputable def triU (M K : ℕ) : Set ℝ :=
  ⋃ t ∈ ↑((triBox M K).filter (fun t : ℤ × ℤ × ℤ => t.1 ≠ 0)),
    {y | (triPoly ((t.1 : ℤ) : ℝ) ((t.2.1 : ℤ) : ℝ) ((t.2.2 : ℤ) : ℝ)).IsRoot y}

/-- Every triple of auxiliary coefficients lies in the box. -/
private theorem triple_mem_box (a b c : ℤ) (x : ℝ) (M K : ℕ)
    (hA : ∀ n, (triA a b c x n).natAbs ≤ M)
    (hB : ∀ n, (triB a b c x n).natAbs ≤ K)
    (hC : ∀ n, (triC a b c x n).natAbs ≤ M)
    (n : ℕ) :
    (triA a b c x n, (triB a b c x n, triC a b c x n)) ∈ triBox M K := by
  have gA := hA n
  have gB := hB n
  have gC := hC n
  simp only [triBox, Finset.mem_product, Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩ <;> omega

/-- The root set over the box is finite. -/
private theorem triU_finite (M K : ℕ) : (triU M K).Finite := by
  simp only [triU]
  refine Set.Finite.biUnion (Finset.finite_toSet _) (fun t ht => ?_)
  have hne : t.1 ≠ 0 :=
    (Finset.mem_filter.mp (Finset.mem_coe.mp ht)).2
  have hA : ((t.1 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hne
  apply Polynomial.finite_setOfPred_isRoot
  intro hz
  have h0 : (triPoly ((t.1 : ℤ) : ℝ) ((t.2.1 : ℤ) : ℝ) ((t.2.2 : ℤ) : ℝ)).coeff 2
      = 0 := by simp [hz]
  rw [triPoly_coeff_two] at h0
  exact hA h0

/-- Every complete quotient past the head lies in the finite root set. -/
private theorem cfXi_mem_triU (x : ℝ) (hx : Irrational x) (a b c : ℤ)
    (hquad : (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0)
    (noroot : ∀ q : ℚ, (a : ℝ) * (((q : ℚ)) : ℝ) ^ 2 + (b : ℝ) * (((q : ℚ)) : ℝ)
      + (c : ℝ) ≠ 0)
    (M K : ℕ)
    (hA : ∀ n, (triA a b c x n).natAbs ≤ M)
    (hB : ∀ n, (triB a b c x n).natAbs ≤ K)
    (hC : ∀ n, (triC a b c x n).natAbs ≤ M)
    (n : ℕ) :
    cfXi x (n + 1) ∈ triU M K := by
  have hbox := triple_mem_box a b c x M K hA hB hC n
  have hAne := triA_ne x hx a b c n noroot
  have h1 : (triA a b c x n, (triB a b c x n, triC a b c x n))
      ∈ (triBox M K).filter (fun t : ℤ × ℤ × ℤ => t.1 ≠ 0) :=
    Finset.mem_filter.mpr ⟨hbox, hAne⟩
  have h2 : (triPoly ((triA a b c x n : ℤ) : ℝ) ((triB a b c x n : ℤ) : ℝ)
      ((triC a b c x n : ℤ) : ℝ)).IsRoot (cfXi x (n + 1)) := by
    change (triPoly ((triA a b c x n : ℤ) : ℝ) ((triB a b c x n : ℤ) : ℝ)
      ((triC a b c x n : ℤ) : ℝ)).eval (cfXi x (n + 1)) = 0
    rw [triPoly_eval]
    exact tri_root x hx a b c n hquad
  exact Set.mem_biUnion (Finset.mem_coe.mpr h1) h2

/-- Shift map on tail complete-quotient values. -/
private noncomputable def xiShift (x : ℝ) (y : ↥(Set.range (fun n => cfXi x (n + 1)))) :
    ↥(Set.range (fun n => cfXi x (n + 1))) :=
  ⟨1 / (y.1 - ⌊y.1⌋), by
    obtain ⟨k, hk⟩ := y.2
    refine ⟨k + 1, ?_⟩
    change cfXi x (k + 1 + 1) = 1 / (y.1 - ⌊y.1⌋)
    have e : k + 1 + 1 = k + 2 := by omega
    rw [e, ← hk]
    exact cfXi_step x k⟩

/-- The shift map sends each tail quotient to the next. -/
private theorem xiShift_orbit (x : ℝ) (n : ℕ) :
    (⟨cfXi x (n + 1 + 1), n + 1, rfl⟩ : ↥(Set.range (fun n => cfXi x (n + 1))))
      = xiShift x ⟨cfXi x (n + 1), n, rfl⟩ := by
  apply Subtype.ext
  change cfXi x (n + 1 + 1) = 1 / (cfXi x (n + 1) - ⌊cfXi x (n + 1)⌋)
  have e : n + 1 + 1 = n + 2 := by omega
  rw [e]
  exact cfXi_step x n

/-- The tail complete quotients form an eventually periodic sequence. -/
private theorem cfXi_eventually_periodic (x : ℝ) (hx : Irrational x) (a b c : ℤ)
    (hquad : (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0)
    (noroot : ∀ q : ℚ, (a : ℝ) * (((q : ℚ)) : ℝ) ^ 2 + (b : ℝ) * (((q : ℚ)) : ℝ)
      + (c : ℝ) ≠ 0)
    (M K : ℕ)
    (hA : ∀ n, (triA a b c x n).natAbs ≤ M)
    (hB : ∀ n, (triB a b c x n).natAbs ≤ K)
    (hC : ∀ n, (triC a b c x n).natAbs ≤ M) :
    IsEventuallyPeriodic (fun n => cfXi x (n + 1)) := by
  have hfin : (Set.range (fun n => cfXi x (n + 1))).Finite := by
    refine Set.Finite.subset (triU_finite M K) (fun y hy => ?_)
    obtain ⟨n, rfl⟩ := hy
    exact cfXi_mem_triU x hx a b c hquad noroot M K hA hB hC n
  have : Fintype ↥(Set.range (fun n => cfXi x (n + 1))) := hfin.fintype
  obtain ⟨p, n₀, hp, hper⟩ := IsEventuallyPeriodic.of_finite_orbit (xiShift x)
    (fun n : ℕ => ⟨cfXi x (n + 1), n, rfl⟩) (fun n => xiShift_orbit x n)
  refine IsEventuallyPeriodic.of_witness (n₀ := n₀) hp (fun n hn => ?_)
  exact congrArg Subtype.val (hper n hn)

/-- A real quadratic irrational (in the `IsIntegral` + degree-two sense) is irrational. -/
private theorem quad_irrational (x : ℝ) (hint : IsIntegral ℚ x)
    (hdeg : (minpoly ℚ x).natDegree = 2) : Irrational x := by
  obtain ⟨a, b, c, ha, heq, hnoroot⟩ := quad_int_of_minpoly x hint hdeg
  intro hmem
  obtain ⟨q, hq⟩ := hmem
  apply hnoroot q
  rw [← hq] at heq
  exact heq

/-- Lagrange direction of the Euler–Lagrange theorem: a real quadratic irrational
has an eventually periodic continued fraction. The canonical biconditional
(`continuedFractionEventuallyPeriodic_iff_isRealQuadraticIrrational`) and the
Euler direction are proved in
`MathlibExt.NumberTheory.ContinuedFractions.EulerPeriodic`.
-/
theorem continuedFractionEventuallyPeriodic_of_isRealQuadraticIrrational
    (x : ℝ) (h : IsRealQuadraticIrrational x) :
    ContinuedFractionEventuallyPeriodic x := by
  obtain ⟨hint, hdeg⟩ := h
  obtain ⟨a, b, c, ha, heq, hnoroot⟩ := quad_int_of_minpoly x hint hdeg
  have hirr : Irrational x := quad_irrational x hint hdeg
  have hnonterm : ¬ (GenContFract.of x).Terminates := by
    rw [GenContFract.terminates_iff_rat]
    intro hmem
    obtain ⟨q, hq⟩ := hmem
    apply hnoroot q
    rw [← hq]
    exact heq
  obtain ⟨M1, hM1⟩ := triA_bound x hirr a b c heq
  obtain ⟨K, hK⟩ := triB_bound x hirr a b c heq
  obtain ⟨M2, hM2⟩ := triC_bound x hirr a b c heq
  have hA : ∀ n, (triA a b c x n).natAbs ≤ max M1 M2 :=
    fun n => le_trans (hM1 n) (le_max_left _ _)
  have hC : ∀ n, (triC a b c x n).natAbs ≤ max M1 M2 :=
    fun n => le_trans (hM2 n) (le_max_right _ _)
  obtain ⟨p, n₀, hp, hper⟩ := cfXi_eventually_periodic x hirr a b c heq hnoroot
    (max M1 M2) K hA hK hC
  have hxi : ∀ n, n₀ ≤ n → cfXi x (n + p + 1) = cfXi x (n + 1) :=
    fun n hn => hper n hn
  refine ⟨hnonterm, IsEventuallyPeriodic.of_witness (n₀ := n₀ + 1) hp
    (fun m hm => ?_)⟩
  rw [partDens_eq_head x (m + p), partDens_eq_head x m]
  have hxi' : cfXi x (m + p) = cfXi x m := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    have e : n + 1 + p = n + p + 1 := by omega
    rw [e]
    exact hxi n (by omega)
  rw [hxi']

end
end MetaMathlibExt
