/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Chebyshev equioscillation theorem (sufficiency) and de la Vallée Poussin's theorem

Let `f` be a real-valued function on an interval `[a, b]` and let `p` be a real
polynomial of degree at most `n`. If the error `f - p` equioscillates at `n + 2`
points of `[a, b]`: the error satisfies `|f y - p.eval y| ≤ E` throughout
`[a, b]`, and there are `x₀ < x₁ < ⋯ < xₙ₊₁` in `[a, b]` and a sign
`σ = ±1` with `f (xᵢ) - p (xᵢ) = σ * (-1) ^ i * E` for all `i`, then `p` is the
*unique* best uniform approximation to `f` among polynomials of degree at most
`n` on `[a, b]`: no such polynomial has uniform error `< E` on `[a, b]`, and any
with uniform error `≤ E` is `p` itself.

More generally, de la Vallée Poussin's theorem says that if instead the error
`f - p` merely alternates with a one-sided lower bound `η` at `n + 2` points,
`η ≤ σ * (-1) ^ i * (f (xᵢ) - p (xᵢ))`, then every polynomial of degree at most
`n` has uniform error at least `η` on `[a, b]`.

Both theorems follow from one alternation lemma: a nonzero polynomial of degree
at most `n` cannot have its values at `n + 2` strictly increasing points
alternate in sign in the sense `(-1) ^ i * r (xᵢ) ≤ 0` for all `i`. The lemma is
proved by induction on `n`, factoring `r` at `x₀`, at `x₁`, or at a root in
`(x₀, x₁)` supplied by the intermediate value theorem, and applying the induction
hypothesis to `-s` where `r = (X - c) * s`.

The converse direction (a best approximation equioscillates) is not proved here.
See e.g. L. N. Trefethen, *Approximation Theory and Approximation Practice*
(SIAM, 2013), Chapter 7, and R. A. DeVore and G. G. Lorentz, *Constructive
Approximation*, Chapter 2.
-/

@[expose] public section

namespace MathlibExt.Analysis.Approximation.Equioscillation

open Polynomial

/-- A polynomial `p` of degree at most `n` equioscillates against `f` on `[a, b]`
with amplitude `E` and sign `σ = ±1` at the `n + 2` points `x 0 < ⋯ < x (n+1)`,
if `f (x i) - p (x i) = σ * (-1) ^ i * E` for every `i ≤ n + 1`, and
`|f y - p.eval y| ≤ E` for every `y ∈ [a, b]`. -/
def Equioscillates (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) (p : ℝ[X]) (E σ : ℝ) (x : ℕ → ℝ) :
    Prop :=
  (σ = 1 ∨ σ = -1) ∧
  p.natDegree ≤ n ∧
  StrictMonoOn x (Set.Icc 0 (n + 1)) ∧
  (∀ i ∈ Set.Icc 0 (n + 1), x i ∈ Set.Icc a b) ∧
  (∀ i ∈ Set.Icc 0 (n + 1), f (x i) - p.eval (x i) = σ * (-1 : ℝ) ^ i * E) ∧
  (∀ y ∈ Set.Icc a b, |f y - p.eval y| ≤ E)

/-- **Alternation lemma.** If the values of a real polynomial `r` of degree at
most `n` at `n + 2` strictly increasing points alternate in sign, in the sense
that `(-1) ^ i * r (x i) ≤ 0` for every `i`, then `r = 0`. -/
private theorem eq_zero_of_alternating_le : ∀ (n : ℕ) (r : ℝ[X]),
    r.natDegree ≤ n → ∀ x : ℕ → ℝ, StrictMonoOn x (Set.Icc 0 (n + 1)) →
    (∀ i ∈ Set.Icc 0 (n + 1), (-1 : ℝ) ^ i * r.eval (x i) ≤ 0) → r = 0 := by
  intro n
  induction n with
  | zero =>
    intro r hr x _hx hsign
    have h0 : r.natDegree = 0 := Nat.eq_zero_of_le_zero hr
    have hrC : r = C (r.coeff 0) := eq_C_of_natDegree_eq_zero h0
    have hle0 : r.coeff 0 ≤ 0 := by
      have h := hsign 0 (by decide)
      rw [hrC] at h
      simp only [eval_C, pow_zero, one_mul] at h
      exact h
    have hle1 : 0 ≤ r.coeff 0 := by
      have h := hsign 1 (by decide)
      rw [hrC] at h
      simp only [eval_C, pow_one] at h
      linarith
    have hcoeff : r.coeff 0 = 0 := le_antisymm hle0 hle1
    rw [hrC, hcoeff]
    simp
  | succ n ih =>
    intro r hr x hx hsign
    by_cases hr0 : r = 0
    · exact hr0
    have h01 : x 0 < x 1 :=
      hx (Set.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩)
        (Set.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩) zero_lt_one
    have hs0 : r.eval (x 0) ≤ 0 := by
      have h := hsign 0 (Set.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩)
      simpa using h
    have hs1 : 0 ≤ r.eval (x 1) := by
      have h := hsign 1 (Set.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩)
      simpa using h
    by_cases hroot0 : r.eval (x 0) = 0
    · -- Factor at `x 0`; apply the induction hypothesis to `-s` at `x 1, …, x (n+2)`.
      obtain ⟨s, hs⟩ := dvd_iff_isRoot.mpr (show r.IsRoot (x 0) from hroot0)
      have hs_ne : s ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hs
        exact hr0 hs
      have hdeg : s.natDegree ≤ n := by
        have hmul := natDegree_mul (X_sub_C_ne_zero (x 0)) hs_ne
        rw [← hs, natDegree_X_sub_C] at hmul
        omega
      have hdeg' : (-s).natDegree ≤ n := by
        rw [natDegree_neg]
        exact hdeg
      have hmono : StrictMonoOn (fun k => x (k + 1)) (Set.Icc 0 (n + 1)) := by
        intro i hi j hj hij
        apply hx
        · exact Set.mem_Icc.mpr ⟨Nat.zero_le _, by have h2 := hi.2; omega⟩
        · exact Set.mem_Icc.mpr ⟨Nat.zero_le _, by have h2 := hj.2; omega⟩
        · omega
      have hsign' : ∀ i ∈ Set.Icc 0 (n + 1),
          (-1 : ℝ) ^ i * (-s).eval (x (i + 1)) ≤ 0 := by
        intro i hi
        have hpos : 0 < x (i + 1) - x 0 :=
          sub_pos.mpr (hx (Set.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩)
            (Set.mem_Icc.mpr ⟨Nat.zero_le _, by have h2 := hi.2; omega⟩) (by omega))
        have hev : r.eval (x (i + 1)) = (x (i + 1) - x 0) * s.eval (x (i + 1)) := by
          rw [hs]
          simp [eval_mul, eval_sub]
        have hsi := hsign (i + 1)
          (Set.mem_Icc.mpr ⟨Nat.zero_le _, by have h2 := hi.2; omega⟩)
        have h1 : (-1 : ℝ) ^ (i + 1) * s.eval (x (i + 1)) ≤ 0 := by
          have h2 : (x (i + 1) - x 0) * ((-1 : ℝ) ^ (i + 1) * s.eval (x (i + 1))) ≤ 0 := by
            have h3 : (x (i + 1) - x 0) * ((-1 : ℝ) ^ (i + 1) * s.eval (x (i + 1)))
                = (-1 : ℝ) ^ (i + 1) * r.eval (x (i + 1)) := by
              rw [hev]
              ring
            rw [h3]
            exact hsi
          by_contra hX
          have hX' : 0 < (-1 : ℝ) ^ (i + 1) * s.eval (x (i + 1)) := lt_of_not_ge hX
          have hpos' := mul_pos hpos hX'
          linarith [h2]
        have hconv : (-1 : ℝ) ^ i * (-s).eval (x (i + 1))
            = (-1 : ℝ) ^ (i + 1) * s.eval (x (i + 1)) := by
          rw [eval_neg, pow_succ]
          ring
        rw [hconv]
        exact h1
      have happly := ih (-s) hdeg' (fun k => x (k + 1)) hmono hsign'
      have hs_eq : s = 0 := neg_eq_zero.mp happly
      rw [hs, hs_eq, mul_zero]
    · by_cases hroot1 : r.eval (x 1) = 0
      · -- Factor at `x 1`; apply the induction hypothesis to `-s` at
        -- `x 0, x 2, …, x (n+2)`.
        obtain ⟨s, hs⟩ := dvd_iff_isRoot.mpr (show r.IsRoot (x 1) from hroot1)
        have hs_ne : s ≠ 0 := by
          rintro rfl
          rw [mul_zero] at hs
          exact hr0 hs
        have hdeg : s.natDegree ≤ n := by
          have hmul := natDegree_mul (X_sub_C_ne_zero (x 1)) hs_ne
          rw [← hs, natDegree_X_sub_C] at hmul
          omega
        have hdeg' : (-s).natDegree ≤ n := by
          rw [natDegree_neg]
          exact hdeg
        -- The point set `x 0, x 2, …, x (n+2)`: update the shifted sequence at `0`.
        set y : ℕ → ℝ := Function.update (fun k => x (k + 1)) 0 (x 0) with hy
        have hy0 : y 0 = x 0 := Function.update_self _ _ _
        have hyj : ∀ j ≠ 0, y j = x (j + 1) := fun j hj => Function.update_of_ne hj _ _
        have hmono : StrictMonoOn y (Set.Icc 0 (n + 1)) := by
          intro i hi j hj hij
          rcases eq_or_ne i 0 with rfl | hi0
          · rw [hy0, hyj j (by omega)]
            exact hx (Set.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩)
              (Set.mem_Icc.mpr ⟨Nat.zero_le _, by have h2 := hj.2; omega⟩) (by omega)
          · rw [hyj i hi0, hyj j (by omega)]
            exact hx (Set.mem_Icc.mpr ⟨Nat.zero_le _, by have h2 := hi.2; omega⟩)
              (Set.mem_Icc.mpr ⟨Nat.zero_le _, by have h2 := hj.2; omega⟩) (by omega)
        have hsign' : ∀ i ∈ Set.Icc 0 (n + 1),
            (-1 : ℝ) ^ i * (-s).eval (y i) ≤ 0 := by
          intro i hi
          rcases eq_or_ne i 0 with rfl | hi0
          · -- At `i = 0`: `s (x 0) = r (x 0) / (x 0 - x 1) > 0` (negative over negative).
            rw [hy0]
            have hlt : r.eval (x 0) < 0 := lt_of_le_of_ne hs0 hroot0
            have hpos : x 0 - x 1 < 0 := sub_neg.mpr h01
            have hev : r.eval (x 0) = (x 0 - x 1) * s.eval (x 0) := by
              rw [hs]
              simp [eval_mul, eval_sub]
            have hs_pos : 0 < s.eval (x 0) := by
              have hdiv : s.eval (x 0) = r.eval (x 0) / (x 0 - x 1) := by
                rw [hev]
                exact (mul_div_cancel_left₀ _ (ne_of_lt hpos)).symm
              rw [hdiv]
              exact div_pos_of_neg_of_neg hlt hpos
            simp only [pow_zero, one_mul, eval_neg]
            linarith
          · -- At `i ≥ 1`: same computation as factoring at `x 0`, with `x 1` in place
            -- of `x 0`.
            rw [hyj i hi0]
            have hpos : 0 < x (i + 1) - x 1 :=
              sub_pos.mpr (hx (Set.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩)
                (Set.mem_Icc.mpr ⟨Nat.zero_le _, by have h2 := hi.2; omega⟩) (by omega))
            have hev : r.eval (x (i + 1)) = (x (i + 1) - x 1) * s.eval (x (i + 1)) := by
              rw [hs]
              simp [eval_mul, eval_sub]
            have hsi := hsign (i + 1)
              (Set.mem_Icc.mpr ⟨Nat.zero_le _, by have h2 := hi.2; omega⟩)
            have h1 : (-1 : ℝ) ^ (i + 1) * s.eval (x (i + 1)) ≤ 0 := by
              have h2 : (x (i + 1) - x 1) * ((-1 : ℝ) ^ (i + 1) * s.eval (x (i + 1))) ≤ 0 := by
                have h3 : (x (i + 1) - x 1) * ((-1 : ℝ) ^ (i + 1) * s.eval (x (i + 1)))
                    = (-1 : ℝ) ^ (i + 1) * r.eval (x (i + 1)) := by
                  rw [hev]
                  ring
                rw [h3]
                exact hsi
              by_contra hX
              have hX' : 0 < (-1 : ℝ) ^ (i + 1) * s.eval (x (i + 1)) := lt_of_not_ge hX
              have hpos' := mul_pos hpos hX'
              linarith [h2]
            have hconv : (-1 : ℝ) ^ i * (-s).eval (x (i + 1))
                = (-1 : ℝ) ^ (i + 1) * s.eval (x (i + 1)) := by
              rw [eval_neg, pow_succ]
              ring
            rw [hconv]
            exact h1
        have happly := ih (-s) hdeg' y hmono hsign'
        have hs_eq : s = 0 := neg_eq_zero.mp happly
        rw [hs, hs_eq, mul_zero]
      · -- The signs at `x 0` and `x 1` are strictly opposite, so the intermediate
        -- value theorem supplies a root `c ∈ (x 0, x 1)`; factor there.
        have hlt0 : r.eval (x 0) < 0 := lt_of_le_of_ne hs0 hroot0
        have hgt1 : 0 < r.eval (x 1) := lt_of_le_of_ne' hs1 hroot1
        obtain ⟨c, hc_mem, hc_eval⟩ := intermediate_value_Ioo (le_of_lt h01)
          (r.continuous.continuousOn)
          (show (0 : ℝ) ∈ Set.Ioo (r.eval (x 0)) (r.eval (x 1)) from ⟨hlt0, hgt1⟩)
        obtain ⟨s, hs⟩ := dvd_iff_isRoot.mpr (show r.IsRoot c from hc_eval)
        have hs_ne : s ≠ 0 := by
          rintro rfl
          rw [mul_zero] at hs
          exact hr0 hs
        have hdeg : s.natDegree ≤ n := by
          have hmul := natDegree_mul (X_sub_C_ne_zero c) hs_ne
          rw [← hs, natDegree_X_sub_C] at hmul
          omega
        have hdeg' : (-s).natDegree ≤ n := by
          rw [natDegree_neg]
          exact hdeg
        have hmono : StrictMonoOn (fun k => x (k + 1)) (Set.Icc 0 (n + 1)) := by
          intro i hi j hj hij
          apply hx
          · exact Set.mem_Icc.mpr ⟨Nat.zero_le _, by have h2 := hi.2; omega⟩
          · exact Set.mem_Icc.mpr ⟨Nat.zero_le _, by have h2 := hj.2; omega⟩
          · omega
        have hsign' : ∀ i ∈ Set.Icc 0 (n + 1),
            (-1 : ℝ) ^ i * (-s).eval (x (i + 1)) ≤ 0 := by
          intro i hi
          have hpos : 0 < x (i + 1) - c := by
            have hle : x 1 ≤ x (i + 1) :=
              hx.monotoneOn (Set.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩)
                (Set.mem_Icc.mpr ⟨Nat.zero_le _, by have h2 := hi.2; omega⟩) (by omega)
            linarith [hc_mem.2]
          have hev : r.eval (x (i + 1)) = (x (i + 1) - c) * s.eval (x (i + 1)) := by
            rw [hs]
            simp [eval_mul, eval_sub]
          have hsi := hsign (i + 1)
            (Set.mem_Icc.mpr ⟨Nat.zero_le _, by have h2 := hi.2; omega⟩)
          have h1 : (-1 : ℝ) ^ (i + 1) * s.eval (x (i + 1)) ≤ 0 := by
            have h2 : (x (i + 1) - c) * ((-1 : ℝ) ^ (i + 1) * s.eval (x (i + 1))) ≤ 0 := by
              have h3 : (x (i + 1) - c) * ((-1 : ℝ) ^ (i + 1) * s.eval (x (i + 1)))
                  = (-1 : ℝ) ^ (i + 1) * r.eval (x (i + 1)) := by
                rw [hev]
                ring
              rw [h3]
              exact hsi
            by_contra hX
            have hX' : 0 < (-1 : ℝ) ^ (i + 1) * s.eval (x (i + 1)) := lt_of_not_ge hX
            have hpos' := mul_pos hpos hX'
            linarith [h2]
          have hconv : (-1 : ℝ) ^ i * (-s).eval (x (i + 1))
              = (-1 : ℝ) ^ (i + 1) * s.eval (x (i + 1)) := by
            rw [eval_neg, pow_succ]
            ring
          rw [hconv]
          exact h1
        have happly := ih (-s) hdeg' (fun k => x (k + 1)) hmono hsign'
        have hs_eq : s = 0 := neg_eq_zero.mp happly
        rw [hs, hs_eq, mul_zero]

/-- The absolute value of `(-1) ^ i * σ * z` is `|z|` when `σ = ±1`. -/
private theorem abs_neg_one_pow_mul_sigma_mul (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (i : ℕ) (z : ℝ) : |(-1 : ℝ) ^ i * σ * z| = |z| := by
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rcases hσ with rfl | rfl <;> simp

/-- If `p` equioscillates against `f` on `[a, b]`, then `p` is the unique
polynomial of degree at most `n` whose uniform error on `[a, b]` is at most `E`.
In particular `p` is the unique best uniform approximation to `f` among
polynomials of degree at most `n`. -/
theorem eq_of_equioscillates {f : ℝ → ℝ} {a b : ℝ} {n : ℕ} {p : ℝ[X]} {E σ : ℝ}
    {x : ℕ → ℝ} (heq : Equioscillates f a b n p E σ x) {q : ℝ[X]}
    (hq : q.natDegree ≤ n) (herr : ∀ y ∈ Set.Icc a b, |f y - q.eval y| ≤ E) : q = p := by
  obtain ⟨hσ, hp, hx, hxI, halt, _⟩ := heq
  have hdeg : (C σ * (p - q)).natDegree ≤ n := by
    calc (C σ * (p - q)).natDegree
        ≤ (C σ).natDegree + (p - q).natDegree := natDegree_mul_le
      _ ≤ 0 + max n n := add_le_add (natDegree_C σ).le (natDegree_sub_le_of_le hp hq)
      _ = n := by simp
  have hsign : ∀ i ∈ Set.Icc 0 (n + 1),
      (-1 : ℝ) ^ i * (C σ * (p - q)).eval (x i) ≤ 0 := by
    intro i hi
    have halt_i := halt i hi
    have h1 : (-1 : ℝ) ^ i * σ * (f (x i) - q.eval (x i)) ≤ E :=
      le_trans (le_abs_self _)
        (by rw [abs_neg_one_pow_mul_sigma_mul σ hσ i]; exact herr (x i) (hxI i hi))
    have h2 : (-1 : ℝ) ^ i * σ * (f (x i) - p.eval (x i)) = E := by
      rw [halt_i]
      rcases hσ with rfl | rfl
      · have h3 : (-1 : ℝ) ^ i * 1 * (1 * (-1 : ℝ) ^ i * E)
            = ((-1 : ℝ) ^ i * (-1 : ℝ) ^ i) * E := by ring
        rw [h3, ← pow_add]
        have hev : Even (i + i) := ⟨i, rfl⟩
        rw [Even.neg_one_pow hev, one_mul]
      · have h3 : (-1 : ℝ) ^ i * (-1 : ℝ) * ((-1 : ℝ) * (-1 : ℝ) ^ i * E)
            = ((-1 : ℝ) ^ i * (-1 : ℝ) ^ i) * E := by ring
        rw [h3, ← pow_add]
        have hev : Even (i + i) := ⟨i, rfl⟩
        rw [Even.neg_one_pow hev, one_mul]
    have hkey : (-1 : ℝ) ^ i * (C σ * (p - q)).eval (x i)
        = (-1 : ℝ) ^ i * σ * (f (x i) - q.eval (x i)) - E := by
      simp only [eval_mul, eval_C, eval_sub]
      linear_combination -h2
    rw [hkey]
    linarith
  have hr0 := eq_zero_of_alternating_le n _ hdeg x hx hsign
  have hσ0 : (C σ : ℝ[X]) ≠ 0 := by
    rcases hσ with rfl | rfl <;> simp
  have hpq : p - q = 0 := by
    rcases mul_eq_zero.mp hr0 with h | h
    · exact absurd h hσ0
    · exact h
  exact (sub_eq_zero.mp hpq).symm

/-- If `p` equioscillates against `f`, then no polynomial of degree at most `n`
has uniform error strictly less than `E` on `[a, b]`: `p` is a best uniform
approximation. -/
theorem not_lt_of_equioscillates {f : ℝ → ℝ} {a b : ℝ} {n : ℕ} {p : ℝ[X]} {E σ : ℝ}
    {x : ℕ → ℝ} (heq : Equioscillates f a b n p E σ x) {q : ℝ[X]}
    (hq : q.natDegree ≤ n) : ¬ ∀ y ∈ Set.Icc a b, |f y - q.eval y| < E := by
  have hσ := heq.1
  have hxI := heq.2.2.2.1
  have halt := heq.2.2.2.2.1
  intro herr
  have hqp : q = p :=
    eq_of_equioscillates heq hq (fun y hy => (herr y hy).le)
  have h0 := halt 0 (Set.mem_Icc.mpr ⟨Nat.zero_le _, Nat.zero_le _⟩)
  have herr0 := herr (x 0) (hxI 0 (Set.mem_Icc.mpr ⟨Nat.zero_le _, Nat.zero_le _⟩))
  rw [hqp] at herr0
  have habs : |f (x 0) - p.eval (x 0)| = |E| := by
    rw [h0]
    rcases hσ with rfl | rfl <;> simp
  rw [habs] at herr0
  exact absurd herr0 (not_lt_of_ge (le_abs_self E))

/-- **De la Vallée Poussin's theorem.** If the error `f - p` of a polynomial
`p` of degree at most `n` alternates with a one-sided lower bound `η` at
`n + 2` strictly increasing points of `[a, b]`,
`η ≤ σ * (-1) ^ i * (f (x i) - p (x i))`, then every polynomial of degree at
most `n` has uniform error at least `η` on `[a, b]`. -/
theorem de_la_vallee_poussin {f : ℝ → ℝ} {a b : ℝ} {n : ℕ} {p : ℝ[X]} {η σ : ℝ}
    {x : ℕ → ℝ} (hσ : σ = 1 ∨ σ = -1) (hp : p.natDegree ≤ n)
    (hx : StrictMonoOn x (Set.Icc 0 (n + 1)))
    (hxI : ∀ i ∈ Set.Icc 0 (n + 1), x i ∈ Set.Icc a b)
    (halt : ∀ i ∈ Set.Icc 0 (n + 1), η ≤ σ * (-1 : ℝ) ^ i * (f (x i) - p.eval (x i)))
    {q : ℝ[X]} (hq : q.natDegree ≤ n) :
    ¬ ∀ y ∈ Set.Icc a b, |f y - q.eval y| < η := by
  intro herr
  have hdeg : (C σ * (p - q)).natDegree ≤ n := by
    calc (C σ * (p - q)).natDegree
        ≤ (C σ).natDegree + (p - q).natDegree := natDegree_mul_le
      _ ≤ 0 + max n n := add_le_add (natDegree_C σ).le (natDegree_sub_le_of_le hp hq)
      _ = n := by simp
  have hsign : ∀ i ∈ Set.Icc 0 (n + 1),
      (-1 : ℝ) ^ i * (C σ * (p - q)).eval (x i) ≤ 0 := by
    intro i hi
    have halt_i := halt i hi
    have h1 : (-1 : ℝ) ^ i * σ * (f (x i) - q.eval (x i)) < η :=
      lt_of_le_of_lt (le_abs_self _)
        (by rw [abs_neg_one_pow_mul_sigma_mul σ hσ i]
            exact herr (x i) (hxI i hi))
    have hkey : (-1 : ℝ) ^ i * (C σ * (p - q)).eval (x i)
        = (-1 : ℝ) ^ i * σ * (f (x i) - q.eval (x i))
          - σ * (-1 : ℝ) ^ i * (f (x i) - p.eval (x i)) := by
      simp only [eval_mul, eval_C, eval_sub]
      ring
    rw [hkey]
    linarith
  have hr0 := eq_zero_of_alternating_le n _ hdeg x hx hsign
  have hσ0 : (C σ : ℝ[X]) ≠ 0 := by
    rcases hσ with rfl | rfl <;> simp
  have hpq : p - q = 0 := by
    rcases mul_eq_zero.mp hr0 with h | h
    · exact absurd h hσ0
    · exact h
  have hqp : q = p := (sub_eq_zero.mp hpq).symm
  have halt0 := halt 0 (Set.mem_Icc.mpr ⟨Nat.zero_le _, Nat.zero_le _⟩)
  have herr0 := herr (x 0) (hxI 0 (Set.mem_Icc.mpr ⟨Nat.zero_le _, Nat.zero_le _⟩))
  rw [hqp] at herr0
  simp only [pow_zero, mul_one] at halt0
  have hle : σ * (f (x 0) - p.eval (x 0)) ≤ |f (x 0) - p.eval (x 0)| := by
    have habs : |σ * (f (x 0) - p.eval (x 0))| = |f (x 0) - p.eval (x 0)| := by
      rw [abs_mul]
      rcases hσ with rfl | rfl <;> simp
    rw [← habs]
    exact le_abs_self _
  linarith

end MathlibExt.Analysis.Approximation.Equioscillation
