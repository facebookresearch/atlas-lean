/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

arnovich/asgard-lean, commit
e5e098d5bce80c3907a6acd4e2beb904309a1709,
`Gimle/Asgard/Streams/Majorant.lean` and `Gimle/Asgard/Streams/Tail.lean`. Authors: arnovich.

MIT License

Copyright (c) 2025 Gimle Labs

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finsupp.WellFounded
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Geometric majorants of rational multivariate power series

Coefficient bounds with positive radii are stable under shrinking radii and
constant scaling. Products admit halved radii. Inversion admits an explicit
smaller polydisc under a geometric smallness condition on the nonconstant part.
The inverse theorem also respects Mathlib's total inverse: zero constant term
makes the formal inverse zero. No analytic convergence is assumed here.

Mathematical references: B. Sambale, An invitation to formal power series,
https://arxiv.org/abs/2205.00879v7, Definition 2.1(iv), Lemma 2.5(i), and Section 8
(Cauchy products and reciprocal coefficient recursion); J. Lebl, Tasty Bits of
Several Complex Variables, version 3.4, Section 1.2, p. 17,
https://www.jirka.org/scv/scv-3.4.pdf (multivariate geometric series).
The explicit bounds here are elementary consequences of these methods, not
verbatim statements from the references. Products use `∏ (α_i + 1) ≤ ∏ 2^α_i`.
For inversion, normalize the coefficient recurrence by `|c| r^α` and induct;
the geometric ratio sum bounds the recursive multiplier by `1`. Equality in
that bound is allowed; this is not a strict Neumann-norm convergence condition.
-/

@[expose] public section
namespace MvPowerSeries

/-- The weight `∏ R_i^(−α_i)` of a majorant at an index. -/
noncomputable def radiiWeight {σ : Type*} [Fintype σ] (R : σ → ℚ) (α : (σ →₀ ℕ)) : ℚ :=
  ∏ i, (R i ^ α i)⁻¹

/-- Weights are positive. -/
theorem radiiWeight_pos {σ : Type*} [Fintype σ] {R : σ → ℚ}
    (hR : ∀ i, 0 < R i) (α : (σ →₀ ℕ)) : 0 < radiiWeight R α :=
  Finset.prod_pos fun i _ => inv_pos.mpr (pow_pos (hR i) _)

/-- Weights are multiplicative in the index. -/
theorem radiiWeight_add {σ : Type*} [Fintype σ] (R : σ → ℚ) (α β : (σ →₀ ℕ)) :
    radiiWeight R (α + β) = radiiWeight R α * radiiWeight R β := by
  unfold radiiWeight
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finsupp.add_apply, pow_add, mul_inv]

/-- A coefficient majorant with nonnegative bound and positive radii. -/
structure GeometricMajorant (σ : Type*) where
  /-- The common coefficient bound. -/
  bound : ℚ
  /-- Positive radius along each variable. -/
  radius : σ → ℚ
  bound_nonneg : 0 ≤ bound
  radius_pos : ∀ i, 0 < radius i

/-- Every coefficient is bounded by the supplied geometric weight. -/
def IsMajorized {σ : Type*} [Fintype σ] (a : MvPowerSeries σ ℚ)
    (m : GeometricMajorant σ) : Prop :=
  ∀ α : σ →₀ ℕ, |coeff α a| ≤ m.bound * ∏ i, (m.radius i ^ α i)⁻¹

private theorem isMajorized_iff {σ : Type*} [Fintype σ]
    (a : MvPowerSeries σ ℚ) (m : GeometricMajorant σ) :
    IsMajorized a m ↔ ∀ α : σ →₀ ℕ,
      |coeff α a| ≤ m.bound * ∏ i, (m.radius i ^ α i)⁻¹ := Iff.rfl

/-- Shrinking the radii and raising the bound keeps a majorant. -/
theorem IsMajorized.mono {σ : Type*} [Fintype σ] {a : MvPowerSeries σ ℚ}
    {m : GeometricMajorant σ} (h : IsMajorized a m)
    (m' : GeometricMajorant σ) (bound : m.bound ≤ m'.bound)
    (radius : ∀ i, m'.radius i ≤ m.radius i) :
    IsMajorized a m' := by
  classical
  intro α
  refine (h α).trans (mul_le_mul bound ?_
    (le_of_lt (radiiWeight_pos m.radius_pos α)) m'.bound_nonneg)
  refine Finset.prod_le_prod₀ (fun i _ => le_of_lt (inv_pos.mpr (pow_pos (m.radius_pos i) _)))
    fun i _ => ?_
  exact inv_anti₀ (pow_pos (m'.radius_pos i) _) (pow_le_pow_left₀ (le_of_lt (m'.radius_pos i))
    (radius i) _)

/-- Scaling by a constant scales the bound. -/
theorem IsMajorized.C_mul {σ : Type*} [Fintype σ] {a : MvPowerSeries σ ℚ}
    {m : GeometricMajorant σ} (h : IsMajorized a m)
    (q : ℚ) : IsMajorized (C q * a)
      ⟨|q| * m.bound, m.radius, mul_nonneg (abs_nonneg q) m.bound_nonneg, m.radius_pos⟩ := by
  rw [isMajorized_iff] at h ⊢
  classical
  intro α
  rw [coeff_C_mul, abs_mul]
  calc |q| * |coeff α a| ≤ |q| * (m.bound * ∏ i, (m.radius i ^ α i)⁻¹) :=
        mul_le_mul_of_nonneg_left (h α) (abs_nonneg q)
    _ = _ := by ring

/-- `∏ q_i^{β_i}`, the ratio of two radiiWeights. -/
noncomputable def qpow {σ : Type*} [Fintype σ] (q : σ → ℚ) (β : (σ →₀ ℕ)) : ℚ :=
  ∏ i, q i ^ β i

/-- The empty index has ratio power `1`. -/
theorem qpow_zero {σ : Type*} [Fintype σ] (q : σ → ℚ) : qpow q 0 = 1 := by simp [qpow]

/-- A weight at the larger radii is the weight at the smaller times a ratio power. -/
theorem radiiWeight_eq_radiiWeight_mul_qpow {σ : Type*} [Fintype σ]
    {R r : σ → ℚ} (hR : ∀ i, 0 < R i)
    (hr : ∀ i, 0 < r i) (β : (σ →₀ ℕ)) :
    radiiWeight R β = radiiWeight r β * qpow (fun i => r i / R i) β := by
  unfold radiiWeight qpow
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have := (hR i).ne'
  have := (hr i).ne'
  rw [div_pow]
  field_simp

/-- An antidiagonal sum of separable weights factors into finite geometric sums. -/
theorem sum_antidiagonal_qpow {σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : σ → ℚ) (α : σ →₀ ℕ) :
    ∑ p ∈ Finset.antidiagonal α, qpow q p.1 =
      ∏ i, ∑ j ∈ Finset.range (α i + 1), q i ^ j := by
  classical
  rw [Finset.prod_univ_sum]
  refine Finset.sum_bij (fun p _ => fun i => p.1 i) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Fintype.mem_piFinset, Finset.mem_range]
    intro i
    have h := congrArg (fun n : σ →₀ ℕ => n i) (Finset.mem_antidiagonal.mp hp)
    simp only [Finsupp.add_apply] at h
    omega
  · intro p hp q hq he
    have hfst : p.1 = q.1 := Finsupp.ext fun i => congrFun he i
    apply Prod.ext hfst
    apply add_left_cancel (a := p.1)
    rw [Finset.mem_antidiagonal.mp hp, hfst, Finset.mem_antidiagonal.mp hq]
  · intro g hg
    let β : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm g
    have hβ : β ≤ α := by
      intro i
      have hi := (Fintype.mem_piFinset.mp hg) i
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    refine ⟨(β, α - β), Finset.mem_antidiagonal.mpr (add_tsub_cancel_of_le hβ), ?_⟩
    rfl
  · intro p hp
    rfl

/-- The antidiagonal cardinality is the product of coordinate lengths. -/
theorem card_antidiagonal_eq {σ : Type*} [Fintype σ] [DecidableEq σ] (α : σ →₀ ℕ) :
    ((Finset.antidiagonal α).card : ℚ) = ∏ i, ((α i : ℚ) + 1) := by
  simpa [qpow] using sum_antidiagonal_qpow (fun _ : σ => 1) α

/-- At most `2^|α|` terms. -/
theorem card_antidiagonal_le {σ : Type*} [Fintype σ] [DecidableEq σ] (α : (σ →₀ ℕ)) :
    ((Finset.antidiagonal α).card : ℚ) ≤ ∏ i, (2 : ℚ) ^ α i := by
  rw [card_antidiagonal_eq]
  refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
  exact_mod_cast Nat.lt_two_pow_self (n := α i)

/-- **Products.** Bounds multiply and radii halve: the antidiagonal of `α` has
at most `2^|α|` terms. -/
theorem IsMajorized.mul {σ : Type*} [Fintype σ] {a b : MvPowerSeries σ ℚ}
    {ma mb : GeometricMajorant σ} (R : σ → ℚ)
    (ha : IsMajorized a ma) (hb : IsMajorized b mb)
    (ra : ∀ i, ma.radius i = R i) (rb : ∀ i, mb.radius i = R i) :
    IsMajorized (a * b)
      ⟨ma.bound * mb.bound, fun i => R i / 2, mul_nonneg ma.bound_nonneg mb.bound_nonneg,
        fun i => by rw [← ra i]; exact half_pos (ma.radius_pos i)⟩ := by
  rw [isMajorized_iff] at ha hb ⊢
  classical
  intro α
  have hR : ∀ i, 0 < R i := fun i => ra i ▸ ma.radius_pos i
  rw [coeff_mul]
  calc |∑ p ∈ Finset.antidiagonal α, coeff p.1 a * coeff p.2 b|
      ≤ ∑ p ∈ Finset.antidiagonal α, |coeff p.1 a * coeff p.2 b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Finset.antidiagonal α, ma.bound * mb.bound * radiiWeight R α := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [Finset.mem_antidiagonal] at hp
        rw [abs_mul]
        have h1 := ha p.1
        have h2 := hb p.2
        simp only [ra, rb] at h1 h2
        calc |coeff p.1 a| * |coeff p.2 b|
            ≤ (ma.bound * radiiWeight R p.1) * (mb.bound * radiiWeight R p.2) :=
              mul_le_mul h1 h2 (abs_nonneg _)
                (mul_nonneg ma.bound_nonneg (le_of_lt (radiiWeight_pos hR p.1)))
          _ = ma.bound * mb.bound * radiiWeight R (p.1 + p.2) := by rw [radiiWeight_add]; ring
          _ = ma.bound * mb.bound * radiiWeight R α := by rw [hp]
    _ = (Finset.antidiagonal α).card * (ma.bound * mb.bound * radiiWeight R α) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (∏ i, (2 : ℚ) ^ α i) * (ma.bound * mb.bound * radiiWeight R α) :=
        mul_le_mul_of_nonneg_right (card_antidiagonal_le α)
          (mul_nonneg (mul_nonneg ma.bound_nonneg mb.bound_nonneg)
            (le_of_lt (radiiWeight_pos hR α)))
    _ = ma.bound * mb.bound * ∏ i, ((R i / 2) ^ α i)⁻¹ := by
        unfold radiiWeight
        rw [mul_comm, mul_assoc, ← Finset.prod_mul_distrib]
        congr 1
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [div_pow, inv_div, div_eq_mul_inv, mul_comm]

/-! ## The inverse -/

/-- The sum of ratio powers over the box below `α`, minus the empty index, is below
`∏ (1 − q_i)⁻¹ − 1`. -/
theorem sum_antidiagonal_qpow_lt_le {σ : Type*} [Fintype σ] [DecidableEq σ]
    {q : σ → ℚ} (hq0 : ∀ i, 0 ≤ q i)
    (hq1 : ∀ i, q i < 1) (α : (σ →₀ ℕ)) :
    ∑ p ∈ Finset.antidiagonal α, (if p.2 < α then qpow q p.1 else 0) ≤
      (∏ i, (1 - q i)⁻¹) - 1 := by
  classical
  have mem : ((0 : (σ →₀ ℕ)), α) ∈ Finset.antidiagonal α := by simp
  have filter_eq : (Finset.antidiagonal α).filter (fun p => p.2 < α) =
      (Finset.antidiagonal α).erase (0, α) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_antidiagonal]
    constructor
    · rintro ⟨sum, lt⟩
      refine ⟨fun e => ?_, sum⟩
      rw [e] at lt
      exact lt_irrefl _ lt
    · rintro ⟨ne, sum⟩
      refine ⟨sum, lt_of_le_of_ne ?_ fun e => ne ?_⟩
      · rw [← sum]; exact le_add_self
      · have first : p.1 = 0 := by
          rw [e] at sum
          exact add_right_cancel (sum.trans (zero_add α).symm)
        exact Prod.ext first e
  rw [← Finset.sum_filter, filter_eq, Finset.sum_erase_eq_sub mem, qpow_zero,
    sum_antidiagonal_qpow]
  refine sub_le_sub_right ?_ 1
  exact Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun j _ => pow_nonneg (hq0 i) _)
    fun i _ => by
      simpa only [Nat.Ico_zero_eq_range, pow_zero, one_div] using
        geom_sum_Ico_le_of_lt_one (m := 0) (n := α i + 1) (hq0 i) (hq1 i)
/-- **Inverse.** If `φ` has constant term `c` and the rest of it is majorized
by `M` at radii `R`, then `φ⁻¹` is majorized by `1/|c|` at any smaller radii `r`
whose ratio tail is small: `(M/|c|)(∏ (1 − r_i/R_i)⁻¹ − 1) ≤ 1`. By
well-founded induction on the index through `coeff_inv`.
(`c = 0` is allowed: Mathlib's inverse is then `0`,
`M / |c|` is `0`, and the bound `0 ≤ 0` is trivially true.) -/
theorem coeff_inv_le {σ : Type*} [Fintype σ] (φ : MvPowerSeries σ ℚ)
    {c M : ℚ} (hc : constantCoeff φ = c)
    (hM : 0 ≤ M)
    {R r : σ → ℚ} (hR : ∀ i, 0 < R i) (hr : ∀ i, 0 < r i)
    (inside : ∀ i, r i < R i)
    (rest : ∀ α : (σ →₀ ℕ), α ≠ 0 → |coeff α φ| ≤ M * radiiWeight R α)
    (small : M / |c| * ((∏ i, (1 - r i / R i)⁻¹) - 1) ≤ 1) (α : (σ →₀ ℕ)) :
    |coeff α φ⁻¹| ≤ |c|⁻¹ * radiiWeight r α := by
  classical
  refine WellFounded.induction (wellFounded_lt (α := (σ →₀ ℕ)))
    (C := fun α => |coeff α φ⁻¹| ≤ |c|⁻¹ * radiiWeight r α) α ?_
  intro α ih
  set q : σ → ℚ := fun i => r i / R i with hq
  have hq0 : ∀ i, 0 ≤ q i := fun i => div_nonneg (le_of_lt (hr i)) (le_of_lt (hR i))
  have hq1 : ∀ i, q i < 1 := fun i => (div_lt_one (hR i)).mpr (inside i)
  by_cases hα : α = 0
  · subst hα
    rw [show coeff (0 : (σ →₀ ℕ)) φ⁻¹ = (constantCoeff φ)⁻¹ from
      (congrFun coeff_zero_eq_constantCoeff φ⁻¹).trans (constantCoeff_inv φ), hc, abs_inv]
    simp [radiiWeight]
  rw [coeff_inv, ite_eq_right hα, hc, abs_mul, abs_neg, abs_inv]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (abs_nonneg c))
  have wpos := radiiWeight_pos hr α
  calc |∑ x ∈ Finset.antidiagonal α, if x.2 < α then coeff x.1 φ * coeff x.2 φ⁻¹ else 0|
      ≤ ∑ x ∈ Finset.antidiagonal α, |if x.2 < α then coeff x.1 φ * coeff x.2 φ⁻¹ else 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ Finset.antidiagonal α,
          (if x.2 < α then M * |c|⁻¹ * radiiWeight r α * qpow q x.1 else 0) := by
        refine Finset.sum_le_sum fun x hx => ?_
        rw [Finset.mem_antidiagonal] at hx
        split_ifs with lt
        · have first : x.1 ≠ 0 := fun e => by
            rw [e, zero_add] at hx
            rw [hx] at lt
            exact lt_irrefl _ lt
          rw [abs_mul]
          calc |coeff x.1 φ| * |coeff x.2 φ⁻¹|
              ≤ (M * radiiWeight R x.1) * (|c|⁻¹ * radiiWeight r x.2) :=
                mul_le_mul (rest x.1 first) (ih x.2 lt) (abs_nonneg _)
                  (mul_nonneg hM (le_of_lt (radiiWeight_pos hR x.1)))
            _ = M * |c|⁻¹ * radiiWeight r α * qpow q x.1 := by
                rw [radiiWeight_eq_radiiWeight_mul_qpow hR hr, ← hx, radiiWeight_add]
                ring
        · simp
    _ = M * |c|⁻¹ * radiiWeight r α *
          ∑ x ∈ Finset.antidiagonal α, (if x.2 < α then qpow q x.1 else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        split_ifs <;> simp
    _ ≤ M * |c|⁻¹ * radiiWeight r α * ((∏ i, (1 - q i)⁻¹) - 1) :=
        mul_le_mul_of_nonneg_left (sum_antidiagonal_qpow_lt_le hq0 hq1 α)
          (mul_nonneg (mul_nonneg hM (inv_nonneg.mpr (abs_nonneg c))) (le_of_lt wpos))
    _ = radiiWeight r α * (M / |c| * ((∏ i, (1 - q i)⁻¹) - 1)) := by ring
    _ ≤ radiiWeight r α * 1 := mul_le_mul_of_nonneg_left small (le_of_lt wpos)
    _ = radiiWeight r α := mul_one _

/-- The inverse's majorant, packaged for convergence and tail estimates. -/
theorem isMajorized_inv {σ : Type*} [Fintype σ] (φ : MvPowerSeries σ ℚ)
    {c M : ℚ} (hc : constantCoeff φ = c)
    (hM : 0 ≤ M)
    {R r : σ → ℚ} (hR : ∀ i, 0 < R i) (hr : ∀ i, 0 < r i)
    (inside : ∀ i, r i < R i)
    (rest : ∀ α : (σ →₀ ℕ), α ≠ 0 → |coeff α φ| ≤ M * radiiWeight R α)
    (small : M / |c| * ((∏ i, (1 - r i / R i)⁻¹) - 1) ≤ 1) :
    IsMajorized φ⁻¹ ⟨|c|⁻¹, r, inv_nonneg.mpr (abs_nonneg c), hr⟩ := by
  rw [isMajorized_iff]
  exact coeff_inv_le φ hc hM hR hr inside rest small

end MvPowerSeries
