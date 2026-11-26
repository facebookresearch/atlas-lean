/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.PoincareMixing

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Dirichlet forms on a finite state space

On a finite set `S` with weights `m : S → ℝ`, a matrix `Q` whose off-diagonal entries are
nonnegative and whose row sums are nonpositive (a *sub-Markovian generator*) defines the
bilinear form

`E(f, g) = ½ ∑_{x,y} m(x) Q(x, y) (f x - f y) (g x - g y) + ∑_x m(x) k(x) f(x) g(x)`,

where `k(x) = -∑_y Q(x, y) ≥ 0` is the killing rate. This is the finite case of
Fukushima, Oshima and Takeda, *Dirichlet Forms and Symmetric Markov Processes*, 2nd revised and
extended edition (de Gruyter, 2011), Example 1.2.5, equation (1.2.27). When `m` is in detailed
balance with `Q`, `E(f, g) = -∑_x m(x) f(x) (Q g)(x)`; for a stochastic matrix `P` and
`Q = P - 1` there is no killing and `E(f, f) = ½ ∑ m(x) P(x, y) (f x - f y)²`, the Dirichlet form
whose identity with `∑ π g (g - P g)` A. Sinclair's variational characterisation uses
(`MathlibExt.Probability.PoincareMixing.sum_mul_sub_mulVec_eq`).

The *Markov property* of a symmetric form (FOT §1.1, conditions (E.4)′ and (E.4)″): normal
contractions, and in particular the unit contraction `u ↦ (0 ∨ u) ∧ 1`, do not increase the
energy. We prove it for these forms, and prove the converse on `ℝⁿ` (the finite-dimensional
Beurling–Deny criterion): the quadratic form `u ⬝ A u` of a symmetric matrix is
unit-contractive exactly when `A` has nonpositive off-diagonal entries and nonnegative row sums,
that is, when `-A` is a symmetric sub-Markovian generator and the form is the one above with
`m = 1` and `Q = -A`. On a finite set every form is closed, so these are exactly the Dirichlet
forms on `ℓ²(S)` with counting measure.

## Main definitions

* `killingRate Q x = -∑_y Q x y`.
* `form m Q f g`: the bilinear form (1.2.27).
* `unitContraction u = (0 ∨ u) ∧ 1`, pointwise.
* `matrixForm A u v = u ⬝ᵥ A *ᵥ v`.

## Main results

* `form_eq_neg_sum_mul_mulVec`: under detailed balance, `E(f, g) = -∑ m f (Q g)`.
* `form_sub_one`: for unit row sums, `E_{P - 1}(f, g) = ½ ∑ m P (f x - f y)(g x - g y)`.
* `form_sub_one_self_eq_sum_mul_sub_mulVec`: the bridge to Sinclair's identity.
* `form_le_form_of_normal_contraction`, `form_unitContraction_le`: the Markov property.
* `unitContraction_le_iff`: the Beurling–Deny criterion on `ℝⁿ`.
* `unitContraction_le_iff_exists_generator`: the same, phrased as "comes from a symmetric
  sub-Markovian generator".

## References

* M. Fukushima, Y. Oshima and M. Takeda, *Dirichlet Forms and Symmetric Markov Processes*, 2nd
  revised and extended edition, de Gruyter Studies in Mathematics 19, 2011: §1.1 and
  Example 1.2.5.
* Z.-M. Ma and M. Röckner, *Introduction to the Theory of (Non-Symmetric) Dirichlet Forms*,
  Springer Universitext, 1992 (the general framework; not used for theorem numbers here).
-/

@[expose] public section

open Finset Matrix ProbabilityTheory

namespace MathlibExt.Probability.DirichletForm

variable {S : Type*} [Fintype S]

/-- **Killing rate of a generator.** For a square matrix `Q`, `k(x) = -∑_y Q(x, y)`; it is
nonnegative exactly when the row sums of `Q` are nonpositive, and zero for a rate matrix
(Fukushima, Oshima and Takeda, *Dirichlet Forms and Symmetric Markov Processes*, 2nd ed., 2011,
Example 1.2.5, `k_i = -q_ii - ∑_{j ≠ i} q_ij`). -/
def killingRate (Q : Matrix S S ℝ) (x : S) : ℝ :=
  -∑ y, Q x y

/-- **Dirichlet form of a sub-Markovian generator on a finite set.** For weights `m` and a matrix
`Q`,
`E(f, g) = ½ ∑_{x,y} m(x) Q(x, y) (f x - f y)(g x - g y) + ∑_x m(x) k(x) f(x) g(x)`
with `k = killingRate Q` (Fukushima, Oshima and Takeda, *Dirichlet Forms and Symmetric Markov
Processes*, 2nd ed., 2011, Example 1.2.5, equation (1.2.27), on a finite set). The diagonal
entries of `Q` contribute only through `k`. FOT assume `m` symmetrising (`m(x) Q(x, y) = m(y)
Q(y, x)`, their (1.2.26)); the definition here makes sense for every `(m, Q)`, and without detailed
balance it is the form of the `m`-symmetrised generator (the Markov property below does not need
detailed balance). -/
noncomputable def form (m : S → ℝ) (Q : Matrix S S ℝ) (f g : S → ℝ) : ℝ :=
  1 / 2 * ∑ x, ∑ y, m x * Q x y * (f x - f y) * (g x - g y) +
    ∑ x, m x * killingRate Q x * f x * g x

/-- **The form is symmetric.** `E(f, g) = E(g, f)` for every `m`, `Q`, `f`, `g`. -/
theorem form_comm (m : S → ℝ) (Q : Matrix S S ℝ) (f g : S → ℝ) :
    form m Q f g = form m Q g f := by
  unfold form
  congr 1
  · congr 1
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  · exact Finset.sum_congr rfl fun x _ => by ring

/-- **The form of a reversible generator is `-⟨f, Q g⟩`.** If `m` is in detailed balance with
`Q` (`m(x) Q(x, y) = m(y) Q(y, x)`), then `E(f, g) = -∑_x m(x) f(x) (Q g)(x)` (Fukushima, Oshima
and Takeda, *Dirichlet Forms and Symmetric Markov Processes*, 2nd ed., 2011, Example 1.2.5:
`E(f, g) = -(Qf, g)_{L²(m)}`, which is the same by symmetry). -/
theorem form_eq_neg_sum_mul_mulVec {m : S → ℝ} {Q : Matrix S S ℝ} (hrev : IsDetailedBalance m Q)
    (f g : S → ℝ) : form m Q f g = -∑ x, m x * f x * (Q *ᵥ g) x := by
  unfold form killingRate
  -- Expand the square bracket into four double sums.
  have e : ∀ x y, m x * Q x y * (f x - f y) * (g x - g y) =
      m x * Q x y * f x * g x - m x * Q x y * f x * g y - m y * Q y x * f y * g x +
        m y * Q y x * f y * g y := by
    intro x y; rw [← hrev x y]; ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h1 : ∑ x, ∑ y, m y * Q y x * f y * g y = ∑ x, ∑ y, m x * Q x y * f x * g x := by
    rw [Finset.sum_comm]
  have h2 : ∑ x, ∑ y, m y * Q y x * f y * g x = ∑ x, ∑ y, m x * Q x y * f x * g y := by
    rw [Finset.sum_comm]
  rw [h1, h2]
  have h3 : ∀ x, ∑ y, m x * Q x y * f x * g x = m x * f x * g x * ∑ y, Q x y := by
    intro x; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
  have h4 : ∀ x, ∑ y, m x * Q x y * f x * g y = m x * f x * (Q *ᵥ g) x := by
    intro x; simp only [mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  simp only [h3, h4]
  have h5 : ∑ x, (m x * -∑ y, Q x y) * f x * g x = -∑ x, m x * f x * g x * ∑ y, Q x y := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [h5]; ring

/-- **No killing for a Markov kernel.** If the rows of `P` sum to `1`, the generator `P - 1` has
zero killing rate. -/
theorem killingRate_sub_one [DecidableEq S] {P : Matrix S S ℝ} (hrow : ∀ x, ∑ y, P x y = 1)
    (x : S) : killingRate (P - 1) x = 0 := by
  simp [killingRate, Matrix.sub_apply, Finset.sum_sub_distrib, hrow, Matrix.one_apply]

/-- **The Dirichlet form of a Markov kernel.** If the rows of `P` sum to `1`, the form of the
generator `P - 1` is `E(f, g) = ½ ∑_{x,y} m(x) P(x, y) (f x - f y)(g x - g y)`; in particular
`E(f, f) = ½ ∑ m(x) P(x, y) (f x - f y)²` (Fukushima, Oshima and Takeda, *Dirichlet Forms and
Symmetric Markov Processes*, 2nd ed., 2011, equation (1.2.27) with `q_ij = P(i, j)` for `i ≠ j`
and `k = 0`; P. Diaconis and L. Saloff-Coste, *Ann. Appl. Probab.* 6 (1996), equation (1.4)). -/
theorem form_sub_one [DecidableEq S] (m : S → ℝ) {P : Matrix S S ℝ}
    (hrow : ∀ x, ∑ y, P x y = 1) (f g : S → ℝ) :
    form m (P - 1) f g = 1 / 2 * ∑ x, ∑ y, m x * P x y * (f x - f y) * (g x - g y) := by
  unfold form
  simp only [killingRate_sub_one hrow, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  congr 1
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  by_cases h : x = y
  · subst h; ring
  · simp [Matrix.sub_apply, h]

/-- **Sinclair's identity in Dirichlet-form terms.** If `P` has unit row sums and is in detailed
balance with `π`, then `E_{P - 1}(g, g) = ∑_x π(x) g(x) (g(x) - (P g)(x))`. This restates
`MathlibExt.Probability.PoincareMixing.sum_mul_sub_mulVec_eq` (the identity behind the
variational characterisation (5) of A. Sinclair, *Combin. Probab. Comput.* 1 (1992)) through
`form_sub_one`. -/
theorem form_sub_one_self_eq_sum_mul_sub_mulVec [DecidableEq S] {π : S → ℝ} {P : Matrix S S ℝ}
    (hrow : ∀ x, ∑ y, P x y = 1) (hrev : IsDetailedBalance π P) (g : S → ℝ) :
    form π (P - 1) g g = ∑ x, π x * g x * (g x - (P *ᵥ g) x) := by
  rw [form_sub_one π hrow, PoincareMixing.sum_mul_sub_mulVec_eq hrow hrev]
  congr 1
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

/-- **Energy comparison under a normal contraction.** Let `m ≥ 0`, let `Q` have nonnegative
off-diagonal entries and nonnegative killing rate (row sums `≤ 0`). If `v` is a normal
contraction of `u`, that is `|v x - v y| ≤ |u x - u y|` and `|v x| ≤ |u x|` for all `x, y`, then
`E(v, v) ≤ E(u, u)`: every normal contraction operates on the form (Fukushima, Oshima and
Takeda, *Dirichlet Forms and Symmetric Markov Processes*, 2nd ed., 2011, §1.1, condition
(E.4)″, for the form (1.2.27)). -/
theorem form_le_form_of_normal_contraction {m : S → ℝ} {Q : Matrix S S ℝ} (hm : ∀ x, 0 ≤ m x)
    (hQ : ∀ x y, x ≠ y → 0 ≤ Q x y) (hk : ∀ x, 0 ≤ killingRate Q x) {u v : S → ℝ}
    (h1 : ∀ x y, |v x - v y| ≤ |u x - u y|) (h2 : ∀ x, |v x| ≤ |u x|) :
    form m Q v v ≤ form m Q u u := by
  unfold form
  have hpair : ∀ x y, m x * Q x y * (v x - v y) * (v x - v y) ≤
      m x * Q x y * (u x - u y) * (u x - u y) := by
    intro x y
    by_cases h : x = y
    · subst h; simp
    · have hc : 0 ≤ m x * Q x y := mul_nonneg (hm x) (hQ x y h)
      have hsq : (v x - v y) ^ 2 ≤ (u x - u y) ^ 2 := sq_le_sq.mpr (h1 x y)
      calc m x * Q x y * (v x - v y) * (v x - v y) = m x * Q x y * (v x - v y) ^ 2 := by ring
        _ ≤ m x * Q x y * (u x - u y) ^ 2 := mul_le_mul_of_nonneg_left hsq hc
        _ = m x * Q x y * (u x - u y) * (u x - u y) := by ring
  have hkill : ∀ x, m x * killingRate Q x * v x * v x ≤ m x * killingRate Q x * u x * u x := by
    intro x
    have hc : 0 ≤ m x * killingRate Q x := mul_nonneg (hm x) (hk x)
    have hsq : v x ^ 2 ≤ u x ^ 2 := sq_le_sq.mpr (h2 x)
    calc m x * killingRate Q x * v x * v x = m x * killingRate Q x * v x ^ 2 := by ring
      _ ≤ m x * killingRate Q x * u x ^ 2 := mul_le_mul_of_nonneg_left hsq hc
      _ = m x * killingRate Q x * u x * u x := by ring
  have hs : ∑ x, ∑ y, m x * Q x y * (v x - v y) * (v x - v y) ≤
      ∑ x, ∑ y, m x * Q x y * (u x - u y) * (u x - u y) :=
    Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hpair x y
  have hk' := Finset.sum_le_sum fun x (_ : x ∈ (univ : Finset S)) => hkill x
  linarith

/-- **Unit contraction.** The function `(0 ∨ u) ∧ 1`, that is `max 0 (min (u x) 1)` at every
point (Fukushima, Oshima and Takeda, *Dirichlet Forms and Symmetric Markov Processes*, 2nd ed.,
2011, §1.1, condition (E.4)′). -/
def unitContraction (u : S → ℝ) (x : S) : ℝ :=
  max 0 (min (u x) 1)

omit [Fintype S] in
/-- **The unit contraction is a normal contraction (differences).**
`|((0 ∨ u) ∧ 1)(x) - ((0 ∨ u) ∧ 1)(y)| ≤ |u x - u y|`. -/
theorem abs_unitContraction_sub_le (u : S → ℝ) (x y : S) :
    |unitContraction u x - unitContraction u y| ≤ |u x - u y| := by
  unfold unitContraction
  calc |max 0 (min (u x) 1) - max 0 (min (u y) 1)|
      ≤ |min (u x) 1 - min (u y) 1| := by
        simpa only [max_comm (0 : ℝ)] using abs_max_sub_max_le_abs (min (u x) 1) (min (u y) 1) 0
    _ ≤ max |u x - u y| |1 - 1| := abs_min_sub_min_le_max _ _ _ _
    _ = |u x - u y| := by simp

omit [Fintype S] in
/-- **The unit contraction is a normal contraction (values).** `|((0 ∨ u) ∧ 1)(x)| ≤ |u x|`. -/
theorem abs_unitContraction_le (u : S → ℝ) (x : S) : |unitContraction u x| ≤ |u x| := by
  unfold unitContraction
  rw [abs_le]
  constructor
  · have := le_max_left 0 (min (u x) 1); linarith [abs_nonneg (u x)]
  · refine max_le (abs_nonneg _) ?_
    exact (min_le_left _ _).trans (le_abs_self _)

/-- **The Markov property of the form of a sub-Markovian generator.** Under the hypotheses of
`form_le_form_of_normal_contraction`, the unit contraction does not increase the energy:
`E((0 ∨ u) ∧ 1, (0 ∨ u) ∧ 1) ≤ E(u, u)` (Fukushima, Oshima and Takeda, *Dirichlet Forms and
Symmetric Markov Processes*, 2nd ed., 2011, §1.1, condition (E.4)′, and Example 1.2.5, where the
form (1.2.27) is shown to be a Dirichlet form). -/
theorem form_unitContraction_le {m : S → ℝ} {Q : Matrix S S ℝ} (hm : ∀ x, 0 ≤ m x)
    (hQ : ∀ x y, x ≠ y → 0 ≤ Q x y) (hk : ∀ x, 0 ≤ killingRate Q x) (u : S → ℝ) :
    form m Q (unitContraction u) (unitContraction u) ≤ form m Q u u :=
  form_le_form_of_normal_contraction hm hQ hk (abs_unitContraction_sub_le u)
    (abs_unitContraction_le u)

/-- **The form of a sub-Markovian generator is nonnegative.** Under the hypotheses of
`form_le_form_of_normal_contraction`, `0 ≤ E(u, u)`. -/
theorem form_self_nonneg {m : S → ℝ} {Q : Matrix S S ℝ} (hm : ∀ x, 0 ≤ m x)
    (hQ : ∀ x y, x ≠ y → 0 ≤ Q x y) (hk : ∀ x, 0 ≤ killingRate Q x) (u : S → ℝ) :
    0 ≤ form m Q u u := by
  have h := form_le_form_of_normal_contraction (v := 0) hm hQ hk (u := u)
    (fun x y => by simp) (fun x => by simp)
  simpa [form] using h

/-- **Quadratic form of a matrix on `ℝⁿ`.** `matrixForm A u v = u ⬝ᵥ (A *ᵥ v)
= ∑_{x,y} u(x) A(x, y) v(y)`, the bilinear form on `ℝ^S` (counting measure) of the matrix `A`. -/
def matrixForm (A : Matrix S S ℝ) (u v : S → ℝ) : ℝ :=
  u ⬝ᵥ (A *ᵥ v)

/-- **A symmetric matrix form is the form of the generator `-A`.** If `A` is symmetric, then
`u ⬝ A v = E(u, v)` for the form (1.2.27) with `m = 1` and `Q = -A`, that is
`u ⬝ A v = ½ ∑_{x,y} (-A(x, y)) (u x - u y)(v x - v y) + ∑_x (∑_y A(x, y)) u(x) v(x)`. -/
theorem matrixForm_eq_form {A : Matrix S S ℝ} (hA : A.IsSymm) (u v : S → ℝ) :
    matrixForm A u v = form 1 (-A) u v := by
  have hrev : IsDetailedBalance (1 : S → ℝ) (-A) := by
    intro i j
    simp only [Pi.one_apply, one_mul, Matrix.neg_apply, neg_inj]
    exact (hA.apply i j).symm
  rw [form_eq_neg_sum_mul_mulVec hrev]
  simp only [matrixForm, dotProduct, Matrix.neg_mulVec, Pi.neg_apply, Pi.one_apply, one_mul,
    mul_neg, Finset.sum_neg_distrib, neg_neg]

/-- **Beurling–Deny criterion on `ℝⁿ`.** For a symmetric matrix `A` on a finite set, the unit
contraction operates on the form `u ⬝ A u`, i.e. `E((0 ∨ u) ∧ 1) ≤ E(u)` for every `u`, if and
only if `A(x, y) ≤ 0` for `x ≠ y` and every row sum `∑_y A(x, y)` is nonnegative. This is the
finite-dimensional case of the Markov property of Fukushima, Oshima and Takeda, *Dirichlet Forms
and Symmetric Markov Processes*, 2nd ed., 2011, §1.1, condition (E.4)′: sufficiency is
Example 1.2.5 with `m = 1`, `Q = -A`; necessity is tested on `u = 1_x - c 1_y` and
`u = 1 + c 1_x` for small `c > 0`. -/
theorem unitContraction_le_iff {A : Matrix S S ℝ} (hA : A.IsSymm) :
    (∀ u : S → ℝ, matrixForm A (unitContraction u) (unitContraction u) ≤ matrixForm A u u) ↔
      (∀ x y, x ≠ y → A x y ≤ 0) ∧ ∀ x, 0 ≤ ∑ y, A x y := by
  classical
  constructor
  · intro h
    constructor
    · intro x y hxy
      by_contra hpos'
      have hpos : 0 < A x y := lt_of_not_ge hpos'
      set c : ℝ := A x y / (|A y y| + 1) with hc
      have hden : 0 < |A y y| + 1 := by positivity
      have hc0 : 0 < c := div_pos hpos hden
      have hcA : c * A y y < A x y := by
        have : c * (|A y y| + 1) = A x y := by rw [hc]; field_simp
        nlinarith [le_abs_self (A y y), abs_nonneg (A y y)]
      have hu := h (Pi.single x 1 - c • Pi.single y 1)
      have hcon : unitContraction (Pi.single x 1 - c • Pi.single y 1) = Pi.single x (1 : ℝ) := by
        funext z
        unfold unitContraction
        by_cases hzx : z = x
        · subst hzx; simp [hxy]
        · by_cases hzy : z = y
          · subst hzy
            simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_apply, hzx, ite_false, ite_true,
              smul_eq_mul, mul_one, zero_sub]
            rw [min_eq_left (by linarith), max_eq_left (by linarith)]
          · simp [hzx, hzy]
      rw [hcon] at hu
      have hsym : A y x = A x y := hA.apply x y
      simp only [matrixForm, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_single,
        dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct, single_dotProduct,
        one_mul, smul_eq_mul] at hu
      simp [hsym] at hu
      nlinarith
    · intro x
      by_contra hneg'
      have hneg : ∑ y, A x y < 0 := lt_of_not_ge hneg'
      set r := ∑ y, A x y with hr
      set c : ℝ := -r / (|A x x| + 1) with hc
      have hden : 0 < |A x x| + 1 := by positivity
      have hc0 : 0 < c := div_pos (by linarith) hden
      have hcA : c * A x x < -r := by
        have : c * (|A x x| + 1) = -r := by rw [hc]; field_simp
        nlinarith [le_abs_self (A x x), abs_nonneg (A x x)]
      have hu := h (1 + c • Pi.single x 1)
      have hcon : unitContraction (1 + c • Pi.single x 1) = (1 : S → ℝ) := by
        funext z
        unfold unitContraction
        by_cases hzx : z = x
        · subst hzx
          simp only [Pi.add_apply, Pi.one_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
            mul_one]
          rw [min_eq_right (by linarith), max_eq_right (by norm_num)]
        · simp [hzx]
      rw [hcon] at hu
      have hcol : ∑ z, A z x = r := by
        rw [hr]; exact Finset.sum_congr rfl fun z _ => hA.apply x z
      have h1 : ((1 : S → ℝ) ⬝ᵥ (A *ᵥ Pi.single x 1)) = r := by
        simp [Matrix.mulVec_single, dotProduct, hcol]
      have h2 : (Pi.single x (1 : ℝ) ⬝ᵥ (A *ᵥ 1)) = r := by
        rw [single_dotProduct, one_mul]; simp [mulVec, dotProduct, hr]
      have h3 : (Pi.single x (1 : ℝ) ⬝ᵥ (A *ᵥ Pi.single x 1)) = A x x := by
        simp [single_dotProduct, Matrix.mulVec_single]
      simp only [matrixForm, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
        add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul, h1, h2, h3] at hu
      nlinarith
  · rintro ⟨hoff, hrow⟩ u
    rw [matrixForm_eq_form hA, matrixForm_eq_form hA]
    refine form_unitContraction_le (fun _ => zero_le_one) (fun x y hxy => ?_) (fun x => ?_) u
    · simpa using hoff x y hxy
    · simp [killingRate, hrow x]

/-- **Beurling–Deny on `ℝⁿ`: unit-contractive forms come from sub-Markovian generators.** For a
symmetric matrix `A` on a finite set, the unit contraction operates on `u ⬝ A u` if and only if
there is a symmetric sub-Markovian generator `Q` (nonnegative off-diagonal entries, nonpositive
row sums) with `u ⬝ A v = E_Q(u, v)` for all `u, v`, where `E_Q` is the form (1.2.27) with
counting measure (Fukushima, Oshima and Takeda, *Dirichlet Forms and Symmetric Markov
Processes*, 2nd ed., 2011, §1.1 and Example 1.2.5); one can take `Q = -A`. -/
theorem unitContraction_le_iff_exists_generator {A : Matrix S S ℝ}
    (hA : A.IsSymm) :
    (∀ u : S → ℝ, matrixForm A (unitContraction u) (unitContraction u) ≤ matrixForm A u u) ↔
      ∃ Q : Matrix S S ℝ, Q.IsSymm ∧ (∀ x y, x ≠ y → 0 ≤ Q x y) ∧ (∀ x, ∑ y, Q x y ≤ 0) ∧
        ∀ u v, matrixForm A u v = form 1 Q u v := by
  classical
  rw [unitContraction_le_iff hA]
  constructor
  · rintro ⟨hoff, hrow⟩
    refine ⟨-A, ?_, fun x y hxy => ?_, fun x => ?_, matrixForm_eq_form hA⟩
    · rw [Matrix.IsSymm, Matrix.transpose_neg, hA.eq]
    · simpa using hoff x y hxy
    · simpa [Finset.sum_neg_distrib] using hrow x
  · rintro ⟨Q, hQs, hQoff, hQrow, hform⟩
    -- The form determines the matrix: `A = -Q`.
    have hAQ : ∀ x y, A x y = -Q x y := by
      have hrev : IsDetailedBalance (1 : S → ℝ) Q := fun i j => by
        simp only [Pi.one_apply, one_mul]; exact (hQs.apply i j).symm
      intro x y
      have h := hform (Pi.single x 1) (Pi.single y 1)
      rw [form_eq_neg_sum_mul_mulVec hrev] at h
      simpa [matrixForm, single_dotProduct, Matrix.mulVec_single, Pi.single_apply] using h
    refine ⟨fun x y hxy => ?_, fun x => ?_⟩
    · rw [hAQ]; linarith [hQoff x y hxy]
    · simp only [hAQ, Finset.sum_neg_distrib]; linarith [hQrow x]

end MathlibExt.Probability.DirichletForm
