/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Fourier coefficients on the Boolean cube

The cube is represented by `Fin n → Bool`, with `true` representing `1` and
`false` representing `-1`. Fourier coefficients use the uniform probability measure.

These definitions are extracted, with their meanings unchanged, from
`OpenConjectures.ComputerScience.InversePolynomialInfluenceThreshold.Statement`,
originally formalized from the MFO-RIMS Tandem Workshop report, Oberwolfach Reports
(2025), DOI 10.4171/owr/2025/9, source record `OWR-14299088-012`.
-/

@[expose] public section

namespace BooleanCube

open scoped BigOperators

/-- The Boolean cube `{-1, 1}^n`, represented by Boolean coordinates. -/
abbrev BoolCube (n : ℕ) : Type := Fin n → Bool

/-- The sign of a Boolean coordinate: `true = 1`, `false = -1`. -/
def cubeVal : Bool → ℝ
  | true => 1
  | false => -1

/-- The Fourier character `χ_S(x) = ∏_{i ∈ S} x_i`. -/
def cubeChi (n : ℕ) (S : Finset (Fin n)) (x : BoolCube n) : ℝ :=
  ∏ i ∈ S, cubeVal (x i)

/-- The normalized Fourier coefficient `f̂(S) = E_x[f(x) χ_S(x)]`. -/
noncomputable def boolFourierCoeff (n : ℕ) (f : BoolCube n → ℝ)
    (S : Finset (Fin n)) : ℝ :=
  (∑ x : BoolCube n, f x * cubeChi n S x) / (Fintype.card (BoolCube n) : ℝ)

/-- Fourier degree at most `d`: all coefficients on sets of size greater than `d` vanish.
This is the degree of the multilinear polynomial representing the function on the cube. -/
def MultilinearDegreeLE (n : ℕ) (f : BoolCube n → ℝ) (d : ℕ) : Prop :=
  ∀ S : Finset (Fin n), d < S.card → boolFourierCoeff n f S = 0

/-- A `true` coordinate represents the positive sign. -/
@[simp] theorem cubeVal_true : cubeVal true = 1 := rfl

/-- A `false` coordinate represents the negative sign. -/
@[simp] theorem cubeVal_false : cubeVal false = -1 := rfl

/-- Each coordinate sign has square one. -/
@[simp] theorem cubeVal_mul_self (b : Bool) : cubeVal b * cubeVal b = 1 := by
  cases b <;> simp

/-- The empty Fourier character is the constant one function. -/
@[simp] theorem cubeChi_empty (n : ℕ) (x : BoolCube n) : cubeChi n ∅ x = 1 := by
  simp [cubeChi]

/-- A singleton Fourier character is its coordinate sign. -/
@[simp] theorem cubeChi_singleton (n : ℕ) (i : Fin n) (x : BoolCube n) :
    cubeChi n {i} x = cubeVal (x i) := by
  simp [cubeChi]

/-- Every Fourier character has square one. -/
@[simp] theorem cubeChi_mul_self (n : ℕ) (S : Finset (Fin n)) (x : BoolCube n) :
    cubeChi n S x * cubeChi n S x = 1 := by
  simp only [cubeChi, ← Finset.prod_mul_distrib, cubeVal_mul_self, Finset.prod_const_one]

/-- The coefficient of the empty character is the uniform mean. -/
theorem boolFourierCoeff_empty (n : ℕ) (f : BoolCube n → ℝ) :
    boolFourierCoeff n f ∅ = (∑ x : BoolCube n, f x) / (Fintype.card (BoolCube n) : ℝ) := by
  simp [boolFourierCoeff]

/-- The identically zero function has zero Fourier coefficients. -/
@[simp] theorem boolFourierCoeff_zero (n : ℕ) (S : Finset (Fin n)) :
    boolFourierCoeff n (fun _ => 0) S = 0 := by
  simp [boolFourierCoeff]

/-- A Fourier character has normalized coefficient one at its own index. -/
@[simp] theorem boolFourierCoeff_cubeChi_self (n : ℕ) (S : Finset (Fin n)) :
    boolFourierCoeff n (cubeChi n S) S = 1 := by
  simp [boolFourierCoeff, Fintype.card_ne_zero]

/-- The mean of a constant function is that constant, including in dimension zero. -/
@[simp] theorem boolFourierCoeff_const_empty (n : ℕ) (c : ℝ) :
    boolFourierCoeff n (fun _ => c) ∅ = c := by
  simp [boolFourierCoeff, Fintype.card_ne_zero]

/-- The zero function has Fourier degree at most every natural number. -/
@[simp] theorem multilinearDegreeLE_zero (n d : ℕ) :
    MultilinearDegreeLE n (fun _ => 0) d := by
  intro S _
  simp

/-- Increasing the degree bound preserves the Fourier degree condition. -/
theorem MultilinearDegreeLE.mono {n d e : ℕ} {f : BoolCube n → ℝ}
    (h : MultilinearDegreeLE n f d) (hde : d ≤ e) : MultilinearDegreeLE n f e := by
  intro S hS
  exact h S (lt_of_le_of_lt hde hS)

/-- Every function on an `n`-dimensional cube has Fourier degree at most `n`. -/
theorem multilinearDegreeLE_of_dimension_le {n d : ℕ} (f : BoolCube n → ℝ)
    (hnd : n ≤ d) : MultilinearDegreeLE n f d := by
  intro S hS
  have hcard : S.card ≤ n := by
    simpa using Finset.card_le_univ S
  exact (Nat.not_lt_of_ge (hcard.trans hnd) hS).elim

/-- The Lagrange basis polynomial associated to a Boolean cube point. -/
noncomputable def cubeBasis {n : ℕ}
    (x : BoolCube n) : MvPolynomial (Fin n) ℝ :=
  ∏ i : Fin n,
    if x i then MvPolynomial.X i else 1 - MvPolynomial.X i

/-- The real multilinear extension of a Boolean function. For each cube point
`x`, the product is its Lagrange indicator: it is one at `x` and zero at every
other Boolean point. The sum is therefore the unique multilinear polynomial
agreeing with `f` on `{0,1}^n`. -/
noncomputable def multilinearExtension {n : ℕ}
    (f : BoolCube n → Bool) : MvPolynomial (Fin n) ℝ := by
  classical
  exact
  ∑ x : BoolCube n,
    MvPolynomial.C (if f x then (1 : ℝ) else 0) *
      cubeBasis x

/-- A cube basis polynomial evaluates to one at its point and zero at every
other Boolean point. -/
theorem eval_cubeBasis {n : ℕ} (x y : BoolCube n) :
    MvPolynomial.eval (fun i => if y i then (1 : ℝ) else 0) (cubeBasis x) =
      if x = y then 1 else 0 := by
  classical
  by_cases hxy : x = y
  · subst y
    simp only [cubeBasis, map_prod]
    apply Finset.prod_eq_one
    intro i _
    cases h : x i <;> simp [h]
  · simp only [cubeBasis, map_prod]
    rw [ite_eq_right hxy]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    cases hxi : x i <;> cases hyi : y i <;> simp_all

/-- The deterministic extension agrees with the Boolean function at every
cube point. -/
theorem eval_multilinearExtension {n : ℕ}
    (f : BoolCube n → Bool) (y : BoolCube n) :
    MvPolynomial.eval (fun i => if y i then (1 : ℝ) else 0)
      (multilinearExtension f) = if f y then 1 else 0 := by
  classical
  simp only [multilinearExtension, map_sum, map_mul, MvPolynomial.eval_C]
  simp_rw [eval_cubeBasis]
  simp

private theorem sum_cubeBasis (n : ℕ) :
    ∑ x : BoolCube n, cubeBasis x = (1 : MvPolynomial (Fin n) ℝ) := by
  classical
  have h := Finset.sum_prod_piFinset (R := MvPolynomial (Fin n) ℝ)
    (Finset.univ : Finset Bool)
    (fun i b => if b then MvPolynomial.X i else 1 - MvPolynomial.X i)
  rw [Fintype.piFinset_univ] at h
  simpa [cubeBasis] using h

private theorem sum_projection_cubeBasis {n : ℕ} (i : Fin n) :
    ∑ x : BoolCube n,
      (if x i then (1 : MvPolynomial (Fin n) ℝ) else 0) * cubeBasis x =
        MvPolynomial.X i := by
  classical
  let g : Fin n → Bool → MvPolynomial (Fin n) ℝ := fun j b =>
    if b then MvPolynomial.X j else if j = i then 0 else 1 - MvPolynomial.X j
  have h := Finset.sum_prod_piFinset (R := MvPolynomial (Fin n) ℝ)
    (Finset.univ : Finset Bool) g
  rw [Fintype.piFinset_univ] at h
  have hl : (∑ x : BoolCube n, ∏ j, g j (x j)) =
      ∑ x : BoolCube n,
        (if x i then (1 : MvPolynomial (Fin n) ℝ) else 0) * cubeBasis x := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hxi : x i
    · simp only [hxi, ite_true, one_mul, g, cubeBasis]
      apply Finset.prod_congr rfl
      intro j _
      by_cases hji : j = i <;> simp [hxi, hji]
    · simp [hxi, g, Finset.prod_eq_zero (Finset.mem_univ i)]
  rw [hl] at h
  calc
    _ = ∏ j : Fin n,
        (MvPolynomial.X j + if j = i then 0 else 1 - MvPolynomial.X j) := by
      simpa [g] using h
    _ = ∏ j : Fin n,
        if j = i then MvPolynomial.X i else (1 : MvPolynomial (Fin n) ℝ) := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j; simp
      · simp [hji]
    _ = MvPolynomial.X i := by simp

/-- Constant Boolean functions have constant multilinear extension. -/
theorem multilinearExtension_const {n : ℕ} (b : Bool) :
    multilinearExtension (n := n) (fun _ => b) =
      MvPolynomial.C (if b then (1 : ℝ) else 0) := by
  classical
  cases b
  · simp [multilinearExtension]
  · simp [multilinearExtension, sum_cubeBasis]

/-- A coordinate projection has extension `X i`. -/
theorem multilinearExtension_projection {n : ℕ} (i : Fin n) :
    multilinearExtension (fun x => x i) = MvPolynomial.X i := by
  classical
  rw [multilinearExtension]
  convert sum_projection_cubeBasis i using 1
  apply Finset.sum_congr rfl
  intro x _
  cases x i <;> simp

/-- The total degree of the unique real multilinear extension of `f`. -/
noncomputable def booleanDegree {n : ℕ}
    (f : BoolCube n → Bool) : ℕ :=
  (multilinearExtension f).totalDegree

/-- Constants have Boolean degree zero. -/
theorem booleanDegree_const {n : ℕ} (b : Bool) :
    booleanDegree (n := n) (fun _ => b) = 0 := by
  rw [booleanDegree, multilinearExtension_const]
  cases b <;> simp

/-- Coordinate projections have Boolean degree one. -/
theorem booleanDegree_projection {n : ℕ} (i : Fin n) :
    booleanDegree (fun x => x i) = 1 := by
  rw [booleanDegree, multilinearExtension_projection]
  simp

/-- The Boolean AND function on all coordinates. -/
def allTrueFunction {n : ℕ} (x : BoolCube n) : Bool :=
  decide (∀ i, x i = true)

private theorem sum_allTrue_cubeBasis (n : ℕ) :
    ∑ x : BoolCube n,
      (if allTrueFunction x then (1 : MvPolynomial (Fin n) ℝ) else 0) *
        cubeBasis x = ∏ i : Fin n, MvPolynomial.X i := by
  classical
  let g : Fin n → Bool → MvPolynomial (Fin n) ℝ := fun i b =>
    if b then MvPolynomial.X i else 0
  have h := Finset.sum_prod_piFinset (R := MvPolynomial (Fin n) ℝ)
    (Finset.univ : Finset Bool) g
  rw [Fintype.piFinset_univ] at h
  have hl : (∑ x : BoolCube n, ∏ i, g i (x i)) =
      ∑ x : BoolCube n,
        (if allTrueFunction x then (1 : MvPolynomial (Fin n) ℝ) else 0) *
          cubeBasis x := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : ∀ i, x i = true
    · simp [allTrueFunction, hx, g, cubeBasis]
    · simp only [allTrueFunction, decide_eq_true_eq, hx, ite_false, zero_mul]
      push Not at hx
      obtain ⟨i, hi⟩ := hx
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [g, hi]
  rw [hl] at h
  simpa [g] using h

/-- The all-true function has the product of all variables as its extension. -/
theorem multilinearExtension_allTrue (n : ℕ) :
    multilinearExtension (n := n) allTrueFunction =
      ∏ i : Fin n, MvPolynomial.X i := by
  classical
  rw [multilinearExtension]
  convert sum_allTrue_cubeBasis n using 1
  apply Finset.sum_congr rfl
  intro x _
  cases allTrueFunction x <;> simp

/-- The two-bit all-true function has degree two. -/
theorem booleanDegree_allTrue_two :
    booleanDegree (allTrueFunction (n := 2)) = 2 := by
  rw [booleanDegree, multilinearExtension_allTrue, Fin.prod_univ_two]
  simp [MvPolynomial.X, Finsupp.sum_add_index]

private theorem sum_ind_pow_mul_cubeChi_eq_zero {n : ℕ} (m : Fin n →₀ ℕ)
    (S : Finset (Fin n)) (hS : m.sum (fun _ e => e) < S.card) :
    (∑ x : BoolCube n,
      (∏ i, (if x i then (1 : ℝ) else 0) ^ m i) * cubeChi n S x) = 0 := by
  classical
  obtain ⟨i, hiS, hi0⟩ : ∃ i ∈ S, m i = 0 := by
    by_contra hcon
    push Not at hcon
    have hsub : S ⊆ m.support := by
      intro j hj
      exact Finsupp.mem_support_iff.mpr (hcon j hj)
    have hle : S.card ≤ m.sum (fun _ e => e) := by
      rw [Finsupp.sum]
      calc S.card = ∑ _j ∈ S, 1 := by simp
        _ ≤ ∑ j ∈ S, m j :=
            Finset.sum_le_sum fun j hj => Nat.one_le_iff_ne_zero.mpr (hcon j hj)
        _ ≤ ∑ j ∈ m.support, m j :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => Nat.zero_le _)
    exact (Nat.not_lt_of_ge hle) hS
  have hfac : (∑ x : BoolCube n,
        (∏ i, (if x i then (1 : ℝ) else 0) ^ m i) * cubeChi n S x) =
      ∏ i, ∑ b : Bool,
        ((if b then (1 : ℝ) else 0) ^ m i *
          (if i ∈ S then cubeVal b else 1)) := by
    have h := Finset.sum_prod_piFinset (R := ℝ) (Finset.univ : Finset Bool)
      (fun i b => (if b then (1 : ℝ) else 0) ^ m i *
        (if i ∈ S then cubeVal b else 1))
    rw [Fintype.piFinset_univ] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro x _
    have hchi : cubeChi n S x =
        ∏ i, (if i ∈ S then cubeVal (x i) else 1) := by
      simp [cubeChi, Finset.prod_ite_mem]
    rw [hchi, ← Finset.prod_mul_distrib]
  rw [hfac]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have hsum : (∑ b : Bool,
      ((if b then (1 : ℝ) else 0) ^ m i *
        (if i ∈ S then cubeVal b else 1))) = 0 := by
    have huniv : (Finset.univ : Finset Bool) = {false, true} := by decide
    rw [huniv, Finset.sum_pair (by decide : (false : Bool) ≠ true), hi0]
    simp [cubeVal, hiS]
  exact hsum

/-- The Fourier degree of the `0/1` indicator of a Boolean function is at most
its Boolean degree: Fourier coefficients above the degree of the multilinear
extension vanish. This connects `booleanDegree` to `MultilinearDegreeLE`. -/
theorem multilinearDegreeLE_indicator {n : ℕ} (f : BoolCube n → Bool) :
    MultilinearDegreeLE n (fun x => if f x then (1 : ℝ) else 0)
      (booleanDegree f) := by
  classical
  intro S hS
  rw [boolFourierCoeff, div_eq_zero_iff]
  left
  have hsum : (∑ x : BoolCube n,
        (if f x then (1 : ℝ) else 0) * cubeChi n S x) =
      ∑ m ∈ (multilinearExtension f).support,
        (multilinearExtension f).coeff m *
          (∑ x : BoolCube n,
            (∏ i, (if x i then (1 : ℝ) else 0) ^ m i) * cubeChi n S x) := by
    have hpt : ∀ x : BoolCube n,
        (if f x then (1 : ℝ) else 0) * cubeChi n S x =
          ∑ m ∈ (multilinearExtension f).support,
            ((multilinearExtension f).coeff m *
              ∏ i, (if x i then (1 : ℝ) else 0) ^ m i) * cubeChi n S x := by
      intro x
      rw [← eval_multilinearExtension f x, MvPolynomial.eval_eq',
        Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [mul_assoc]
  rw [hsum]
  apply Finset.sum_eq_zero
  intro m hm
  rw [sum_ind_pow_mul_cubeChi_eq_zero m S
    (lt_of_le_of_lt (MvPolynomial.le_totalDegree hm) hS)]
  simp

end BooleanCube
