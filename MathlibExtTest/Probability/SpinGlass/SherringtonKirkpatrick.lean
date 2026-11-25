/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.SpinGlass.SherringtonKirkpatrick

/-!
# Tests for the Sherrington–Kirkpatrick model and the Parisi functional

Two checks of the definitions.

* A `β = 0` sanity check: the couplings disappear, the free energy is `log 2 + log cosh h` for
  every `N ≥ 1`, and the Parisi functional takes the same value for every choice of parameters,
  as the Parisi formula requires in this degenerate case. It checks the `log 2 + log cosh h`
  skeleton and the recursion, but not the `1/√N` factor or `ξ`, which vanish at `β = 0`.
* A covariance check, which pins both: `H_N(σ) = ∑_{i,j} g_{ij} c_{ij}(σ)` is linear in the
  couplings, and for every pair of configurations
  `∑_{i,j} c_{ij}(σ¹) c_{ij}(σ²) = N ξ(R_{1,2}) - β² / 2` with `ξ = skCovariance β` and the overlap
  `R_{1,2} = (1/N) ∑_i σ¹_i σ²_i`. For independent standard couplings the left-hand side is
  `E H_N(σ¹) H_N(σ²)`, which gives Talagrand's (1.3) with `c(N) = β² / (2N)`; that last
  probabilistic step is the usual covariance of a linear form in independent standard Gaussians
  and is not formalized here.
-/

@[expose] public section

namespace MathlibExtTest.Probability.SherringtonKirkpatrick

open MeasureTheory ProbabilityTheory Real MathlibExt.Probability.SherringtonKirkpatrick

instance (N : ℕ) : IsProbabilityMeasure (couplingLaw N) := by
  unfold couplingLaw; infer_instance

/-- At `β = 0`, `F_N = log 2 + log cosh h` for every `N ≥ 1`. -/
theorem freeEnergy_zero (h : ℝ) {N : ℕ} (hN : 0 < N) :
    freeEnergy 0 h N = log 2 + log (cosh h) := by
  have hsum : ∀ g : Fin N → Fin N → ℝ,
      (∑ σ : Fin N → Bool, exp (hamiltonian 0 N g σ + h * ∑ i, spin (σ i))) =
        (2 * cosh h) ^ N := by
    intro g
    have h1 : ∀ σ : Fin N → Bool, exp (hamiltonian 0 N g σ + h * ∑ i, spin (σ i)) =
        ∏ i, exp (h * spin (σ i)) := fun σ => by
      rw [hamiltonian, zero_div, neg_zero, zero_mul, zero_add, Finset.mul_sum, Real.exp_sum]
    simp_rw [h1]
    rw [← Fintype.prod_sum (fun (_ : Fin N) (b : Bool) => exp (h * spin b))]
    simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
      Finset.sum_insert, Finset.sum_singleton, spin, ite_true, Bool.false_eq_true, ite_false,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [cosh_eq]
    congr 1
    ring_nf
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [freeEnergy]
  simp_rw [hsum]
  rw [integral_const, probReal_univ, one_smul, log_pow, log_mul two_ne_zero (cosh_pos h).ne']
  field_simp

theorem skCovariance_zero : skCovariance 0 = fun _ => 0 := by
  funext x; simp [skCovariance]

theorem deriv_skCovariance_zero : deriv (skCovariance 0) = fun _ => 0 := by
  rw [skCovariance_zero]; funext x; simp

/-- At `β = 0` the Parisi recursion is constant: every level is `log cosh`. -/
theorem parisiRecursion_zero (k : ℕ) (m q : ℕ → ℝ) (j : ℕ) :
    parisiRecursion (fun _ => 0) k m q j = fun y => log (cosh y) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext y
    simp only [parisiRecursion, ih, sub_self, Real.toNNReal_zero, gaussianReal_zero_var,
      parisiStep]
    split_ifs with hm
    · simp
    · rw [integral_dirac, add_zero, log_exp]
      field_simp

/-- At `β = 0` the Parisi functional equals `log 2 + log cosh h` for all parameters. -/
theorem parisiFunctional_zero (h : ℝ) (k : ℕ) (m q : ℕ → ℝ) :
    parisiFunctional (skCovariance 0) h k m q = log 2 + log (cosh h) := by
  rw [parisiFunctional, deriv_skCovariance_zero, parisiRecursion_zero, skCovariance_zero]
  simp

/-- The Parisi formula holds at `β = 0` (the theorem itself assumes `β > 0`). -/
example (h : ℝ) {N : ℕ} (hN : 0 < N) :
    freeEnergy 0 h N = parisiFunctional (skCovariance 0) h 1 (fun _ => 0) (fun _ => 0) := by
  rw [freeEnergy_zero h hN, parisiFunctional_zero]

/-! ### Covariance check -/

/-- The coefficient of `g_{ij}` in `H_N(σ)`. -/
noncomputable def coeff (β : ℝ) (N : ℕ) (σ : Fin N → Bool) (i j : Fin N) : ℝ :=
  if i < j then -(β / Real.sqrt N) * (spin (σ i) * spin (σ j)) else 0

theorem hamiltonian_eq_sum_coeff (β : ℝ) (N : ℕ) (g : Fin N → Fin N → ℝ) (σ : Fin N → Bool) :
    hamiltonian β N g σ = ∑ i, ∑ j, g i j * coeff β N σ i j := by
  rw [hamiltonian, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : i < j <;> simp [coeff, h]; ring

theorem spin_mul_self (b : Bool) : spin b * spin b = 1 := by cases b <;> norm_num [spin]

/-- `∑_{i<j} a_i a_j = ((∑ a)² - ∑ a²) / 2`. -/
theorem sum_lt_mul_eq {N : ℕ} (a : Fin N → ℝ) :
    ∑ i, ∑ j, (if i < j then a i * a j else 0) = ((∑ i, a i) ^ 2 - ∑ i, a i ^ 2) / 2 := by
  have hsym : ∑ i, ∑ j, (if i < j then a i * a j else 0) =
      ∑ i, ∑ j, (if j < i then a i * a j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j < i <;> simp [h, mul_comm]
  have hsplit : ∀ i j : Fin N, a i * a j = (if i < j then a i * a j else 0) +
      (if j < i then a i * a j else 0) + (if i = j then a i * a j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · subst h; simp
    · simp [h, h.ne', not_lt.mpr h.le]
  have hsq : (∑ i, a i) ^ 2 = ∑ i, ∑ j, a i * a j := by rw [sq, Finset.sum_mul_sum]
  have hdiag : ∑ i, ∑ j, (if i = j then a i * a j else 0) = ∑ i, a i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq]; simp [sq]
  have htot : ∑ i, ∑ j, a i * a j = 2 * ∑ i, ∑ j, (if i < j then a i * a j else 0) +
      ∑ i, a i ^ 2 := by
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsplit i j, ← hdiag]
    simp only [Finset.sum_add_distrib]
    rw [← hsym]; ring
  rw [hsq, htot]; ring

/-- **The SK covariance.** For all configurations `σ¹, σ²`,
`∑_{i,j} c_{ij}(σ¹) c_{ij}(σ²) = N ξ(R_{1,2}) - β² / 2`, with `ξ = skCovariance β` and
`R_{1,2} = (1/N) ∑_i σ¹_i σ²_i` (Talagrand, *The Parisi formula*, (1.3)–(1.4)). -/
theorem sum_coeff_mul_coeff (β : ℝ) {N : ℕ} (hN : 0 < N) (σ₁ σ₂ : Fin N → Bool) :
    ∑ i, ∑ j, coeff β N σ₁ i j * coeff β N σ₂ i j =
      N * skCovariance β ((1 / N) * ∑ i, spin (σ₁ i) * spin (σ₂ i)) - β ^ 2 / 2 := by
  set a : Fin N → ℝ := fun i => spin (σ₁ i) * spin (σ₂ i)
  have ha2 : ∀ i, a i ^ 2 = 1 := fun i => by
    simp only [a]
    calc (spin (σ₁ i) * spin (σ₂ i)) ^ 2 = (spin (σ₁ i) * spin (σ₁ i)) *
          (spin (σ₂ i) * spin (σ₂ i)) := by ring
      _ = 1 := by rw [spin_mul_self, spin_mul_self, one_mul]
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hsqrt : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN'.le
  have hterm : ∀ i j, coeff β N σ₁ i j * coeff β N σ₂ i j =
      β ^ 2 / N * (if i < j then a i * a j else 0) := by
    intro i j
    by_cases h : i < j
    · simp only [coeff, h, ite_true, a]
      have : -(β / Real.sqrt N) * -(β / Real.sqrt N) = β ^ 2 / N := by
        rw [neg_mul_neg, ← sq, div_pow, hsqrt]
      calc -(β / Real.sqrt N) * (spin (σ₁ i) * spin (σ₁ j)) *
            (-(β / Real.sqrt N) * (spin (σ₂ i) * spin (σ₂ j)))
          = (-(β / Real.sqrt N) * -(β / Real.sqrt N)) *
            (spin (σ₁ i) * spin (σ₂ i) * (spin (σ₁ j) * spin (σ₂ j))) := by ring
        _ = _ := by rw [this]
    · simp [coeff, h]
  simp_rw [hterm, ← Finset.mul_sum]
  rw [sum_lt_mul_eq, Finset.sum_congr rfl fun i _ => ha2 i]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    skCovariance, a]
  field_simp

end MathlibExtTest.Probability.SherringtonKirkpatrick
