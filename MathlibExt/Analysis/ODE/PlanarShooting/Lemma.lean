/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The unstable branch of the logistic traveling-wave ODE

A traveling wave `u(x, t) = U(x - c t)` of the Fisher–KPP equation
`∂u/∂t = D ∂²u/∂x² + r u (1 - u)` has profile equation `D U'' + c U' + r U (1 - U) = 0`
(`MathlibExt.Biology.Dynamics.FisherKPP.IsWaveProfile`). In the phase plane `(U, U')` the
equilibrium `(1, 0)` is a saddle: the linearization `D w'' + c w' - r w = 0` of `w = 1 - U` has
eigenvalues `stableRate D r c < 0 < unstableRate D r c` for every speed `c` (`D, r > 0`). The
phase-plane proof of front existence (Murray, §13.2) starts from the branch of the unstable
manifold of `(1, 0)` that leaves into the quadrant `{U < 1, U' < 0}`. This file constructs that
branch and proves its properties; it does not define fronts and does not assume a
heteroclinic connection.

## Construction

Write `λ = unstableRate D r c` and `x = e^{λ z} / 4`. We look for `w = 1 - U = ∑ₙ aₙ xⁿ`. The
profile equation becomes `(n - 1) (D λ² n + r) aₙ = -r ∑_{i + j = n} aᵢ aⱼ` with `a₀ = 0` and
`a₁ = 1` (`branchCoeff`, `branchCoeff_rec`). The factorization
`D λ² n² + c λ n - r = (n - 1) (D λ² n + r)` comes from `D λ² + c λ - r = 0`, and it gives
`|aₙ| ≤ 1` by induction (`abs_branchCoeff_le_one`). The series therefore converges for
`|x| < 1`, and termwise differentiation (`hasDerivAt_branchSeries`) plus the Cauchy product
(`branchSeries_ode`) give an exact solution on the half-line `z < 0`. This is the
parameterization method for a one-dimensional unstable manifold of a polynomial vector field
(Cabré–Fontich–de la Llave), made explicit for the logistic nonlinearity.

## Main results

* `hasDerivAt_branch`, `hasDerivAt_branchDeriv`: `(branch, branchDeriv)` solves the profile
  equation on `z < 0`, in the same form as `IsWaveProfile`.
* `branch_mem_quadrant`: **orientation**: for `z < 0`, `0 < U < 1` and `U' < 0`.
* `tendsto_branch_atBot`, `tendsto_branchDeriv_atBot`: `(U, U') → (1, 0)` as `z → -∞`.
* `tendsto_one_sub_branch_div_exp`, `tendsto_branchDeriv_div`: the branch leaves at rate
  `e^{λ z}`, tangent to the unstable eigenvector: `U' / (U - 1) → λ`.
* `exists_unstableBranch`: the packaged statement.

The branch exists for every speed `c`; the speed threshold `c ≥ 2 √(r D)` enters only in the
later trapping-region argument, which also continues the branch past `z = 0`.

## Existing contracts audited

`WantedExt/Dynamics/StableUnstableManifoldsWanted.lean` (set-level Hadamard–Perron) concerns
iterates of a `C¹` map on `ℝⁿ`. It gives neither a flow-invariant curve, nor tangency, nor a
choice of branch, so it cannot supply this lemma even once proved. It is weaker still: its
conclusion `Ws ∩ Wu = {x₀}` also holds when `Wu = {x₀}`, so it does not even promise a
nontrivial unstable set.
`WantedExt/Analysis/ODE/LinearizedInstabilityWanted.lean` only asserts that some nearby
solution segment escapes. Neither contract is used or modified here.

The downstream consumer is `MathlibExt.Biology.Dynamics.FisherKPP.exists_isFront_of_le` in
`WantedExt/Biology/Dynamics/FisherKPPWanted.lean`. Its docstring has the unstable branch enter
the triangle `{0 ≤ U ≤ 1, -μ U ≤ U' ≤ 0}` with `μ = c / (2 D)`. This file proves only the
quadrant property `0 < U < 1`, `U' < 0`; entry into the triangle is left to the
trapping-region step.

## References

* J. D. Murray, *Mathematical Biology I: An Introduction*, 3rd ed., Springer, 2002, §13.2.
* A. Kolmogorov, I. Petrovsky and N. Piskunov, *Étude de l'équation de la diffusion avec
  croissance de la quantité de matière et son application à un problème biologique*, Bull.
  Univ. État Moscou Sér. Int. A 1 (1937), 1–26.
* X. Cabré, E. Fontich and R. de la Llave, *The parameterization method for invariant manifolds
  I: manifolds associated to non-resonant subspaces*, Indiana Univ. Math. J. 52 (2003),
  283–328.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Analysis.ODE.PlanarShooting

open Real Filter Topology Finset

/-- Coefficients of the unstable branch: `branchCoeff κ ρ 0 = 0`, `branchCoeff κ ρ 1 = 1` and,
for `n ≥ 2`, `(n - 1) (κ n + ρ) aₙ = -ρ ∑_{i + j = n, i, j ≥ 1} aᵢ aⱼ`. -/
noncomputable def branchCoeff (κ ρ : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | n + 2 => -ρ / ((n + 1) * (κ * (n + 2) + ρ)) *
      ∑ k : Fin (n + 1), branchCoeff κ ρ (k + 1) * branchCoeff κ ρ (n + 1 - k)
decreasing_by all_goals (have := k.isLt; omega)

/-- `a₀ = 0`. -/
@[simp] lemma branchCoeff_zero (κ ρ : ℝ) : branchCoeff κ ρ 0 = 0 := by simp [branchCoeff]

/-- `a₁ = 1`. -/
@[simp] lemma branchCoeff_one (κ ρ : ℝ) : branchCoeff κ ρ 1 = 1 := by simp [branchCoeff]

/-- The coefficients are bounded by `1` when `κ ≥ 0` and `ρ > 0`. -/
theorem abs_branchCoeff_le_one {κ ρ : ℝ} (hκ : 0 ≤ κ) (hρ : 0 < ρ) (n : ℕ) :
    |branchCoeff κ ρ n| ≤ 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | 1 => simp
    | n + 2 =>
      have hsum : |∑ k : Fin (n + 1), branchCoeff κ ρ (k + 1) * branchCoeff κ ρ (n + 1 - k)|
          ≤ n + 1 := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        have : ∀ k : Fin (n + 1),
            |branchCoeff κ ρ (k + 1) * branchCoeff κ ρ (n + 1 - k)| ≤ 1 := fun k => by
          rw [abs_mul]
          have h1 := ih (k + 1) (by omega)
          have h2 := ih (n + 1 - k) (by omega)
          nlinarith [abs_nonneg (branchCoeff κ ρ (k + 1)),
            abs_nonneg (branchCoeff κ ρ (n + 1 - k))]
        refine (Finset.sum_le_sum fun k _ => this k).trans ?_
        simp
      have hden : 0 < ((n : ℝ) + 1) * (κ * (n + 2) + ρ) := by positivity
      rw [branchCoeff, abs_mul, abs_div, abs_neg, abs_of_pos hρ, abs_of_pos hden]
      rw [div_mul_eq_mul_div, div_le_one hden]
      calc ρ * |∑ k : Fin (n + 1), branchCoeff κ ρ (k + 1) * branchCoeff κ ρ (n + 1 - k)|
          ≤ ρ * (n + 1) := by gcongr
        _ ≤ ((n : ℝ) + 1) * (κ * (n + 2) + ρ) := by nlinarith [mul_nonneg hκ (by positivity :
            (0 : ℝ) ≤ ((n : ℝ) + 1) * (n + 2))]

/-- The recursion in Cauchy-product form, valid for every `n`:
`(n - 1) (κ n + ρ) aₙ = -ρ ∑_{i + j = n} aᵢ aⱼ`. -/
theorem branchCoeff_rec {κ ρ : ℝ} (hκ : 0 ≤ κ) (hρ : 0 < ρ) (n : ℕ) :
    ((n : ℝ) - 1) * (κ * n + ρ) * branchCoeff κ ρ n =
      -ρ * ∑ p ∈ antidiagonal n, branchCoeff κ ρ p.1 * branchCoeff κ ρ p.2 := by
  match n with
  | 0 => simp
  | 1 => simp [Finset.Nat.antidiagonal_succ]
  | n + 2 =>
    have hden : 0 < ((n : ℝ) + 1) * (κ * (n + 2) + ρ) := by positivity
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
      Finset.sum_range_succ', ← Fin.sum_univ_eq_sum_range
        (fun k => branchCoeff κ ρ (k + 1) * branchCoeff κ ρ (n + 2 - (k + 1)))]
    have : ∀ k : Fin (n + 1), n + 2 - (k + 1 : ℕ) = n + 1 - k := fun k => by omega
    simp only [this, branchCoeff_zero, mul_zero, zero_mul, add_zero, Nat.sub_self, Nat.sub_zero]
    rw [branchCoeff]
    push_cast
    field_simp
    ring

/-- The power series `∑ₙ nᵐ aₙ xⁿ` built on `branchCoeff κ ρ`; `m = 0, 1, 2` give the branch
`w = 1 - U` and (up to powers of the rate) its first two derivatives in `z` when
`x = θ e^{λ z}`. -/
noncomputable def branchSeries (κ ρ : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  ∑' n, branchCoeff κ ρ n * (n : ℝ) ^ m * x ^ n

section Series

variable {κ ρ : ℝ}

/-- Absolute summability of `∑ nᵐ aₙ xⁿ` for `|x| < 1`. -/
lemma summable_norm_branchTerm (hκ : 0 ≤ κ) (hρ : 0 < ρ) (m : ℕ) {x : ℝ} (hx : |x| < 1) :
    Summable fun n : ℕ => ‖branchCoeff κ ρ n * (n : ℝ) ^ m * x ^ n‖ := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_pow_mul_geometric_of_norm_lt_one m (r := |x|) (by simpa using hx)))
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_pow, Nat.abs_cast]
  have := abs_branchCoeff_le_one hκ hρ n
  have h0 : 0 ≤ (n : ℝ) ^ m * |x| ^ n := by positivity
  nlinarith [abs_nonneg (branchCoeff κ ρ n)]

/-- Termwise differentiation along `x = θ e^{λ z}` on the half-line `z < 0`:
`d/dz ∑ nᵐ aₙ xⁿ = λ ∑ nᵐ⁺¹ aₙ xⁿ`. -/
theorem hasDerivAt_branchSeries (hκ : 0 ≤ κ) (hρ : 0 < ρ) (m : ℕ) {θ l : ℝ} (hθ : 0 ≤ θ)
    (hθ1 : θ < 1) (hl : 0 ≤ l) {z : ℝ} (hz : z < 0) :
    HasDerivAt (fun z => branchSeries κ ρ m (θ * exp (l * z)))
      (l * branchSeries κ ρ (m + 1) (θ * exp (l * z))) z := by
  have hX : ∀ y : ℝ, y < 0 → 0 ≤ θ * exp (l * y) ∧ θ * exp (l * y) ≤ θ := fun y hy =>
    ⟨by positivity, mul_le_of_le_one_right hθ (exp_le_one_iff.2 (by nlinarith))⟩
  have hterm : ∀ (n : ℕ) (y : ℝ), HasDerivAt
      (fun z => branchCoeff κ ρ n * (n : ℝ) ^ m * (θ * exp (l * z)) ^ n)
      (l * (branchCoeff κ ρ n * (n : ℝ) ^ (m + 1) * (θ * exp (l * y)) ^ n)) y := fun n y => by
    have h1 : HasDerivAt (fun z => θ * exp (l * z)) (θ * (exp (l * y) * l)) y := by
      simpa using ((hasDerivAt_id y).const_mul l).exp.const_mul θ
    convert (h1.pow n).const_mul (branchCoeff κ ρ n * (n : ℝ) ^ m) using 1
    rcases n with _ | n
    · simp
    · simp only [Nat.add_sub_cancel]; push_cast; ring
  have hsum := hasDerivAt_tsum_of_isPreconnected
    (u := fun n : ℕ => l * ((n : ℝ) ^ (m + 1) * θ ^ n))
    (g := fun n z => branchCoeff κ ρ n * (n : ℝ) ^ m * (θ * exp (l * z)) ^ n)
    (g' := fun n y => l * (branchCoeff κ ρ n * (n : ℝ) ^ (m + 1) * (θ * exp (l * y)) ^ n))
    (t := Set.Iio 0) (y₀ := z)
    ((summable_pow_mul_geometric_of_norm_lt_one (m + 1)
      (by rwa [Real.norm_eq_abs, abs_of_nonneg hθ])).mul_left l)
    isOpen_Iio isPreconnected_Iio (fun n y _ => hterm n y)
    (fun n y hy => by
      obtain ⟨h0, h1⟩ := hX y hy
      have hc := abs_branchCoeff_le_one hκ hρ n
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hl, abs_mul, abs_mul, abs_pow, abs_pow,
        Nat.abs_cast, abs_of_nonneg h0]
      refine mul_le_mul_of_nonneg_left ?_ hl
      calc |branchCoeff κ ρ n| * (n : ℝ) ^ (m + 1) * (θ * exp (l * y)) ^ n
          ≤ 1 * (n : ℝ) ^ (m + 1) * (θ * exp (l * y)) ^ n := by gcongr
        _ ≤ (n : ℝ) ^ (m + 1) * θ ^ n := by rw [one_mul]; gcongr)
    hz ((summable_norm_branchTerm hκ hρ m (by
      rw [abs_of_nonneg (hX z hz).1]; exact (hX z hz).2.trans_lt hθ1)).of_norm) hz
  simpa [branchSeries, tsum_mul_left] using hsum

/-- The series solves the (rescaled) logistic profile equation:
`κ S₂ + (ρ - κ) S₁ - ρ S₀ = -ρ S₀²` for `|x| < 1`, where `Sₘ = branchSeries κ ρ m x`. -/
theorem branchSeries_ode (hκ : 0 ≤ κ) (hρ : 0 < ρ) {x : ℝ} (hx : |x| < 1) :
    κ * branchSeries κ ρ 2 x + (ρ - κ) * branchSeries κ ρ 1 x - ρ * branchSeries κ ρ 0 x =
      -ρ * branchSeries κ ρ 0 x ^ 2 := by
  set f : ℕ → ℝ := fun n => branchCoeff κ ρ n * (n : ℝ) ^ 0 * x ^ n with hf
  have hs := fun m => summable_norm_branchTerm hκ hρ m hx
  have hL := ((((hs 2).of_norm.hasSum.mul_left κ).add ((hs 1).of_norm.hasSum.mul_left
    (ρ - κ))).sub ((hs 0).of_norm.hasSum.mul_left ρ))
  have hC : HasSum (fun n => ∑ p ∈ antidiagonal n, f p.1 * f p.2) ((∑' n, f n) * ∑' n, f n) := by
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (hs 0) (hs 0)]
    exact (summable_norm_sum_mul_antidiagonal_of_summable_norm (hs 0) (hs 0)).of_norm.hasSum
  have hR := hC.mul_left (-ρ)
  rw [branchSeries, branchSeries, branchSeries, sq]
  refine hL.unique (hR.congr_fun fun n => ?_)
  have hrec := branchCoeff_rec hκ hρ n
  have hanti : ∑ p ∈ antidiagonal n, f p.1 * f p.2 =
      (∑ p ∈ antidiagonal n, branchCoeff κ ρ p.1 * branchCoeff κ ρ p.2) * x ^ n := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    simp only [hf, ← hp, pow_add, pow_zero, mul_one]
    ring
  rw [hanti]
  linear_combination x ^ n * hrec

/-- Near the equilibrium the series is its linear term plus `O(x²)`:
`|Sₘ(x) - x| ≤ x² ∑ₙ (n + 2)ᵐ 4⁻ⁿ` for `0 ≤ x ≤ 1/4`. -/
theorem abs_branchSeries_sub_le (hκ : 0 ≤ κ) (hρ : 0 < ρ) (m : ℕ) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ 1 / 4) :
    |branchSeries κ ρ m x - x| ≤ x ^ 2 * ∑' n : ℕ, ((n : ℝ) + 2) ^ m * (1 / 4 : ℝ) ^ n := by
  have hx1 : |x| < 1 := by rw [abs_of_nonneg hx0]; linarith
  have hs := summable_norm_branchTerm hκ hρ m hx1
  have hs2 : Summable fun n : ℕ => ‖branchCoeff κ ρ (n + 2) * ((n + 2 : ℕ) : ℝ) ^ m *
      x ^ (n + 2)‖ := (summable_nat_add_iff 2).2 hs
  have hg : Summable fun n : ℕ => ((n : ℝ) + 2) ^ m * (1 / 4 : ℝ) ^ n := by
    have h := (summable_nat_add_iff 2).2
      (summable_pow_mul_geometric_of_norm_lt_one m (r := (1 / 4 : ℝ)) (by norm_num))
    refine (h.mul_left 16).congr fun n => ?_
    push_cast
    ring
  rw [branchSeries, hs.of_norm.tsum_eq_zero_add,
    ((summable_nat_add_iff 1).2 hs.of_norm).tsum_eq_zero_add]
  simp only [branchCoeff_zero, zero_mul, zero_add, Nat.cast_one, one_pow, mul_one,
    branchCoeff_one, pow_one, one_mul, add_sub_cancel_left]
  refine (norm_tsum_le_tsum_norm hs2).trans ?_
  rw [← tsum_mul_left]
  refine hs2.tsum_le_tsum (fun n => ?_) (hg.mul_left _)
  have hc := abs_branchCoeff_le_one hκ hρ (n + 2)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_pow, abs_of_nonneg hx0]
  push_cast
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 2)]
  have h1 : x ^ (n + 2) ≤ x ^ 2 * (1 / 4 : ℝ) ^ n := by
    rw [pow_add, mul_comm]; gcongr
  calc |branchCoeff κ ρ (n + 2)| * ((n : ℝ) + 2) ^ m * x ^ (n + 2)
      ≤ 1 * ((n : ℝ) + 2) ^ m * (x ^ 2 * (1 / 4 : ℝ) ^ n) := by gcongr
    _ = _ := by ring

private lemma tsum_branchConst_zero : ∑' n : ℕ, ((n : ℝ) + 2) ^ 0 * (1 / 4 : ℝ) ^ n = 4 / 3 := by
  simp only [pow_zero, one_mul]
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

private lemma tsum_branchConst_one : ∑' n : ℕ, ((n : ℝ) + 2) ^ 1 * (1 / 4 : ℝ) ^ n = 28 / 9 := by
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1 / 4 : ℝ)) (by norm_num)
  have h0 := summable_geometric_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
  simp only [pow_one] at h1 ⊢
  simp_rw [add_mul]
  rw [h1.tsum_add (h0.mul_left 2), tsum_mul_left,
    tsum_coe_mul_geometric_of_norm_lt_one (by norm_num),
    tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

end Series

section Logistic

variable {D r c : ℝ}

/-- The unstable eigenvalue `λ₊ = (-c + √(c² + 4 r D)) / (2 D)` of the linearization
`D w'' + c w' - r w = 0` of the logistic profile equation at the saddle `U = 1`. -/
noncomputable def unstableRate (D r c : ℝ) : ℝ := (-c + √(c ^ 2 + 4 * r * D)) / (2 * D)

/-- The stable eigenvalue `λ₋ = (-c - √(c² + 4 r D)) / (2 D)` at the saddle `U = 1`. -/
noncomputable def stableRate (D r c : ℝ) : ℝ := (-c - √(c ^ 2 + 4 * r * D)) / (2 * D)

private lemma sqrt_disc_gt (hD : 0 < D) (hr : 0 < r) (c : ℝ) : |c| < √(c ^ 2 + 4 * r * D) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith [mul_pos hr hD])

/-- `λ₊ > 0`. -/
theorem unstableRate_pos (hD : 0 < D) (hr : 0 < r) (c : ℝ) : 0 < unstableRate D r c := by
  have := sqrt_disc_gt hD hr c
  unfold unstableRate
  exact div_pos (by linarith [le_abs_self c]) (by positivity)

/-- `λ₋ < 0`. -/
theorem stableRate_neg (hD : 0 < D) (hr : 0 < r) (c : ℝ) : stableRate D r c < 0 := by
  have := sqrt_disc_gt hD hr c
  unfold stableRate
  exact div_neg_of_neg_of_pos (by linarith [neg_abs_le c]) (by positivity)

/-- Both rates are roots of the characteristic polynomial `D λ² + c λ - r`: the equilibrium
`(U, U') = (1, 0)` is a saddle with eigenvalues `λ₋ < 0 < λ₊`. -/
theorem unstableRate_char (hD : 0 < D) (r c : ℝ) (hdisc : 0 ≤ c ^ 2 + 4 * r * D) :
    D * unstableRate D r c ^ 2 + c * unstableRate D r c - r = 0 := by
  have h := Real.sq_sqrt hdisc
  unfold unstableRate
  set s := √(c ^ 2 + 4 * r * D)
  rw [div_pow, mul_pow]
  field_simp
  linear_combination h

/-- `λ₋` is a root of `D λ² + c λ - r`. -/
theorem stableRate_char (hD : 0 < D) (r c : ℝ) (hdisc : 0 ≤ c ^ 2 + 4 * r * D) :
    D * stableRate D r c ^ 2 + c * stableRate D r c - r = 0 := by
  have h := Real.sq_sqrt hdisc
  unfold stableRate
  set s := √(c ^ 2 + 4 * r * D)
  rw [div_pow, mul_pow]
  field_simp
  linear_combination h

/-- The amplitude variable `x(z) = e^{λ₊ z} / 4` of the branch; `0 < x(z) < 1/4` for `z < 0`. -/
noncomputable def branchArg (D r c z : ℝ) : ℝ := 1 / 4 * exp (unstableRate D r c * z)

/-- **The unstable branch** of the logistic traveling-wave ODE `D U'' + c U' + r U (1 - U) = 0`
at the saddle `U = 1`: `U(z) = 1 - ∑ₙ aₙ x(z)ⁿ` with `x(z) = e^{λ₊ z} / 4`. -/
noncomputable def branch (D r c z : ℝ) : ℝ :=
  1 - branchSeries (D * unstableRate D r c ^ 2) r 0 (branchArg D r c z)

/-- The derivative of the unstable branch, `U'(z) = -λ₊ ∑ₙ n aₙ x(z)ⁿ`. -/
noncomputable def branchDeriv (D r c z : ℝ) : ℝ :=
  -(unstableRate D r c * branchSeries (D * unstableRate D r c ^ 2) r 1 (branchArg D r c z))

/-- `x(z) > 0`. -/
lemma branchArg_pos (D r c z : ℝ) : 0 < branchArg D r c z := by
  unfold branchArg; positivity

/-- `x(z) < 1/4` for `z < 0`. -/
lemma branchArg_lt (hD : 0 < D) (hr : 0 < r) (c : ℝ) {z : ℝ} (hz : z < 0) :
    branchArg D r c z < 1 / 4 := by
  have := unstableRate_pos hD hr c
  unfold branchArg
  have : exp (unstableRate D r c * z) < 1 := exp_lt_one_iff.2 (by nlinarith)
  linarith

/-- `x(z) → 0` as `z → -∞`. -/
lemma tendsto_branchArg (hD : 0 < D) (hr : 0 < r) (c : ℝ) :
    Tendsto (branchArg D r c) atBot (𝓝 0) := by
  have h := (tendsto_exp_atBot.comp
    (tendsto_id.const_mul_atBot (unstableRate_pos hD hr c))).const_mul (1 / 4 : ℝ)
  have h' : Tendsto (fun z => 1 / 4 * exp (unstableRate D r c * z)) atBot (𝓝 0) := by
    simpa [Function.comp_def] using h
  exact h'

/-- The branch solves `U' = branchDeriv` on `z < 0`. -/
theorem hasDerivAt_branch (hD : 0 < D) (hr : 0 < r) (c : ℝ) {z : ℝ} (hz : z < 0) :
    HasDerivAt (branch D r c) (branchDeriv D r c z) z := by
  have h := hasDerivAt_branchSeries (κ := D * unstableRate D r c ^ 2) (ρ := r) (by positivity) hr 0
    (θ := 1 / 4) (by norm_num) (by norm_num) (unstableRate_pos hD hr c).le hz
  exact h.const_sub 1

/-- The branch solves the logistic profile equation
`U'' = (-(c U') - r U (1 - U)) / D` on `z < 0` (the form used by `IsWaveProfile`). -/
theorem hasDerivAt_branchDeriv (hD : 0 < D) (hr : 0 < r) (c : ℝ) {z : ℝ} (hz : z < 0) :
    HasDerivAt (branchDeriv D r c)
      ((-(c * branchDeriv D r c z) - r * branch D r c z * (1 - branch D r c z)) / D) z := by
  have hl0 := unstableRate_pos hD hr c
  have hchar := unstableRate_char hD r c (by nlinarith [sq_nonneg c, mul_pos hr hD])
  have h := hasDerivAt_branchSeries (κ := D * unstableRate D r c ^ 2) (ρ := r) (by positivity)
    hr 1 (θ := 1 / 4) (by norm_num) (by norm_num) hl0.le hz
  have h2 : HasDerivAt (branchDeriv D r c) (-(unstableRate D r c * (unstableRate D r c *
      branchSeries (D * unstableRate D r c ^ 2) r 2 (branchArg D r c z)))) z :=
    (h.const_mul (unstableRate D r c)).neg
  have hx : |branchArg D r c z| < 1 := by
    rw [abs_of_pos (branchArg_pos D r c z)]; linarith [branchArg_lt hD hr c hz]
  have hode := branchSeries_ode (κ := D * unstableRate D r c ^ 2) (by positivity) hr hx
  convert h2 using 1
  rw [branchDeriv, branch]
  generalize branchSeries (D * unstableRate D r c ^ 2) r 0 (branchArg D r c z) = S0 at hode ⊢
  generalize branchSeries (D * unstableRate D r c ^ 2) r 1 (branchArg D r c z) = S1 at hode ⊢
  generalize branchSeries (D * unstableRate D r c ^ 2) r 2 (branchArg D r c z) = S2 at hode ⊢
  generalize unstableRate D r c = l at hode hchar ⊢
  field_simp
  linear_combination hode + S1 * hchar

/-- **Orientation into the invariant quadrant.** For `z < 0` the branch lies in
`{0 < U < 1, U' < 0}`. -/
theorem branch_mem_quadrant (hD : 0 < D) (hr : 0 < r) (c : ℝ) {z : ℝ} (hz : z < 0) :
    0 < branch D r c z ∧ branch D r c z < 1 ∧ branchDeriv D r c z < 0 := by
  have hκ : 0 ≤ D * unstableRate D r c ^ 2 := by positivity
  have hx0 := branchArg_pos D r c z
  have hx1 := branchArg_lt hD hr c hz
  have h0 := abs_branchSeries_sub_le hκ hr 0 hx0.le hx1.le
  have h1 := abs_branchSeries_sub_le hκ hr 1 hx0.le hx1.le
  rw [tsum_branchConst_zero] at h0
  rw [tsum_branchConst_one] at h1
  have hl := unstableRate_pos hD hr c
  set x := branchArg D r c z
  obtain ⟨h0a, h0b⟩ := abs_le.1 h0
  obtain ⟨h1a, -⟩ := abs_le.1 h1
  have hx2 : x ^ 2 ≤ x / 4 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [branch]; nlinarith
  · rw [branch]; nlinarith
  · rw [branchDeriv, neg_lt_zero]
    exact mul_pos hl (by nlinarith)

/-- `Sₘ(x(z)) / x(z) → 1` as `z → -∞`. -/
lemma tendsto_branchSeries_div (hD : 0 < D) (hr : 0 < r) (c : ℝ) (m : ℕ) :
    Tendsto (fun z => branchSeries (D * unstableRate D r c ^ 2) r m (branchArg D r c z) /
      branchArg D r c z) atBot (𝓝 1) := by
  have hκ : 0 ≤ D * unstableRate D r c ^ 2 := by positivity
  set K := ∑' n : ℕ, ((n : ℝ) + 2) ^ m * (1 / 4 : ℝ) ^ n
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa using (tendsto_branchArg hD hr c).const_mul K)
  filter_upwards [eventually_lt_atBot 0] with z hz
  have hx0 := branchArg_pos D r c z
  have h := abs_branchSeries_sub_le hκ hr m hx0.le (branchArg_lt hD hr c hz).le
  rw [Real.norm_eq_abs, div_sub_one hx0.ne', abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
  nlinarith

/-- `Sₘ(x(z)) → 0` as `z → -∞`. -/
lemma tendsto_branchSeries (hD : 0 < D) (hr : 0 < r) (c : ℝ) (m : ℕ) :
    Tendsto (fun z => branchSeries (D * unstableRate D r c ^ 2) r m (branchArg D r c z)) atBot
      (𝓝 0) := by
  have h := (tendsto_branchSeries_div hD hr c m).mul (tendsto_branchArg hD hr c)
  rw [one_mul] at h
  refine h.congr fun z => ?_
  field_simp [(branchArg_pos D r c z).ne']

/-- The branch converges to the saddle: `U → 1` at `-∞`. -/
theorem tendsto_branch_atBot (hD : 0 < D) (hr : 0 < r) (c : ℝ) :
    Tendsto (branch D r c) atBot (𝓝 1) := by
  have h := (tendsto_branchSeries hD hr c 0).const_sub 1
  rw [sub_zero] at h
  exact h

/-- The branch converges to the saddle: `U' → 0` at `-∞`. -/
theorem tendsto_branchDeriv_atBot (hD : 0 < D) (hr : 0 < r) (c : ℝ) :
    Tendsto (branchDeriv D r c) atBot (𝓝 0) := by
  have h := ((tendsto_branchSeries hD hr c 1).const_mul (unstableRate D r c)).neg
  rw [mul_zero, neg_zero] at h
  exact h

/-- Exponential rate of departure: `(1 - U(z)) e^{-λ₊ z} → 1/4` at `-∞`. -/
theorem tendsto_one_sub_branch_div_exp (hD : 0 < D) (hr : 0 < r) (c : ℝ) :
    Tendsto (fun z => (1 - branch D r c z) / exp (unstableRate D r c * z)) atBot
      (𝓝 (1 / 4)) := by
  have h := (tendsto_branchSeries_div hD hr c 0).const_mul (1 / 4 : ℝ)
  rw [mul_one] at h
  refine h.congr fun z => ?_
  simp only [branch, sub_sub_cancel, branchArg]
  field_simp

/-- **Tangency to the unstable eigendirection**: `U'(z) / (U(z) - 1) → λ₊` at `-∞`, i.e. the
branch leaves `(1, 0)` along the eigenvector `(1, λ₊)`, on the side `U < 1`, `U' < 0`. -/
theorem tendsto_branchDeriv_div (hD : 0 < D) (hr : 0 < r) (c : ℝ) :
    Tendsto (fun z => branchDeriv D r c z / (branch D r c z - 1)) atBot
      (𝓝 (unstableRate D r c)) := by
  have h := ((tendsto_branchSeries_div hD hr c 1).div (tendsto_branchSeries_div hD hr c 0)
    one_ne_zero).const_mul (unstableRate D r c)
  rw [div_one, mul_one] at h
  refine h.congr fun z => ?_
  have hx := (branchArg_pos D r c z).ne'
  simp only [Pi.div_apply, branch, branchDeriv, sub_sub_cancel_left]
  rw [neg_div_neg_eq, mul_div_assoc, div_div_div_cancel_right₀ hx]

/-- **The unstable branch of the logistic traveling-wave ODE.** For `D, r > 0` and every speed
`c` there is a solution `(U, U')` of `D U'' + c U' + r U (1 - U) = 0` on `z < 0`. It lies in
the quadrant `{0 < U < 1, U' < 0}`, tends to the saddle `(1, 0)` as `z → -∞`, and is tangent
there to the unstable eigendirection: `U' / (U - 1) → λ₊`. -/
theorem exists_unstableBranch (hD : 0 < D) (hr : 0 < r) (c : ℝ) :
    ∃ U U' : ℝ → ℝ,
      (∀ z < 0, HasDerivAt U (U' z) z ∧
        HasDerivAt U' ((-(c * U' z) - r * U z * (1 - U z)) / D) z) ∧
      (∀ z < 0, 0 < U z ∧ U z < 1 ∧ U' z < 0) ∧
      Tendsto U atBot (𝓝 1) ∧ Tendsto U' atBot (𝓝 0) ∧
      Tendsto (fun z => U' z / (U z - 1)) atBot (𝓝 (unstableRate D r c)) :=
  ⟨branch D r c, branchDeriv D r c,
    fun _ hz => ⟨hasDerivAt_branch hD hr c hz, hasDerivAt_branchDeriv hD hr c hz⟩,
    fun _ hz => branch_mem_quadrant hD hr c hz, tendsto_branch_atBot hD hr c,
    tendsto_branchDeriv_atBot hD hr c, tendsto_branchDeriv_div hD hr c⟩

end Logistic

end MathlibExt.Analysis.ODE.PlanarShooting
