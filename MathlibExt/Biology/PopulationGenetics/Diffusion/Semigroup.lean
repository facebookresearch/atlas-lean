/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.BlockCounting
public import MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisher
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# The Wright–Fisher diffusion semigroup via moment duality

In the neutral Wright–Fisher model with `M` gene copies, the allele count of the next generation
is `Bin(M, x)` when the current allele frequency is `x`. Acting on continuous functions of the
frequency, one generation is the Bernstein operator
`(wfStep M f)(x) = ∑_i f(i/M) C(M, i) x^i (1 - x)^(M - i)` (the expectation of `f` at the next
frequency, by `ProbabilityTheory.integral_binomial`; Mathlib's `bernsteinApproximation M f`),
and `t` generations are `wfStep M ^ t`. Each `wfStep M` is a positive linear contraction of
`C([0, 1], ℝ)` fixing `1`.

**Moment duality.** A sample of `n` genes has `k` distinct parents with probability
`wfLineageProb M n k = S(n, k) M_(k) / M^n` (Stirling numbers of the second kind, falling
factorial), so `E_x[(X₁)^n] = ∑_k wfLineageProb M n k · x^k` (`integral_binomial_div_pow`), and
after `m` generations the coefficients are the entries of the `m`-th power of the lineage-count
matrix `wfLineageMatrix` (`wfStep_pow_X_pow`).

**The limit semigroup.** With time in units of `M` generations, Kingman's theorem for the lineage
count (`tendsto_wfLineageMatrix_pow_floor`) gives `(wfLineageMatrix n M)^⌊tM⌋ → exp (t • G)`,
where `G = blockCountingGenerator n` is the rate matrix of the block-counting (pure-death)
process. We define `polySemigroup t` on polynomials by `X^n ↦ ∑_k exp (t • G) n k · X^k`
(`dualMomentPoly`); it is a group of linear maps (`polySemigroup_add`), using that the
block-counting transition matrices are lower triangular and consistent across truncation levels
(`KingmanBlockCounting.exp_smul_blockCountingGenerator_of_lt`,
`KingmanBlockCounting.exp_smul_blockCountingGenerator_castLE`). For every
polynomial `p` and `t ≥ 0`, `(wfStep M)^⌊tM⌋ p → polySemigroup t p` uniformly on `[0, 1]`.
Because the chain operators are contractions and polynomials are dense (Weierstrass),
`(wfStep M)^⌊tM⌋ f` converges uniformly for **every** continuous `f`; the limit defines
`wfSemigroup t`, a positive linear contraction of `C([0, 1], ℝ)` with `wfSemigroup t 1 = 1`, the
semigroup law for `s, t ≥ 0`, strong continuity at `0`, and generator
`(L p)(x) = x (1 - x) / 2 · p''(x)` (`generator 0`) on polynomials. These are the defining
properties of a Feller semigroup on `[0, 1]`, and `tendsto_wfStep_pow_floor` is the conclusion of
the Trotter–Kato approximation theorem in this concrete case, proved here directly from duality.

Not covered: the Wright–Fisher diffusion as a stochastic process (path space, weak convergence of
the rescaled chains), the full domain of the generator (only polynomial test functions are
treated; that they form a core is not proved),
and selection or mutation. For `t < 0`, `wfSemigroup t` is the identity because `⌊tM⌋₊ = 0`
(a junk value outside the domain `t ≥ 0`), whereas `polySemigroup t` is the algebraic inverse.

## Main results

* `wfStep`, `norm_wfStep_le`: one Wright–Fisher generation as a linear contraction.
* `sum_binomial_mul_div_pow`, `integral_binomial_div_pow`: one-generation moment duality.
* `wfStep_pow_X_pow`: moment duality for `m` generations.
* `polySemigroup`, `polySemigroup_zero`, `polySemigroup_add`, `polySemigroup_one`: the dual
  semigroup on polynomials.
* `tendsto_wfStep_pow_floor_toContinuousMapOn`: the chain converges on polynomials.
* `wfSemigroup`, `tendsto_wfStep_pow_floor`: the chain converges uniformly for every continuous
  test function, and the limit is the Wright–Fisher diffusion semigroup.
* `wfSemigroup_toContinuousMapOn`, `wfSemigroup_X_pow`: on polynomials the limit is given by
  duality, `E_x[(X_t)^n] = E_n[x^{A_t}]` with `A_t` the block-counting process.
* `wfSemigroup_add`, `wfSemigroup_apply_one`, `wfSemigroup_nonneg`, `norm_wfSemigroup_le`,
  `tendsto_wfSemigroup_nhdsGE_zero`: the Feller semigroup properties.
* `tendsto_wfSemigroup_sub_div`, `eval_polyGenerator`: the generator on polynomials is
  `x (1 - x) / 2 · p''`.

## References

* S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley
  (1986), Chapter 1 (Trotter–Kato, Feller semigroups) and Chapter 10 (genetic models).
* S. N. Ethier and R. C. Griffiths, *The transition function of a Fleming–Viot process*,
  Ann. Probab. 21 (1993) 1571–1590 (moment duality with the block-counting process).
* R. Durrett, *Probability Models for DNA Sequence Evolution*, 2nd ed., Springer (2008), ch. 7.
* J. F. C. Kingman, *The coalescent*, Stochastic Process. Appl. 13 (1982) 235–248.
-/

@[expose] public section

open Filter Topology Matrix Polynomial
open scoped unitInterval

namespace MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisherSemigroup

open MathlibExt.Biology.PopulationGenetics.Coalescent.KingmanBlockCounting

/-! ### The Wright–Fisher chain as an operator on continuous functions -/

/-- One generation of the neutral Wright–Fisher chain with `M` gene copies, acting on continuous
functions of the allele frequency: `(wfStep M f)(x) = ∑_k f(k/M) C(M, k) x^k (1 - x)^(M - k)`,
which for `M ≥ 1` is the expected value of `f` at the next frequency `Bin(M, x) / M` (the `M`-th
Bernstein operator, Mathlib's `bernsteinApproximation`; the expectation is
`ProbabilityTheory.integral_binomial`). It is a linear
contraction. At `M = 0` it returns the constant `f 0` (Lean's `k / 0 = 0`; no population). -/
noncomputable def wfStep (M : ℕ) : C(I, ℝ) →L[ℝ] C(I, ℝ) :=
  LinearMap.mkContinuous
    { toFun := bernsteinApproximation M
      map_add' := fun f g => by
        ext x
        simp [bernsteinApproximation.apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c f => by
        ext x
        simp [bernsteinApproximation.apply, Finset.mul_sum, smul_eq_mul, mul_left_comm] }
    1 (fun f => by
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun x => ?_
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul, bernsteinApproximation.apply]
      calc ‖∑ k : Fin (M + 1), bernstein M k x • f (bernstein.z k)‖
          ≤ ∑ k : Fin (M + 1), ‖bernstein M k x • f (bernstein.z k)‖ := norm_sum_le _ _
        _ ≤ ∑ k : Fin (M + 1), bernstein M k x * ‖f‖ := Finset.sum_le_sum fun k _ => by
            rw [norm_smul, Real.norm_of_nonneg bernstein_nonneg]
            exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) bernstein_nonneg
        _ = ‖f‖ := by rw [← Finset.sum_mul, bernstein.probability, one_mul])

/-- `wfStep M` is the Bernstein approximation operator. -/
theorem wfStep_apply (M : ℕ) (f : C(I, ℝ)) : wfStep M f = bernsteinApproximation M f := rfl

/-- One Wright–Fisher generation is a contraction for the sup norm. -/
theorem norm_wfStep_le (M : ℕ) : ‖wfStep M‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Any number of Wright–Fisher generations is a contraction for the sup norm. -/
theorem norm_wfStep_pow_le (M m : ℕ) : ‖wfStep M ^ m‖ ≤ 1 := by
  induction m with
  | zero => exact ContinuousLinearMap.norm_id_le
  | succ m ih =>
    rw [pow_succ, ContinuousLinearMap.mul_def]
    calc ‖(wfStep M ^ m).comp (wfStep M)‖ ≤ ‖wfStep M ^ m‖ * ‖wfStep M‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 :=
          mul_le_mul ih (norm_wfStep_le M) (ContinuousLinearMap.opNorm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-! ### Moment duality for the chain -/

/-- `C(M, i) · i_(j) = M_(j) · C(M - j, i - j)` for `j ≤ i`. -/
private theorem choose_mul_descFactorial (M i j : ℕ) (hji : j ≤ i) :
    M.choose i * i.descFactorial j =
      M.descFactorial j * (M - j).choose (i - j) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose]
  calc
    M.choose i * (j.factorial * i.choose j) =
        j.factorial * (M.choose i * i.choose j) := by ring
    _ = j.factorial * (M.choose j * (M - j).choose (i - j)) := by
      rw [Nat.choose_mul hji]
    _ = j.factorial * M.choose j * (M - j).choose (i - j) := by ring

/-- Factorial moments of the binomial law: `E[X_(j)] = M_(j) x^j` for `X ~ Bin(M, x)`. -/
private theorem binomial_factorial_moment (M j : ℕ) (x : ℝ) :
    ∑ i ∈ Finset.range (M + 1),
        (M.choose i : ℝ) * x ^ i * (1 - x) ^ (M - i) * (i.descFactorial j : ℝ) =
      (M.descFactorial j : ℝ) * x ^ j := by
  by_cases hj : j ≤ M
  · let f : ℕ → ℝ := fun i =>
      (M.choose i : ℝ) * x ^ i * (1 - x) ^ (M - i) * (i.descFactorial j : ℝ)
    have hlow : ∑ i ∈ Finset.range j, f i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [f, Nat.descFactorial_of_lt (Finset.mem_range.mp hi)]
    have hsplit : M + 1 = j + (M - j + 1) := by omega
    change ∑ i ∈ Finset.range (M + 1), f i = _
    rw [hsplit, Finset.sum_range_add, hlow, zero_add]
    calc
      ∑ r ∈ Finset.range (M - j + 1), f (j + r) =
          ∑ r ∈ Finset.range (M - j + 1),
            (M.descFactorial j : ℝ) * x ^ j *
              (((M - j).choose r : ℝ) * x ^ r * (1 - x) ^ (M - j - r)) := by
        apply Finset.sum_congr rfl
        intro r hr
        have hc : (M.choose (j + r) : ℝ) * ((j + r).descFactorial j : ℝ) =
            (M.descFactorial j : ℝ) * ((M - j).choose r : ℝ) := by
          have hc := choose_mul_descFactorial M (j + r) j (by omega)
          simp only [Nat.add_sub_cancel_left] at hc
          exact_mod_cast hc
        dsimp [f]
        rw [pow_add, show M - (j + r) = M - j - r by omega]
        calc
          _ = ((M.choose (j + r) : ℝ) * ((j + r).descFactorial j : ℝ)) *
              x ^ j * x ^ r * (1 - x) ^ (M - j - r) := by ring
          _ = _ := by rw [hc]; ring
      _ = (M.descFactorial j : ℝ) * x ^ j *
          (x + (1 - x)) ^ (M - j) := by
        rw [add_pow, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        ring
      _ = (M.descFactorial j : ℝ) * x ^ j := by
        rw [show x + (1 - x) = 1 by ring, one_pow, mul_one]
  · have hmj : M < j := by omega
    rw [Nat.descFactorial_of_lt hmj, Nat.cast_zero, zero_mul]
    apply Finset.sum_eq_zero
    intro i hi
    have hij : i < j := by have := Finset.mem_range.mp hi; omega
    simp [Nat.descFactorial_of_lt hij]

/-- **Moment duality, one generation (polynomial identity).** For `M ≥ 1` gene copies,
`∑_i C(M, i) x^i (1 - x)^(M - i) (i/M)^n = ∑_k S(n, k) M_(k) / M^n · x^k`: the `n`-th moment of
the frequency after one generation equals the generating function of the number of distinct
parents of `n` sampled genes. Holds for every real `x`.

Source: Ethier & Griffiths (1993); Durrett (2008), §7. -/
theorem sum_binomial_mul_div_pow (M n : ℕ) (hM : M ≠ 0) (x : ℝ) :
    ∑ i ∈ Finset.range (M + 1),
        (M.choose i : ℝ) * x ^ i * (1 - x) ^ (M - i) * ((i : ℝ) / M) ^ n =
      ∑ k ∈ Finset.range (n + 1), wfLineageProb M n k * x ^ k := by
  have hden : (M : ℝ) ^ n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hM)
  have hpow (i : ℕ) : (i : ℝ) ^ n =
      ∑ k ∈ Finset.range (n + 1),
        (Nat.stirlingSecond n k : ℝ) * (i.descFactorial k : ℝ) := by
    exact_mod_cast Nat.pow_eq_sum_stirlingSecond_mul_descFactorial i n
  calc
    ∑ i ∈ Finset.range (M + 1),
        (M.choose i : ℝ) * x ^ i * (1 - x) ^ (M - i) * ((i : ℝ) / M) ^ n =
        (∑ i ∈ Finset.range (M + 1),
          (M.choose i : ℝ) * x ^ i * (1 - x) ^ (M - i) * (i : ℝ) ^ n) /
            (M : ℝ) ^ n := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      rw [div_pow]
      exact mul_div_assoc' _ _ _
    _ = (∑ k ∈ Finset.range (n + 1), (Nat.stirlingSecond n k : ℝ) *
          (∑ i ∈ Finset.range (M + 1),
            (M.choose i : ℝ) * x ^ i * (1 - x) ^ (M - i) *
              (i.descFactorial k : ℝ))) / (M : ℝ) ^ n := by
      congr 1
      simp_rw [hpow, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ k ∈ Finset.range (n + 1),
          (Nat.stirlingSecond n k : ℝ) * (M.descFactorial k : ℝ) * x ^ k) /
            (M : ℝ) ^ n := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [binomial_factorial_moment]
      ring
    _ = ∑ k ∈ Finset.range (n + 1), wfLineageProb M n k * x ^ k := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k hk
      dsimp [wfLineageProb]
      field_simp

/-- **Moment duality, one generation.** If the allele count after one neutral Wright–Fisher
generation with `M ≥ 1` gene copies is `Bin(M, x)`, then
`E_x[(X₁)^n] = ∑_k wfLineageProb M n k · x^k`, where `X₁` is the new frequency and
`wfLineageProb M n k` is the probability that `n` genes have `k` distinct parents. -/
theorem integral_binomial_div_pow (M n : ℕ) (hM : M ≠ 0) (x : I) :
    ∫ i, ((i : ℝ) / M) ^ n ∂(ProbabilityTheory.binomial M x) =
      ∑ k ∈ Finset.range (n + 1), wfLineageProb M n k * (x : ℝ) ^ k := by
  rw [ProbabilityTheory.integral_binomial, ← Nat.range_succ_eq_Iic,
    ← sum_binomial_mul_div_pow M n hM]
  simp only [smul_eq_mul]

/-- A real linear combination of monomials, as a continuous function on `[0, 1]`. -/
private theorem toContinuousMapOn_sum_C_mul {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (e : ι → ℕ) :
    (∑ k ∈ s, C (a k) * X ^ e k).toContinuousMapOn I =
      ∑ k ∈ s, a k • (X ^ e k : ℝ[X]).toContinuousMapOn I := by
  ext x
  simp [eval_finsetSum]

/-- One generation maps `x ^ n` to `∑_k wfLineageProb M n k x ^ k`. -/
private theorem wfStep_X_pow (M n : ℕ) (hM : M ≠ 0) :
    wfStep M ((X ^ n : ℝ[X]).toContinuousMapOn I) =
      (∑ k ∈ Finset.range (n + 1), C (wfLineageProb M n k) * X ^ k).toContinuousMapOn I := by
  ext x
  simp only [wfStep_apply, bernsteinApproximation.apply, bernstein_apply, smul_eq_mul,
    toContinuousMapOn_apply, toContinuousMap_apply, eval_pow, eval_X, eval_finsetSum, eval_mul,
    eval_C, bernstein.z]
  rw [← sum_binomial_mul_div_pow M n hM,
    ← Fin.sum_univ_eq_sum_range (fun i => (M.choose i : ℝ) * (x : ℝ) ^ i * (1 - x) ^ (M - i) *
      ((i : ℝ) / M) ^ n)]

/-- One generation in the size-`N` coordinates of the lineage matrix. -/
private theorem wfStep_X_pow_fin (M N : ℕ) (hM : M ≠ 0) (n : Fin (N + 1)) :
    wfStep M ((X ^ (n : ℕ) : ℝ[X]).toContinuousMapOn I) =
      (∑ k : Fin (N + 1), C (wfLineageMatrix N M n k) * X ^ (k : ℕ)).toContinuousMapOn I := by
  rw [wfStep_X_pow M n hM]
  congr 1
  simp only [wfLineageMatrix, Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k => C (wfLineageProb M n k) * X ^ k) (N + 1)]
  refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun k _ hk => ?_
  simp only [Finset.mem_range, not_lt] at hk
  simp [wfLineageProb, Nat.stirlingSecond_eq_zero_of_lt (by omega : (n : ℕ) < k)]

/-- **Moment duality, `m` generations.** For `M ≥ 1` and `n ≤ N`, `m` generations of the
Wright–Fisher chain map `x ^ n` to `∑_k ((wfLineageMatrix N M)^m) n k · x^k`: the `n`-th moment
of the frequency after `m` generations is the generating function of the number of ancestors,
`m` generations back, of `n` sampled genes. -/
theorem wfStep_pow_X_pow (M m N : ℕ) (hM : M ≠ 0) (n : Fin (N + 1)) :
    (wfStep M ^ m) ((X ^ (n : ℕ) : ℝ[X]).toContinuousMapOn I) =
      (∑ k : Fin (N + 1),
        C ((wfLineageMatrix N M ^ m) n k) * X ^ (k : ℕ)).toContinuousMapOn I := by
  induction m generalizing n with
  | zero =>
    rw [pow_zero, pow_zero, one_apply_eq_self, Finset.sum_eq_single n]
    · simp
    · intro k _ hk
      simp [Matrix.one_apply_ne' hk]
    · simp
  | succ m ih =>
    rw [pow_succ, mul_apply_eq_comp, wfStep_X_pow_fin M N hM n,
      toContinuousMapOn_sum_C_mul, toContinuousMapOn_sum_C_mul, map_sum]
    simp only [map_smul, ih, toContinuousMapOn_sum_C_mul, Finset.smul_sum, smul_smul, pow_succ',
      Matrix.mul_apply, Finset.sum_smul]
    exact Finset.sum_comm

/-! ### The dual semigroup on polynomials -/

/-- The dual moment polynomial `∑_k P_t(n → k) X^k`, where for `t ≥ 0`,
`P_t(n → k) = exp (t • G) n k` is the probability that `n` lineages of Kingman's coalescent have
`k` ancestors time `t` earlier (time in units of `M = 2N` generations); evaluated at `x` it is
`E_n[x^{A_t}]` for the block-counting process `A`. -/
noncomputable def dualMomentPoly (t : ℝ) (n : ℕ) : ℝ[X] :=
  ∑ k : Fin (n + 1),
    C (NormedSpace.exp (t • blockCountingGenerator n) (Fin.last n) k) * X ^ (k : ℕ)

/-- The neutral Wright–Fisher diffusion semigroup on polynomials, defined by moment duality on
the monomial basis: `polySemigroup t (X ^ n) = dualMomentPoly t n`. It is meaningful for
`t ≥ 0`; the formula is defined, and the group law holds, for every real `t`. -/
noncomputable def polySemigroup (t : ℝ) : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  (Polynomial.basisMonomials ℝ).constr ℝ (dualMomentPoly t)

/-- The dual semigroup on a monomial is the dual moment polynomial. -/
theorem polySemigroup_X_pow (t : ℝ) (n : ℕ) : polySemigroup t (X ^ n) = dualMomentPoly t n := by
  have h : (X ^ n : ℝ[X]) = basisMonomials ℝ n := by rw [coe_basisMonomials, X_pow_eq_monomial]
  rw [h, polySemigroup, Module.Basis.constr_basis]

/-- `dualMomentPoly t k` written in the size-`n` coordinates, for `k ≤ n`. -/
private theorem dualMomentPoly_eq_sum_fin (t : ℝ) {n : ℕ} (k : Fin (n + 1)) :
    dualMomentPoly t k = ∑ j : Fin (n + 1),
      C (NormedSpace.exp (t • blockCountingGenerator n) k j) * X ^ (j : ℕ) := by
  set f : ℕ → ℝ[X] := fun j => if h : j < n + 1 then
    C (NormedSpace.exp (t • blockCountingGenerator n) k ⟨j, h⟩) * X ^ j else 0
  have hk := k.isLt
  have h1 : dualMomentPoly t k = ∑ j ∈ Finset.range (k + 1), f j := by
    rw [dualMomentPoly, ← Fin.sum_univ_eq_sum_range f]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : (j : ℕ) < n + 1 := by have := j.isLt; omega
    simp only [f, dite_eq_left hj]
    rw [← exp_smul_blockCountingGenerator_castLE (n := k) (N := n) (by omega) t (Fin.last k) j]
    congr 3
  have h2 : ∑ j : Fin (n + 1),
      C (NormedSpace.exp (t • blockCountingGenerator n) k j) * X ^ (j : ℕ) =
        ∑ j ∈ Finset.range (n + 1), f j := by
    rw [← Fin.sum_univ_eq_sum_range f]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [f]
    rw [dite_eq_left j.isLt]
  rw [h1, h2]
  refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun j hj hjk => ?_
  simp only [Finset.mem_range, not_lt] at hj hjk
  simp only [f, dite_eq_left hj]
  have hkj : k < ⟨j, hj⟩ := Fin.lt_def.2 (by simp; omega)
  rw [exp_smul_blockCountingGenerator_of_lt t hkj, C_0, zero_mul]

/-- At time `0` the dual semigroup is the identity. -/
theorem polySemigroup_zero : polySemigroup 0 = LinearMap.id := by
  refine (basisMonomials ℝ).ext fun n => ?_
  simp only [coe_basisMonomials, ← X_pow_eq_monomial, polySemigroup_X_pow, LinearMap.id_apply,
    dualMomentPoly, zero_smul, NormedSpace.exp_zero]
  rw [Finset.sum_eq_single (Fin.last n)]
  · simp
  · intro k _ hk
    simp [Matrix.one_apply_ne' hk]
  · simp

/-- **Semigroup law** on polynomials, from `exp ((s + t) • G) = exp (t • G) * exp (s • G)` and
truncation consistency; holds for all real `s`, `t`. -/
theorem polySemigroup_add (s t : ℝ) :
    polySemigroup (s + t) = polySemigroup s ∘ₗ polySemigroup t := by
  refine (basisMonomials ℝ).ext fun n => ?_
  simp only [coe_basisMonomials, ← X_pow_eq_monomial, LinearMap.comp_apply, polySemigroup_X_pow]
  conv_rhs => rw [dualMomentPoly]
  have hc : Commute (t • blockCountingGenerator n) (s • blockCountingGenerator n) :=
    ((Commute.refl _).smul_left t).smul_right s
  rw [dualMomentPoly, add_comm s t, add_smul, Matrix.exp_add_of_commute _ _ hc]
  simp only [C_mul', map_sum, map_smul, polySemigroup_X_pow]
  simp only [dualMomentPoly_eq_sum_fin s, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum,
    smul_smul, C_mul']
  exact Finset.sum_comm

/-- The dual semigroup fixes the constant polynomial `1` (zero lineages stay zero). -/
theorem polySemigroup_one (t : ℝ) : polySemigroup t 1 = 1 := by
  have hG : blockCountingGenerator 0 = 0 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [blockCountingGenerator]
  rw [← pow_zero (X : ℝ[X]), polySemigroup_X_pow, dualMomentPoly]
  simp [hG]

private theorem toContinuousMapOn_add' (p q : ℝ[X]) :
    (p + q).toContinuousMapOn I = p.toContinuousMapOn I + q.toContinuousMapOn I := by
  ext
  simp

private theorem toContinuousMapOn_smul' (a : ℝ) (p : ℝ[X]) :
    (a • p).toContinuousMapOn I = a • p.toContinuousMapOn I := by
  ext
  simp

/-- `polySemigroup t (X ^ n)` as a continuous function. -/
private theorem toContinuousMapOn_polySemigroup_X_pow (t : ℝ) (n : ℕ) :
    (polySemigroup t (X ^ n)).toContinuousMapOn I = ∑ k : Fin (n + 1),
      NormedSpace.exp (t • blockCountingGenerator n) (Fin.last n) k •
        (X ^ (k : ℕ) : ℝ[X]).toContinuousMapOn I := by
  rw [polySemigroup_X_pow, dualMomentPoly, toContinuousMapOn_sum_C_mul]

/-- **Convergence on polynomials.** For `t ≥ 0` and every polynomial `p`, `⌊tM⌋` generations
of the Wright–Fisher chain with `M` gene copies applied to `p` converge uniformly on `[0, 1]` to
`polySemigroup t p` as `M → ∞` (moment duality plus Kingman's theorem for the lineage count). -/
theorem tendsto_wfStep_pow_floor_toContinuousMapOn (p : ℝ[X]) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun M : ℕ => (wfStep M ^ ⌊t * M⌋₊) (p.toContinuousMapOn I)) atTop
      (𝓝 ((polySemigroup t p).toContinuousMapOn I)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [toContinuousMapOn_add', map_add] using hp.add hq
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, C_mul', map_smul]
    simp only [toContinuousMapOn_smul']
    rw [toContinuousMapOn_polySemigroup_X_pow]
    have hP := tendsto_wfLineageMatrix_pow_floor n ht
    have h : ∀ᶠ M : ℕ in atTop, a • ∑ k : Fin (n + 1),
        (wfLineageMatrix n M ^ ⌊t * M⌋₊) (Fin.last n) k •
          (X ^ (k : ℕ) : ℝ[X]).toContinuousMapOn I =
        (wfStep M ^ ⌊t * M⌋₊) (a • (X ^ n : ℝ[X]).toContinuousMapOn I) := by
      filter_upwards [eventually_ne_atTop 0] with M hM
      have := wfStep_pow_X_pow M ⌊t * M⌋₊ n hM (Fin.last n)
      rw [Fin.val_last] at this
      rw [map_smul, this, toContinuousMapOn_sum_C_mul]
    refine Tendsto.congr' h ?_
    exact (tendsto_finsetSum _ fun k _ =>
      (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hP (Fin.last n)) k).smul_const _).const_smul a

/-! ### The semigroup on continuous functions -/

private theorem cauchySeq_apply_of_dense {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : ℕ → E →L[ℝ] E} (hL : ∀ M, ‖L M‖ ≤ 1) {D : Set E}
    (hD : Dense D) (h : ∀ d ∈ D, CauchySeq fun M => L M d) (f : E) :
    CauchySeq fun M => L M f := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hε3 : 0 < ε / 3 := by linarith
  obtain ⟨d, hd, hfd⟩ := hD.exists_dist_lt f hε3
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (h d hd) (ε / 3) hε3
  have hdist (M : ℕ) : dist (L M f) (L M d) ≤ dist f d := by
    simpa only [dist_eq_norm, ← map_sub, one_mul] using
      (L M).le_of_opNorm_le (hL M) (f - d)
  refine ⟨N, ?_⟩
  intro M hM P hP
  have hmid := hN M hM P hP
  have hlast : dist (L P d) (L P f) ≤ dist f d := by
    rw [dist_comm]
    exact hdist P
  have htri := dist_triangle4 (L M f) (L M d) (L P d) (L P f)
  linarith [hdist M]

private theorem tendsto_apply_of_dense {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} {l : Filter ι} {T : ι → E →L[ℝ] E}
    (hT : ∀ i, ‖T i‖ ≤ 1) {S : E →L[ℝ] E} (hS : ‖S‖ ≤ 1) {D : Set E} (hD : Dense D)
    (h : ∀ d ∈ D, Tendsto (fun i => T i d) l (𝓝 (S d))) (f : E) :
    Tendsto (fun i => T i f) l (𝓝 (S f)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hε3 : 0 < ε / 3 := by linarith
  obtain ⟨d, hd, hfd⟩ := hD.exists_dist_lt f hε3
  have hdist (i : ι) : dist (T i f) (T i d) ≤ dist f d := by
    simpa only [dist_eq_norm, ← map_sub, one_mul] using
      (T i).le_of_opNorm_le (hT i) (f - d)
  have hlast : dist (S d) (S f) ≤ dist f d := by
    simpa only [dist_eq_norm, ← map_sub, one_mul, norm_sub_rev] using
      S.le_of_opNorm_le hS (d - f)
  apply (Metric.tendsto_nhds.mp (h d hd) (ε / 3) hε3).mono
  intro i hi
  have htri := dist_triangle4 (T i f) (T i d) (S d) (S f)
  linarith [hdist i]

/-- Weierstrass: polynomial functions are dense in `C([0, 1], ℝ)`. -/
private theorem dense_polynomialFunctions : Dense (polynomialFunctions I : Set C(I, ℝ)) := by
  rw [dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe,
    polynomialFunctions_closure_eq_top']
  rfl

private theorem floor_mul_eq_zero {t : ℝ} (ht : t ≤ 0) (M : ℕ) : ⌊t * M⌋₊ = 0 :=
  Nat.floor_of_nonpos (mul_nonpos_of_nonpos_of_nonneg ht (Nat.cast_nonneg M))

/-- For every continuous `f`, the sequence `(wfStep M)^⌊tM⌋ f` is Cauchy in `C([0, 1], ℝ)`: it
converges on the dense set of polynomials and the operators are contractions. -/
theorem cauchySeq_wfStep_pow_floor (t : ℝ) (f : C(I, ℝ)) :
    CauchySeq fun M : ℕ => (wfStep M ^ ⌊t * M⌋₊) f := by
  rcases le_or_gt 0 t with ht | ht
  · refine cauchySeq_apply_of_dense (fun M => norm_wfStep_pow_le M _) dense_polynomialFunctions
      (fun d hd => ?_) f
    rw [polynomialFunctions_coe] at hd
    obtain ⟨p, rfl⟩ := hd
    exact (tendsto_wfStep_pow_floor_toContinuousMapOn p ht).cauchySeq
  · simp only [floor_mul_eq_zero ht.le, pow_zero]
    exact cauchySeq_const _

/-- The neutral Wright–Fisher diffusion semigroup on `C([0, 1], ℝ)`, time in units of `M = 2N`
generations: `wfSemigroup t f` is the uniform limit of `(wfStep M)^⌊tM⌋ f` as `M → ∞`
(`tendsto_wfStep_pow_floor`). For `t < 0` it is the identity (a junk value: `⌊tM⌋₊ = 0`). -/
noncomputable def wfSemigroup (t : ℝ) : C(I, ℝ) →L[ℝ] C(I, ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun f => limUnder atTop fun M : ℕ => (wfStep M ^ ⌊t * M⌋₊) f
      map_add' := fun f g => by
        refine tendsto_nhds_unique (cauchySeq_wfStep_pow_floor t (f + g)).tendsto_limUnder ?_
        simpa using ((cauchySeq_wfStep_pow_floor t f).tendsto_limUnder).add
          (cauchySeq_wfStep_pow_floor t g).tendsto_limUnder
      map_smul' := fun c f => by
        refine tendsto_nhds_unique (cauchySeq_wfStep_pow_floor t (c • f)).tendsto_limUnder ?_
        simpa using ((cauchySeq_wfStep_pow_floor t f).tendsto_limUnder).const_smul c }
    1 (fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      refine le_of_tendsto ((cauchySeq_wfStep_pow_floor t f).tendsto_limUnder).norm
        (Eventually.of_forall fun M => ?_)
      exact ((wfStep M ^ ⌊t * M⌋₊).le_opNorm f).trans
        (mul_le_of_le_one_left (norm_nonneg f) (norm_wfStep_pow_le M _)))

/-- **Diffusion approximation of the transition operators (Trotter–Kato, concrete form).** For
every continuous `f`, `⌊tM⌋` generations of the neutral Wright–Fisher chain with `M` gene copies
applied to `f` converge uniformly on `[0, 1]` to `wfSemigroup t f`.

Source: Ethier & Kurtz (1986), ch. 1, §6 (approximation theorems), and ch. 10. -/
theorem tendsto_wfStep_pow_floor (t : ℝ) (f : C(I, ℝ)) :
    Tendsto (fun M : ℕ => (wfStep M ^ ⌊t * M⌋₊) f) atTop (𝓝 (wfSemigroup t f)) :=
  (cauchySeq_wfStep_pow_floor t f).tendsto_limUnder

/-- **Contraction.** `sup_{[0,1]} |wfSemigroup t f| ≤ sup_{[0,1]} |f|`. -/
theorem norm_wfSemigroup_le (t : ℝ) : ‖wfSemigroup t‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- On polynomials the diffusion semigroup is the dual semigroup, for `t ≥ 0`. -/
theorem wfSemigroup_toContinuousMapOn {t : ℝ} (ht : 0 ≤ t) (p : ℝ[X]) :
    wfSemigroup t (p.toContinuousMapOn I) = (polySemigroup t p).toContinuousMapOn I :=
  tendsto_nhds_unique (tendsto_wfStep_pow_floor t _)
    (tendsto_wfStep_pow_floor_toContinuousMapOn p ht)

/-- For `t ≤ 0`, `wfSemigroup t` is the identity (at `t = 0` by definition of a semigroup; for
`t < 0` this is a junk value of the definition). -/
theorem wfSemigroup_of_nonpos {t : ℝ} (ht : t ≤ 0) : wfSemigroup t = 1 := by
  refine ContinuousLinearMap.ext fun f => tendsto_nhds_unique (tendsto_wfStep_pow_floor t f) ?_
  simp only [floor_mul_eq_zero ht, pow_zero, one_apply_eq_self]
  exact tendsto_const_nhds

/-- At time `0` the diffusion semigroup is the identity. -/
@[simp]
theorem wfSemigroup_zero : wfSemigroup 0 = 1 :=
  wfSemigroup_of_nonpos le_rfl

/-- **Moment duality for the diffusion** (Ethier & Griffiths 1993). For `t ≥ 0`, the semigroup
applied to `x ↦ x ^ n` is `∑_k P_t(n → k) x^k`, with `P_t = exp (t • G)` the transition matrix of
Kingman's block-counting process `A`; in process language `E_x[(X_t)^n] = E_n[x^{A_t}]` (the
processes themselves are not constructed here). -/
theorem wfSemigroup_X_pow {t : ℝ} (ht : 0 ≤ t) (n : ℕ) (x : I) :
    wfSemigroup t ((X ^ n : ℝ[X]).toContinuousMapOn I) x =
      ∑ k : Fin (n + 1),
        NormedSpace.exp (t • blockCountingGenerator n) (Fin.last n) k * (x : ℝ) ^ (k : ℕ) := by
  rw [wfSemigroup_toContinuousMapOn ht, polySemigroup_X_pow, dualMomentPoly]
  simp [eval_finsetSum]

/-- **Semigroup law** for `s, t ≥ 0`. -/
theorem wfSemigroup_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    wfSemigroup (s + t) = wfSemigroup s * wfSemigroup t := by
  refine DFunLike.coe_injective (Continuous.ext_on dense_polynomialFunctions (map_continuous _)
    (map_continuous _) fun d hd => ?_)
  rw [SetLike.mem_coe, ← SetLike.mem_coe, polynomialFunctions_coe] at hd
  obtain ⟨p, rfl⟩ := hd
  simp only [toContinuousMapOnAlgHom_apply, mul_apply_eq_comp]
  rw [wfSemigroup_toContinuousMapOn (add_nonneg hs ht), wfSemigroup_toContinuousMapOn ht,
    wfSemigroup_toContinuousMapOn hs, polySemigroup_add, LinearMap.comp_apply]

private theorem wfStep_pow_one (M m : ℕ) : (wfStep M ^ m) 1 = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : wfStep M 1 = 1 := by
      ext x
      simp [wfStep_apply, bernsteinApproximation.apply, bernstein.probability]
    rw [pow_succ, mul_apply_eq_comp, h1, ih]

/-- The diffusion semigroup fixes constants (it is Markov: total mass `1`). -/
theorem wfSemigroup_apply_one (t : ℝ) : wfSemigroup t 1 = 1 := by
  refine tendsto_nhds_unique (tendsto_wfStep_pow_floor t 1) ?_
  simp only [wfStep_pow_one]
  exact tendsto_const_nhds

private theorem wfStep_pow_nonneg (M m : ℕ) {f : C(I, ℝ)} (hf : 0 ≤ f) :
    0 ≤ (wfStep M ^ m) f := by
  induction m with
  | zero => simpa using hf
  | succ m ih =>
    rw [pow_succ', mul_apply_eq_comp]
    refine ContinuousMap.le_def.2 fun x => ?_
    simp only [ContinuousMap.zero_apply, wfStep_apply, bernsteinApproximation.apply]
    exact Finset.sum_nonneg fun k _ => smul_nonneg bernstein_nonneg (ContinuousMap.le_def.1 ih _)

/-- **Positivity.** The diffusion semigroup maps nonnegative functions to nonnegative functions. -/
theorem wfSemigroup_nonneg (t : ℝ) {f : C(I, ℝ)} (hf : 0 ≤ f) : 0 ≤ wfSemigroup t f :=
  ContinuousMap.le_def.2 fun x => ge_of_tendsto'
    (((continuous_eval_const x).tendsto _).comp (tendsto_wfStep_pow_floor t f))
    fun M => ContinuousMap.le_def.1 (wfStep_pow_nonneg M _ hf) x

/-- Entries of `exp (t • G)` as finite sums of exponentials (spectral decomposition). -/
private theorem exp_smul_apply_eq_sum (n : ℕ) (t : ℝ) (i j : Fin (n + 1)) :
    NormedSpace.exp (t • blockCountingGenerator n) i j =
      ∑ l, blockCountingRightEigen n i l * Real.exp (t * blockCountingEigenvalue n l) *
        blockCountingLeftEigen n l j := by
  rw [exp_smul_blockCountingGenerator, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]

private theorem hasDerivAt_exp_smul_apply (n : ℕ) (i j : Fin (n + 1)) (t : ℝ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • blockCountingGenerator n) i j)
      (∑ l, blockCountingRightEigen n i l *
        (blockCountingEigenvalue n l * Real.exp (t * blockCountingEigenvalue n l)) *
          blockCountingLeftEigen n l j) t := by
  simp only [exp_smul_apply_eq_sum]
  refine HasDerivAt.fun_sum fun l _ => ?_
  have h := ((hasDerivAt_mul_const (x := t) (blockCountingEigenvalue n l)).exp.const_mul
    (blockCountingRightEigen n i l)).mul_const (blockCountingLeftEigen n l j)
  convert h using 1
  ring

private theorem hasDerivAt_exp_smul_apply_zero (n : ℕ) (i j : Fin (n + 1)) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • blockCountingGenerator n) i j)
      (blockCountingGenerator n i j) 0 := by
  convert hasDerivAt_exp_smul_apply n i j 0 using 1
  have hVW := mul_eq_one_comm.1 (blockCountingLeftEigen_mul_rightEigen n)
  have hG : blockCountingRightEigen n * diagonal (blockCountingEigenvalue n) *
      blockCountingLeftEigen n = blockCountingGenerator n := by
    rw [← blockCountingGenerator_mul_rightEigen, Matrix.mul_assoc, hVW, Matrix.mul_one]
  rw [← hG, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, zero_mul, Real.exp_zero, mul_one]

private theorem continuous_toContinuousMapOn_polySemigroup (p : ℝ[X]) :
    Continuous fun t => (polySemigroup t p).toContinuousMapOn I := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, toContinuousMapOn_add']
    exact hp.add hq
  | monomial n a =>
    simp only [← C_mul_X_pow_eq_monomial, C_mul', map_smul, toContinuousMapOn_smul',
      toContinuousMapOn_polySemigroup_X_pow]
    refine Continuous.const_smul ?_ a
    exact (continuous_finsetSum _ fun k _ =>
      (continuous_iff_continuousAt.2 fun t =>
        (hasDerivAt_exp_smul_apply n (Fin.last n) k t).continuousAt).smul
          (continuous_const (y := ((X ^ (k : ℕ) : ℝ[X]).toContinuousMapOn I))))

/-- **Strong continuity.** `wfSemigroup t f → f` uniformly as `t → 0⁺`, for every continuous
`f`. -/
theorem tendsto_wfSemigroup_nhdsGE_zero (f : C(I, ℝ)) :
    Tendsto (fun t => wfSemigroup t f) (𝓝[≥] 0) (𝓝 f) := by
  have h := tendsto_apply_of_dense (T := wfSemigroup) (l := 𝓝[≥] (0 : ℝ)) norm_wfSemigroup_le
    (S := 1) ContinuousLinearMap.norm_id_le dense_polynomialFunctions ?_ f
  · simpa using h
  intro d hd
  rw [polynomialFunctions_coe] at hd
  obtain ⟨p, rfl⟩ := hd
  refine Tendsto.congr' (eventually_nhdsWithin_of_forall fun t ht =>
    (wfSemigroup_toContinuousMapOn ht p).symm) ?_
  have := ((continuous_toContinuousMapOn_polySemigroup p).tendsto 0).mono_left
    (nhdsWithin_le_nhds (s := Set.Ici 0))
  simpa [polySemigroup_zero] using this

/-- The neutral Wright–Fisher generator on polynomials, `x (1 - x) / 2 · p''`. -/
noncomputable def polyGenerator (p : ℝ[X]) : ℝ[X] :=
  C (1 / 2 : ℝ) * X * (1 - X) * derivative (derivative p)

/-- `polyGenerator` is the neutral Wright–Fisher generator `generator 0` evaluated on `p`. -/
theorem eval_polyGenerator (p : ℝ[X]) (x : ℝ) :
    (polyGenerator p).eval x = generator 0 (fun y => p.eval y) x := by
  have h : deriv (fun y => p.eval y) = fun y => (derivative p).eval y :=
    funext fun y => Polynomial.deriv p
  simp only [polyGenerator, generator, h, Polynomial.deriv, eval_mul, eval_C, eval_X, eval_sub,
    eval_one]
  ring

/-- The generator sums of the dual process: `∑_k G n k x^k = C(n, 2) (x^(n-1) - x^n)`. -/
private theorem sum_blockCountingGenerator_last (n : ℕ) (x : ℝ) :
    ∑ k : Fin (n + 1), blockCountingGenerator n (Fin.last n) k * x ^ (k : ℕ) =
      (n.choose 2 : ℝ) * (x ^ (n - 1) - x ^ n) := by
  rcases n with _ | m
  · simp [blockCountingGenerator]
  · rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [blockCountingGenerator, Matrix.of_apply, Fin.ext_iff, Fin.val_castSucc,
      Fin.val_last]
    rw [Finset.sum_eq_zero fun k _ => by
      have := k.isLt
      simp only [show (k : ℕ) + 1 ≠ m + 1 by omega, show (k : ℕ) ≠ m + 1 by omega, ite_false,
        zero_mul]]
    simp only [show m + 1 + 1 ≠ m + 1 by omega, ite_true, ite_false, Nat.add_sub_cancel]
    ring

private theorem polyGenerator_add (p q : ℝ[X]) :
    polyGenerator (p + q) = polyGenerator p + polyGenerator q := by
  simp only [polyGenerator, map_add, mul_add]

private theorem polyGenerator_smul (a : ℝ) (p : ℝ[X]) :
    polyGenerator (a • p) = a • polyGenerator p := by
  simp only [polyGenerator, map_smul, mul_smul_comm]

private theorem toContinuousMapOn_polyGenerator_X_pow (n : ℕ) :
    (polyGenerator (X ^ n)).toContinuousMapOn I = ∑ k : Fin (n + 1),
      blockCountingGenerator n (Fin.last n) k • (X ^ (k : ℕ) : ℝ[X]).toContinuousMapOn I := by
  ext x
  simp only [toContinuousMapOn_apply, toContinuousMap_apply, eval_polyGenerator,
    ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply, smul_eq_mul, eval_pow,
    eval_X]
  rw [generator_pow, sum_blockCountingGenerator_last]

private theorem tendsto_polySemigroup_sub_div (p : ℝ[X]) :
    Tendsto (fun t : ℝ => t⁻¹ •
        ((polySemigroup t p).toContinuousMapOn I - p.toContinuousMapOn I))
      (𝓝[>] 0) (𝓝 ((polyGenerator p).toContinuousMapOn I)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [polyGenerator_add]
    simp only [map_add, toContinuousMapOn_add']
    refine (hp.add hq).congr fun t => ?_
    rw [← smul_add]
    congr 1
    abel
  | monomial n a =>
    have hslope : ∀ k : Fin (n + 1), Tendsto (fun t : ℝ => t⁻¹ *
        (NormedSpace.exp (t • blockCountingGenerator n) (Fin.last n) k -
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (Fin.last n) k))
        (𝓝[>] 0) (𝓝 (blockCountingGenerator n (Fin.last n) k)) := fun k => by
      simpa using (hasDerivAt_exp_smul_apply_zero n (Fin.last n) k).tendsto_slope_zero_right
    have h0 : (X ^ n : ℝ[X]).toContinuousMapOn I = ∑ k : Fin (n + 1),
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (Fin.last n) k •
          (X ^ (k : ℕ) : ℝ[X]).toContinuousMapOn I := by
      have h := toContinuousMapOn_polySemigroup_X_pow 0 n
      rw [polySemigroup_zero, LinearMap.id_apply, zero_smul, NormedSpace.exp_zero] at h
      exact h
    rw [← C_mul_X_pow_eq_monomial, C_mul', polyGenerator_smul]
    simp only [map_smul, toContinuousMapOn_smul']
    rw [toContinuousMapOn_polyGenerator_X_pow]
    refine Tendsto.congr (fun t => ?_) ((tendsto_finsetSum _ fun k _ =>
      (hslope k).smul_const ((X ^ (k : ℕ) : ℝ[X]).toContinuousMapOn I)).const_smul a)
    rw [toContinuousMapOn_polySemigroup_X_pow, h0, ← smul_sub, ← Finset.sum_sub_distrib,
      smul_comm, Finset.smul_sum]
    simp only [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← sub_smul, smul_smul, smul_smul, smul_smul, mul_assoc]

/-- **Generator on polynomials.** For every polynomial `p`,
`(wfSemigroup t p - p) / t → x (1 - x) / 2 · p''` uniformly on `[0, 1]` as `t → 0⁺`.

Source: Ethier & Kurtz (1986), ch. 10; Durrett (2008), §7. -/
theorem tendsto_wfSemigroup_sub_div (p : ℝ[X]) :
    Tendsto (fun t : ℝ => t⁻¹ • (wfSemigroup t (p.toContinuousMapOn I) - p.toContinuousMapOn I))
      (𝓝[>] 0) (𝓝 ((polyGenerator p).toContinuousMapOn I)) :=
  (tendsto_polySemigroup_sub_div p).congr' (eventually_nhdsWithin_of_forall fun t ht => by
    dsimp only
    rw [wfSemigroup_toContinuousMapOn (le_of_lt ht)])

end MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisherSemigroup
