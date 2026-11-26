/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.MobiusFermat
import all MathlibExt.NumberTheory.MobiusFermatReduction
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finsupp.Weight

/-!
# The multinomial formula for the von Mangoldt–Fermat function

We prove the signed factorial formula for the von Mangoldt–Fermat function at products of
Mersenne numbers whose exponent vectors exclude the exceptional factor `63 = 3 ^ 2 * 7`.
-/

open ArithmeticFunction Finsupp Finset

namespace MetaMathlibExt
namespace vonMangoldtFermat_eq_multinomial

open mobiusFermat_mul_factorial_eq_squarefree_part

private theorem single_le_of_mem {d : Index →₀ ℕ} {i : Index} (hi : i ∈ d.support) :
    single i 1 ≤ d :=
  Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))

private theorem sub_single_add {d : Index →₀ ℕ} {i : Index} (hi : i ∈ d.support) :
    d - single i 1 + single i 1 = d :=
  tsub_add_cancel_of_le (single_le_of_mem hi)

-- The term with second factor one survives for a general weight. All other contributing
-- pairs remove one Mersenne factor, since the exponent bounds exclude the factor 63.
private theorem sum_divisors {R : Type*} [Semiring R]
    (μ : ArithmeticFunction ℤ) (hμ : μ * fermatUnitFunction = 1)
    (φ : ℤ →+ R) (w : ℕ → R) (d : Index →₀ ℕ) (hd : d two ≤ 1 ∨ d three = 0) :
    (∑ p ∈ (value d).divisorsAntidiagonal, φ (μ p.1 * fermatUnitFunction p.2) * w p.2) =
      φ (μ (value d)) * w 1 +
        ∑ i ∈ d.support, φ (μ (value (d - single i 1))) * w (mersenne i) := by
  classical
  have hfilter : ((value d).divisorsAntidiagonal.filter fun p => p.2 = 1) =
      {(value d, 1)} := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal, ne_eq, Finset.mem_singleton,
      Prod.mk.injEq, value_ne_zero, not_false_eq_true, and_true]
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨by simpa using h, rfl⟩
    · rintro ⟨rfl, rfl⟩
      simp
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun p => p.2 = 1), hfilter, Finset.sum_singleton,
    fermatUnitFunction_small_values.1, mul_one]
  congr 1
  let e (i : Index) := (value (d - single i 1), mersenne i)
  symm
  apply Finset.sum_of_injOn e
  · intro i _ j _ hij
    have hs : single i 1 = single j 1 := value_injective (by
      simpa only [value_single, pow_one] using congrArg Prod.snd hij)
    simpa using congrArg Finsupp.support hs
  · intro i hi
    have hm : 1 < mersenne i := one_lt_mersenne.mpr i.2.1
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisorsAntidiagonal.mpr
      ⟨by simpa only [value_add, value_single, pow_one] using congrArg value (sub_single_add hi),
        value_ne_zero d⟩, hm.ne'⟩
  · rintro ⟨a, b⟩ hab hout
    by_cases hz : μ a * fermatUnitFunction b = 0
    · rw [hz, _root_.map_zero, zero_mul]
    exfalso
    obtain ⟨u, rfl⟩ := inverse_in_range μ hμ (left_ne_zero_of_mul hz)
    obtain ⟨n, hn, rfl⟩ := unit_index (right_ne_zero_of_mul hz)
    have hmem := Finset.mem_filter.mp hab
    have hprod := (Nat.mem_divisorsAntidiagonal.mp hmem.1).1
    rcases generator_cases hn with h1 | h6 | ⟨i, hi⟩
    · exact hmem.2 h1
    · have heq : u + base 2 1 = d := value_injective (by rw [value_add, ← h6, hprod])
      have htwo : d two = u two + 2 := by
        rw [← heq]
        simp [base]
      have hthree : d three = u three + 1 := by
        rw [← heq]
        simp [base]
      omega
    · have heq : u + single i 1 = d :=
        value_injective (by rw [value_add, value_single, pow_one, ← hi, hprod])
      have his : i ∈ d.support := by rw [← heq]; simp
      apply hout
      refine ⟨i, his, ?_⟩
      simp [e, ← heq, hi]
  · intro i _
    rw [show fermatUnitFunction (e i).2 = 1 from
      fermatUnitFunction_two_pow_sub_one (le_trans (by decide) i.2.1), mul_one]

private theorem degree_sub_single {d : Index →₀ ℕ} {i : Index} (hi : i ∈ d.support) :
    (d - single i 1).degree + 1 = d.degree := by
  simpa only [map_add, Finsupp.degree_single] using congrArg Finsupp.degree (sub_single_add hi)

private theorem restriction_sub_single {d : Index →₀ ℕ} (hd : d two ≤ 1 ∨ d three = 0)
    (i : Index) : ((d - single i 1 : Index →₀ ℕ) two) ≤ 1 ∨
      ((d - single i 1 : Index →₀ ℕ) three) = 0 := by
  have hle : d - single i 1 ≤ d := tsub_le_self
  rcases hd with h | h
  · exact Or.inl ((hle two).trans h)
  · exact Or.inr (Nat.eq_zero_of_le_zero (h ▸ hle three))

private theorem factorials_sub_single {d : Index →₀ ℕ} {i : Index} (hi : i ∈ d.support) :
    factorials d = (d i : ℤ) * factorials (d - single i 1) := by
  have he : (d - single i 1 : Index →₀ ℕ) i + 1 = d i := by
    simpa only [Finsupp.add_apply, Finsupp.single_eq_same] using
      congrArg (fun f : Index →₀ ℕ => f i) (sub_single_add hi)
  have hc : ((d - single i 1 : Index →₀ ℕ) i : ℤ) + 1 = d i := by exact_mod_cast he
  have h := factorials_succ (d - single i 1) i
  rw [sub_single_add hi, hc] at h
  exact h

-- Multiplying by the factorial product makes each predecessor term proportional to its
-- removed multiplicity. Summing those multiplicities gives the total degree.
private theorem inverse_mul_factorials (μ : ArithmeticFunction ℤ) (hμ : μ * fermatUnitFunction = 1)
    (d : Index →₀ ℕ) (hd : d two ≤ 1 ∨ d three = 0) :
    μ (value d) * factorials d = (-1) ^ d.degree * (d.degree.factorial : ℤ) := by
  classical
  by_cases hz : d = 0
  · subst d
    simp [factorials, (mobiusFermat_one_and_vanishing μ hμ).1]
  have hv : value d ≠ 1 := fun h => hz (value_injective (h.trans value_zero.symm))
  have hconv := sum_divisors μ hμ (AddMonoidHom.id ℤ) (fun _ => 1) d hd
  simp only [AddMonoidHom.id_apply, mul_one, ← ArithmeticFunction.mul_apply, hμ,
    ArithmeticFunction.one_apply, hv, ite_false] at hconv
  have hμd : μ (value d) = -(∑ i ∈ d.support, μ (value (d - single i 1))) := by omega
  have hsum : (∑ i ∈ d.support, μ (value (d - single i 1))) * factorials d =
      (-1) ^ (d.degree - 1) * ((d.degree - 1).factorial : ℤ) * d.degree := by
    have hcast : (d.degree : ℤ) = ∑ i ∈ d.support, (d i : ℤ) := by
      rw [Finsupp.degree_apply, Nat.cast_sum]
    rw [Finset.sum_mul, hcast, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hdeg := degree_sub_single hi
    have hdegree : Finsupp.degree (d - single i 1) = d.degree - 1 :=
      Nat.eq_sub_of_add_eq hdeg
    have hrec := inverse_mul_factorials μ hμ (d - single i 1) (restriction_sub_single hd i)
    rw [factorials_sub_single hi, mul_left_comm, hrec, hdegree, mul_comm (d i : ℤ)]
  have hdeg : d.degree ≠ 0 := fun h => hz ((Finsupp.degree_eq_zero_iff d).mp h)
  have hsucc : d.degree - 1 + 1 = d.degree :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hdeg)
  rw [hμd, neg_mul, hsum, ← hsucc, pow_succ, Nat.factorial_succ]
  simp only [Nat.add_sub_cancel, Nat.cast_mul]
  ring
termination_by d.degree
decreasing_by omega

private theorem log_value (d : Index →₀ ℕ) :
    Real.log (value d : ℕ) = ∑ i ∈ d.support, (d i : ℝ) * Real.log (mersenne i) := by
  rw [value, Nat.cast_finsuppProd]
  simp_rw [Finsupp.prod, Nat.cast_pow, Real.log_prod
    (fun i _ => pow_ne_zero _ (Nat.cast_ne_zero.mpr (gen_pos i).ne')), Real.log_pow]

private theorem convolution (μ : ArithmeticFunction ℤ) (hμ : μ * fermatUnitFunction = 1)
    (d : Index →₀ ℕ) (hd : d two ≤ 1 ∨ d three = 0) :
    ((μ : ArithmeticFunction ℝ) * (fermatUnitFunction : ArithmeticFunction ℝ).pmul log)
        (value d) =
      (-1) ^ (d.degree - 1) * ((d.degree - 1).factorial : ℝ) /
        (d.prod fun _ m => (m.factorial : ℝ)) * Real.log (value d : ℕ) := by
  have hs := sum_divisors μ hμ (Int.castAddHom ℝ) (fun b => Real.log b) d hd
  simp only [Int.coe_castAddHom, Int.cast_mul, Nat.cast_one, Real.log_one, mul_zero,
    zero_add] at hs
  rw [ArithmeticFunction.mul_apply]
  simp only [ArithmeticFunction.pmul_apply, ArithmeticFunction.intCoe_apply, log_apply,
    ← mul_assoc]
  rw [hs, log_value]
  have hfac : (factorials d : ℝ) = d.prod fun _ m => (m.factorial : ℝ) := by
    simp [factorials, Finsupp.prod]
  have hne : (factorials d : ℝ) ≠ 0 := by
    rw [hfac]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [← hfac, div_mul_eq_mul_div, eq_div_iff hne, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i hi => by
    have hdegree : Finsupp.degree (d - single i 1) = d.degree - 1 :=
      Nat.eq_sub_of_add_eq (degree_sub_single hi)
    have hrec := congrArg (fun x : ℤ => (x : ℝ))
      (inverse_mul_factorials μ hμ (d - single i 1) (restriction_sub_single hd i))
    push_cast at hrec
    rw [hdegree] at hrec
    rw [factorials_sub_single hi, Int.cast_mul, Int.cast_natCast, ← hrec]
    ring

end vonMangoldtFermat_eq_multinomial

open mobiusFermat_mul_factorial_eq_squarefree_part vonMangoldtFermat_eq_multinomial in
/-- **Multinomial formula for the von Mangoldt–Fermat function.** Let $u_M$ be the Fermat unit
function, and let $\mu$ be an integer-valued arithmetic function with $\mu * u_M = \varepsilon$,
where $*$ is Dirichlet convolution and $\varepsilon$ is its identity (so $\mu$ is the
Möbius–Fermat function $\mu_M$). Let $\Lambda_M = \mu * u'_M$, computed with real values, where
$u'_M(l) = u_M(l) \log l$. Let $f : \mathbb{N} \to \mathbb{N}$ be finitely supported, with
$n \ge 2$ and $n \ne 6$ for every $n$ such that $f(n) \ne 0$, and with $f(2) \le 1$ or $f(3) = 0$.
Put $l = \prod_n (2^n - 1)^{f(n)}$ and $r = \sum_n f(n)$. Then
$$\Lambda_M(l) = (-1)^{r - 1} \frac{(r - 1)!}{\prod_n f(n)!} \log l,$$
where $r - 1$ is read as $0$ when $r = 0$.

Source: J. L. Varona, *The Möbius and the von Mangoldt-type Functions of the Fermat Zeta
Function*, INTEGERS 26 (2026), Article A106, Proposition 5. -/
public theorem vonMangoldtFermat_eq_multinomial (μ : ArithmeticFunction ℤ)
    (hμ : μ * fermatUnitFunction = 1) (f : ℕ →₀ ℕ) (hf : ∀ n ∈ f.support, 2 ≤ n ∧ n ≠ 6)
    (h37 : f 2 ≤ 1 ∨ f 3 = 0) :
    ((μ : ArithmeticFunction ℝ) * (fermatUnitFunction : ArithmeticFunction ℝ).pmul log)
        (f.prod fun n m => (2 ^ n - 1) ^ m) =
      (-1) ^ ((f.sum fun _ m => m) - 1) * (((f.sum fun _ m => m) - 1).factorial : ℝ) /
        (f.prod fun _ m => (m.factorial : ℝ)) *
        Real.log (f.prod fun n m => (2 ^ n - 1) ^ m : ℕ) := by
  let d := f.subtypeDomain fun n => 2 ≤ n ∧ n ≠ 6
  have hd : d two ≤ 1 ∨ d three = 0 := h37
  have hdegree : d.degree = d.sum fun _ m => m := rfl
  simpa only [value, hdegree, d, mersenne,
    Finsupp.prod_subtypeDomain_index (h := fun (n m : ℕ) => (2 ^ n - 1) ^ m) hf,
    Finsupp.prod_subtypeDomain_index (h := fun (_ m : ℕ) => (m.factorial : ℝ)) hf,
    Finsupp.sum_subtypeDomain_index (h := fun (_ m : ℕ) => m) hf]
    using convolution μ hμ d hd

end MetaMathlibExt
