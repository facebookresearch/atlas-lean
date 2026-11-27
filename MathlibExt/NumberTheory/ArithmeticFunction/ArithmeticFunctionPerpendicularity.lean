/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ArithmeticFunction.Antimultiplicative
public import MathlibExt.NumberTheory.RearickLogarithm

/-!
# Perpendicularities of arithmetical functions

This file proves preservation under real powers and unique multiplicative–antimultiplicative
factorization as in Pentti Haukkanen and Timo Tossavainen, *Some Perpendicularities of
Arithmetical Functions*, INTEGERS 25 (2025), Article A33.

Arithmetical functions are real-valued (`ArithmeticFunction ℝ`, whose multiplication is the
Dirichlet convolution and whose unit `1` is the paper's `δ`). `U` is the unit group, `U₁` the units
with `f 1 = 1`, `U_M` the multiplicative functions (Mathlib's `IsMultiplicative`) and `U_A` the
antimultiplicative functions (`IsAntimultiplicative`). The paper's real power `f^{(α)} = E(α Lf)`
(Rearick) is pinned by `L(f^{(α)}) = α L(f)`, with `L` the MathlibExt `rearickLog`.
-/

namespace MetaMathlibExt

open ArithmeticFunction

namespace dirichletRealPower_multiplicative_antimultiplicative_subspaces

private theorem mul_apply_prime_pow_congr_left {f g h : ArithmeticFunction ℝ} {p k : ℕ}
    (hp : p.Prime) (hfg : ∀ i, f (p ^ i) = g (p ^ i)) :
    (f * h) (p ^ k) = (g * h) (p ^ k) := by
  simp only [ArithmeticFunction.mul_apply]
  refine Finset.sum_congr rfl ?_
  rintro ⟨a, b⟩ hab
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp
    ⟨b, (Nat.mem_divisorsAntidiagonal.mp hab).1.symm⟩
  rw [hfg]

private theorem antimultiplicative_apply_prime_pow {f : ArithmeticFunction ℝ}
    (hf : IsAntimultiplicative f) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    f (p ^ k) = (1 : ArithmeticFunction ℝ) (p ^ k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using hf.1
  · rw [hf.2 p k hp hk, one_apply_ne (Nat.one_lt_pow hk.ne' hp.one_lt).ne']

private theorem isAntimultiplicative_iff_rearickLog {f : ArithmeticFunction ℝ} (hf : f 1 = 1)
    (hfpos : 0 < f 1) :
    IsAntimultiplicative f ↔ ∀ p k : ℕ, p.Prime → 0 < k → rearickLog f hfpos (p ^ k) = 0 := by
  have hlog : f * rearickLog f hfpos = f.pmul log := by
    rw [rearickLog_eq_pmul_log_mul_dirichletInverse f hfpos hf, mul_left_comm,
      ArithmeticFunction.self_mul_dirichletInverse, mul_one]
  constructor
  · intro ha p k hp hk
    calc
      rearickLog f hfpos (p ^ k) = (f * rearickLog f hfpos) (p ^ k) := by
        rw [mul_apply_prime_pow_congr_left hp (antimultiplicative_apply_prime_pow ha hp), one_mul]
      _ = 0 := by rw [hlog, pmul_apply, ha.2 p k hp hk, zero_mul]
  · intro ha
    refine ⟨hf, fun p k hp hk => ?_⟩
    have hzero (i : ℕ) : rearickLog f hfpos (p ^ i) = (0 : ArithmeticFunction ℝ) (p ^ i) := by
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp [hf]
      · simpa using ha p i hp hi
    have hm := mul_apply_prime_pow_congr_left (h := f) (k := k) hp hzero
    rw [mul_comm (rearickLog f hfpos) f, hlog, zero_mul, pmul_apply, log_apply, zero_apply] at hm
    have hpos : 0 < Real.log ((p ^ k : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast Nat.one_lt_pow hk.ne' hp.one_lt)
    exact (mul_eq_zero.mp hm).resolve_right hpos.ne'

end dirichletRealPower_multiplicative_antimultiplicative_subspaces

open dirichletRealPower_multiplicative_antimultiplicative_subspaces

/-- **Unique splitting into multiplicative and antimultiplicative parts.** Every real
arithmetical function $f$ with $f(1) = 1$ can be written in exactly one way as a Dirichlet
convolution $f = g * h$ of a multiplicative real arithmetical function $g$ and an
antimultiplicative real arithmetical function $h$.

In the source, writing $U_1$, $U_M$ and $U_A$ for the real arithmetical functions $f$ with
$f(1) = 1$, the multiplicative ones and the antimultiplicative ones, this is written
$U_1 = U_M \oplus U_A$.

Source: Pentti Haukkanen and Timo Tossavainen, *Some Perpendicularities of Arithmetical
Functions*, INTEGERS 25 (2025), Article A33, Proposition 2 (`integers-2025-A33-prop-2`). -/
public theorem existsUnique_multiplicative_mul_antimultiplicative
    (f : ArithmeticFunction ℝ) (hf : f 1 = 1) :
    ∃! gh : ArithmeticFunction ℝ × ArithmeticFunction ℝ,
      gh.1.IsMultiplicative ∧ IsAntimultiplicative gh.2 ∧ gh.1 * gh.2 = f := by
  -- The multiplicative factor is determined by the prime-power values of f.
  let g : ArithmeticFunction ℝ :=
    ⟨fun n => if n = 0 then 0 else n.factorization.prod (fun p k => f (p ^ k)), by simp⟩
  have hg_apply {n : ℕ} (hn : n ≠ 0) :
      g n = n.factorization.prod (fun p k => f (p ^ k)) := by
    simp [g, hn]
  have hg : g.IsMultiplicative := by
    refine IsMultiplicative.iff_ne_zero.mpr ⟨by simp [hg_apply Nat.one_ne_zero], ?_⟩
    intro m n hm hn hcop
    rw [hg_apply (mul_ne_zero hm hn), hg_apply hm, hg_apply hn,
      Nat.factorization_mul_of_coprime hcop, Finsupp.prod_add_index_of_disjoint
        hcop.disjoint_primeFactors]
  have hagree (p : ℕ) (hp : p.Prime) (k : ℕ) : g (p ^ k) = f (p ^ k) := by
    rw [hg_apply (pow_ne_zero _ hp.ne_zero), hp.factorization_pow,
      Finsupp.prod_single_index (by simpa using hf)]
  obtain ⟨u, hu⟩ :=
    (isUnit_iff_isUnit_apply_one.mpr (by simp [hg.map_one]) : IsUnit g)
  let h := (↑u⁻¹ : ArithmeticFunction ℝ) * f
  have hprod : (u : ArithmeticFunction ℝ) * h = f := by simp [h, ← mul_assoc]
  have hanti : IsAntimultiplicative h := by
    refine ⟨?_, fun p k hp hk => ?_⟩
    · have heq := congrArg (fun a : ArithmeticFunction ℝ => a 1) hprod
      simpa [mul_apply_one, hu, hg.map_one, hf] using heq
    · change ((↑u⁻¹ : ArithmeticFunction ℝ) * f) (p ^ k) = 0
      rw [mul_comm, ← mul_apply_prime_pow_congr_left hp (hagree p hp), ← hu, u.mul_inv,
        one_apply_ne (Nat.one_lt_pow hk.ne' hp.one_lt).ne']
  have humult : (u : ArithmeticFunction ℝ).IsMultiplicative := hu.symm ▸ hg
  refine ⟨(↑u, h), ⟨humult, hanti, hprod⟩, ?_⟩
  rintro ⟨g', h'⟩ ⟨hg', ha', heq⟩
  change g' * h' = f at heq
  have hg'eq : g' = (u : ArithmeticFunction ℝ) := by
    refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ hg' _ humult).mpr fun p k hp => ?_
    rw [hu, hagree p hp, ← heq, mul_comm g' h',
      mul_apply_prime_pow_congr_left hp (antimultiplicative_apply_prime_pow ha' hp), one_mul]
  subst g'
  exact Prod.ext rfl (u.isUnit.mul_left_cancel (heq.trans hprod.symm))

/-- **Real powers preserve multiplicativity and antimultiplicativity.** Let $L$ denote the
Rearick logarithm. Let $f$ and $F$ be real arithmetical functions with $f(1) = F(1) = 1$, and let
$\alpha$ be a real number with $L(F) = \alpha L(f)$. If $f$ is multiplicative, then $F$ is
multiplicative, and if $f$ is antimultiplicative, then $F$ is antimultiplicative. Moreover, every
real arithmetical function $f$ with $f(1) = 1$ can be written in exactly one way as a Dirichlet
convolution $f = g * h$ with $g$ multiplicative and $h$ antimultiplicative.

In the source $F$ is Rearick's real power $f^{(\alpha)}$, and the theorem says that the
multiplicative and the antimultiplicative functions with $f(1) = 1$ form subspaces of the real
vector space of all real arithmetical functions $f$ with $f(1) = 1$, whose direct sum is that space.

Source: Pentti Haukkanen and Timo Tossavainen, *Some Perpendicularities of Arithmetical
Functions*, INTEGERS 25 (2025), Article A33, Theorem 2 (`integers-2025-A33-thm-2`). -/
public theorem dirichletRealPower_multiplicative_antimultiplicative_subspaces :
    (∀ (f F : ArithmeticFunction ℝ) (α : ℝ), f 1 = 1 → F 1 = 1 →
        (∀ (hF : 0 < F 1) (hf : 0 < f 1), rearickLog F hF = α • rearickLog f hf) →
        (f.IsMultiplicative → F.IsMultiplicative) ∧
          (IsAntimultiplicative f → IsAntimultiplicative F)) ∧
      ∀ f : ArithmeticFunction ℝ, f 1 = 1 →
        ∃! gh : ArithmeticFunction ℝ × ArithmeticFunction ℝ,
          gh.1.IsMultiplicative ∧ IsAntimultiplicative gh.2 ∧ gh.1 * gh.2 = f := by
  refine ⟨?_, existsUnique_multiplicative_mul_antimultiplicative⟩
  intro f F α hf hF hscale
  have hfpos : 0 < f 1 := by simp [hf]
  have hFpos : 0 < F 1 := by simp [hF]
  have hscaled (n : ℕ) : rearickLog F hFpos n = α * rearickLog f hfpos n :=
    DFunLike.congr_fun (hscale hFpos hfpos) n
  constructor
  · intro hmult
    refine (rearick_log_eq_zero_iff_isMultiplicative F hFpos).2 fun n hn => ?_
    rw [hscaled, (rearick_log_eq_zero_iff_isMultiplicative f hfpos).1 hmult n hn, mul_zero]
  · intro hanti
    refine (isAntimultiplicative_iff_rearickLog hF hFpos).2 fun p k hp hk => ?_
    rw [hscaled, (isAntimultiplicative_iff_rearickLog hf hfpos).1 hanti p k hp hk, mul_zero]

end MetaMathlibExt
