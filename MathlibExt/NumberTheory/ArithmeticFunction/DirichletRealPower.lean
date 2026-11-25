/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

-- This import order preserves the scalar multiplication instance in the original statement.
public import Mathlib.Basic.Real.Basic
public import MathlibExt.NumberTheory.RearickLogarithm

/-!
# Real powers under Dirichlet convolution

Scaling the Rearick logarithm defines real powers of normalized arithmetic functions and
gives the scalar multiplication laws for Dirichlet convolution.
-/

namespace MetaMathlibExt

namespace DirichletRealPower

open ArithmeticFunction

local notation "AF" => ArithmeticFunction ℝ

-- Solve f(n) log n = (f * a)(n) recursively, starting with f(1) = 1.
private noncomputable def coefficient (a : AF) (n : ℕ) : ℝ :=
  if n = 1 then 1 else
    (∑ d : n.properDivisors,
      have : (d : ℕ) < n := (Nat.mem_properDivisors.mp d.property).2
      coefficient a d * a (n / d)) / Real.log n

private noncomputable def exp (a : AF) : AF :=
  ⟨coefficient a, by rw [coefficient]; simp⟩

private theorem exp_one (a : AF) : exp a 1 = 1 := by
  change coefficient a 1 = 1
  rw [coefficient, ite_eq_left rfl]

private theorem exp_apply (a : AF) {n : ℕ} (hn : 1 < n) :
    exp a n = (∑ d ∈ n.properDivisors, exp a d * a (n / d)) / Real.log n := by
  change coefficient a n = _
  rw [coefficient, ite_eq_right hn.ne']
  conv_rhs => rw [← Finset.sum_attach n.properDivisors, Finset.attach_eq_univ]
  rfl

private theorem equation_at {a f : AF} (ha : a 1 = 0) {n : ℕ} (hn : 1 < n) :
    (f.pmul log) n = (f * a) n ↔
      f n = (∑ d ∈ n.properDivisors, f d * a (n / d)) / Real.log n := by
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  have hlog := Real.log_pos (show (1 : ℝ) < n by exact_mod_cast hn)
  rw [eq_div_iff hlog.ne', pmul_apply, log_apply, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun d e => f d * a e), ← Nat.cons_self_properDivisors hn0.ne',
    Finset.sum_cons, Nat.div_self hn0, ha, mul_zero, zero_add]

private theorem exp_equation {a : AF} (ha : a 1 = 0) : (exp a).pmul log = exp a * a := by
  ext n
  match n with
  | 0 => simp
  | 1 => simp [pmul_apply, log_apply, ha]
  | n + 2 => exact (equation_at ha (by omega)).2 (exp_apply a (by omega))

private theorem eq_exp {f a : AF} (hf : f 1 = 1) (ha : a 1 = 0)
    (h : f.pmul log = f * a) : f = exp a := by
  ext n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases n with _ | _ | n
    · simp
    · rw [hf, exp_one]
    · have hn : 1 < n + 2 := by omega
      rw [(equation_at ha hn).1 (DFunLike.congr_fun h _), exp_apply a hn]
      congr 1
      exact Finset.sum_congr rfl fun d hd => by rw [ih d (Nat.mem_properDivisors.mp hd).2]

private theorem pmul_log_mul (f g : AF) :
    (f * g).pmul log = f.pmul log * g + f * g.pmul log := by
  ext n
  simp only [pmul_apply, log_apply, _root_.add_apply, ArithmeticFunction.mul_apply,
    Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← (Nat.mem_divisorsAntidiagonal.mp hd).1, Nat.cast_mul, Real.log_mul]
  · ring
  · exact_mod_cast Nat.left_ne_zero_of_mem_divisorsAntidiagonal hd
  · exact_mod_cast Nat.right_ne_zero_of_mem_divisorsAntidiagonal hd

-- Only normalized inputs matter for the power laws.
private noncomputable def normalizedLog (f : AF) : AF :=
  if h : f 1 = 1 then rearickLog f (by rw [h]; exact zero_lt_one) else 0

private theorem normalizedLog_eq {f : AF} (h : f 1 = 1) (hp : 0 < f 1) :
    normalizedLog f = rearickLog f hp := dite_eq_left h

private theorem normalizedLog_one (f : AF) : normalizedLog f 1 = 0 := by
  unfold normalizedLog
  split <;> simp_all

private theorem log_eq_iff {f a : AF} (hf : f 1 = 1) :
    normalizedLog f = a ↔ f.pmul log = f * a := by
  have hp : 0 < f 1 := by simp [hf]
  rw [normalizedLog_eq hf hp, rearickLog_eq_pmul_log_mul_dirichletInverse f hp hf]
  constructor
  · rintro rfl
    rw [mul_left_comm, self_mul_dirichletInverse, mul_one]
  · intro h
    rw [h, mul_right_comm, self_mul_dirichletInverse, one_mul]

private theorem log_mul {f g : AF} (hf : f 1 = 1) (hg : g 1 = 1) :
    normalizedLog (f * g) = normalizedLog f + normalizedLog g := by
  apply (log_eq_iff (by simp [hf, hg])).2
  rw [pmul_log_mul, (log_eq_iff hf).1 rfl, (log_eq_iff hg).1 rfl]
  ring

private theorem log_injective {f g : AF} (hf : f 1 = 1) (hg : g 1 = 1)
    (h : normalizedLog f = normalizedLog g) : f = g := by
  rw [eq_exp hf (normalizedLog_one f) ((log_eq_iff hf).1 rfl),
    eq_exp hg (normalizedLog_one g) ((log_eq_iff hg).1 rfl)]
  exact congrArg exp h

end DirichletRealPower

open DirichletRealPower

/-- **Rearick's real power and its vector space laws.** Let $L$ denote the Rearick logarithm and
$*$ the Dirichlet convolution. There is a map $(\alpha, f) \mapsto f^{(\alpha)}$, sending a real
number $\alpha$ and a real arithmetical function $f$ to a real arithmetical function, such that:
for every real $\alpha$ and every real arithmetical function $f$ with $f(1) = 1$, we have
$f^{(\alpha)}(1) = 1$ and $L(f^{(\alpha)}) = \alpha L(f)$; and for all real arithmetical functions
$f$, $g$ with $f(1) = g(1) = 1$ and all real $\alpha$, $\beta$, we have
$(f^{(\alpha)})^{(\beta)} = f^{(\alpha\beta)}$, $f^{(\alpha+\beta)} = f^{(\alpha)} * f^{(\beta)}$,
$(f * g)^{(\alpha)} = f^{(\alpha)} * g^{(\alpha)}$ and $f^{(1)} = f$.

In the source this is the statement that the real arithmetical functions $f$ with $f(1) = 1$ form
a real vector space, with Dirichlet convolution as addition and the real power as scalar
multiplication.

Source: Pentti Haukkanen and Timo Tossavainen, *Some Perpendicularities of Arithmetical
Functions*, INTEGERS 25 (2025), Article A33, Theorem 1 (`integers-2025-A33-thm-1`). -/
public theorem dirichletRealPower_vectorSpace :
    ∃ pow : ℝ → ArithmeticFunction ℝ → ArithmeticFunction ℝ,
      (∀ (α : ℝ) (f : ArithmeticFunction ℝ), f 1 = 1 → pow α f 1 = 1 ∧
        ∀ (hp : 0 < pow α f 1) (hf : 0 < f 1),
          rearickLog (pow α f) hp = α • rearickLog f hf) ∧
      ∀ f g : ArithmeticFunction ℝ, f 1 = 1 → g 1 = 1 → ∀ α β : ℝ,
        pow β (pow α f) = pow (α * β) f ∧ pow (α + β) f = pow α f * pow β f ∧
          pow α (f * g) = pow α f * pow α g ∧ pow 1 f = f := by
  let pow (α : ℝ) (f : ArithmeticFunction ℝ) := exp (α • normalizedLog f)
  have norm (α : ℝ) (f : ArithmeticFunction ℝ) : pow α f 1 = 1 := exp_one _
  have log_pow (α : ℝ) (f : ArithmeticFunction ℝ) :
      normalizedLog (pow α f) = α • normalizedLog f := by
    apply (log_eq_iff (norm α f)).2
    apply exp_equation
    change α * normalizedLog f 1 = 0
    rw [normalizedLog_one, mul_zero]
  refine ⟨pow, ?_, ?_⟩
  · intro α f hf
    refine ⟨norm α f, fun hp hf' => ?_⟩
    simpa only [normalizedLog_eq (norm α f) hp, normalizedLog_eq hf hf'] using log_pow α f
  · intro f g hf hg α β
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply log_injective (norm ..) (norm ..)
      simp only [log_pow, smul_smul, mul_comm β α]
    · apply log_injective (norm ..) (by simp [norm])
      simp only [log_mul (norm ..) (norm ..), log_pow]
      exact add_smul α β (normalizedLog f)
    · apply log_injective (norm ..) (by simp [norm])
      simp only [log_mul (norm ..) (norm ..), log_pow, log_mul hf hg]
      exact smul_add α (normalizedLog f) (normalizedLog g)
    · apply log_injective (norm ..) hf
      rw [log_pow, one_smul]

end MetaMathlibExt
