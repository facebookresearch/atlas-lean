/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs

/-!
# Antimultiplicative arithmetic functions

This file defines antimultiplicative arithmetic functions and proves that the multiplicative and
antimultiplicative Dirichlet units form subgroups whose intersection is trivial.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Antimultiplicative arithmetical functions.** Let $R$ be a type with a zero and a one. An
arithmetical function $f$ with values in $R$ is antimultiplicative if $f(1) = 1$ and $f(p^k) = 0$
for every prime $p$ and every integer $k \ge 1$.

Source: Pentti Haukkanen and Timo Tossavainen, *Some Perpendicularities of Arithmetical
Functions*, INTEGERS 25 (2025), Article A33, Section 2. -/
def IsAntimultiplicative {R : Type*} [Zero R] [One R] (f : ArithmeticFunction R) : Prop :=
  f 1 = 1 ∧ ∀ p k : ℕ, p.Prime → 0 < k → f (p ^ k) = 0

/-- **The Dirichlet identity is antimultiplicative.** For every semiring $R$, the identity
$\delta$ of Dirichlet convolution on arithmetical functions with values in $R$, given by
$\delta(1) = 1$ and $\delta(n) = 0$ for $n \ne 1$, is antimultiplicative.

Source: Pentti Haukkanen and Timo Tossavainen, *Some Perpendicularities of Arithmetical
Functions*, INTEGERS 25 (2025), Article A33, Section 2. -/
theorem isAntimultiplicative_one {R : Type*} [Semiring R] :
    IsAntimultiplicative (1 : ArithmeticFunction R) := by
  refine ⟨ArithmeticFunction.one_one, fun p k hp hk => ?_⟩
  exact ArithmeticFunction.one_apply_ne (Nat.one_lt_pow hk.ne' hp.one_lt).ne'

/-- **Antimultiplicative functions vanish at primes.** Let $R$ be a type with a zero and a one, and
let $f$ be an antimultiplicative arithmetical function with values in $R$. Then $f(p) = 0$ for
every prime $p$.

Source: Pentti Haukkanen and Timo Tossavainen, *Some Perpendicularities of Arithmetical
Functions*, INTEGERS 25 (2025), Article A33, Section 2. -/
theorem IsAntimultiplicative.apply_prime {R : Type*} [Zero R] [One R] {f : ArithmeticFunction R}
    (hf : IsAntimultiplicative f) {p : ℕ} (hp : p.Prime) : f p = 0 := by
  simpa using hf.2 p 1 hp one_pos

end

namespace dirichletUnits_multiplicative_antimultiplicative_subgroups

open ArithmeticFunction

private theorem mul_apply_prime_pow_congr {f g f' g' : ArithmeticFunction ℝ} {p k : ℕ}
    (hp : p.Prime) (hf : ∀ i, f (p ^ i) = f' (p ^ i))
    (hg : ∀ i, g (p ^ i) = g' (p ^ i)) :
    (f * g) (p ^ k) = (f' * g') (p ^ k) := by
  simp only [ArithmeticFunction.mul_apply]
  refine Finset.sum_congr rfl ?_
  rintro ⟨a, b⟩ hab
  have heq := (Nat.mem_divisorsAntidiagonal.mp hab).1
  obtain ⟨i, -, ha⟩ := (Nat.dvd_prime_pow hp).mp ⟨b, heq.symm⟩
  obtain ⟨j, -, hb⟩ := (Nat.dvd_prime_pow hp).mp ⟨a, heq.symm.trans (mul_comm a b)⟩
  rw [ha, hb, hf, hg]

private theorem inv_apply_one {u : (ArithmeticFunction ℝ)ˣ}
    (hu : (u : ArithmeticFunction ℝ) 1 = 1) :
    (↑u⁻¹ : ArithmeticFunction ℝ) 1 = 1 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f 1) u.mul_inv
  rwa [mul_apply_one, hu, one_mul, one_one] at h

private theorem eq_one_on_prime_powers {f : ArithmeticFunction ℝ} (hf : IsAntimultiplicative f)
    {p : ℕ} (hp : p.Prime) (k : ℕ) : f (p ^ k) = (1 : ArithmeticFunction ℝ) (p ^ k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa only [pow_zero, one_one] using hf.1
  · rw [hf.2 p k hp hk, one_apply_ne (Nat.one_lt_pow hk.ne' hp.one_lt).ne']

private theorem isMultiplicative_inv {u : (ArithmeticFunction ℝ)ˣ}
    (hu : (u : ArithmeticFunction ℝ).IsMultiplicative) :
    (↑u⁻¹ : ArithmeticFunction ℝ).IsMultiplicative := by
  let g : ArithmeticFunction ℝ := ↑u⁻¹
  -- Extend the inverse's prime-power values multiplicatively, then use uniqueness of inverses.
  let F : ArithmeticFunction ℝ :=
    ⟨fun n => if n = 0 then 0 else n.factorization.prod (fun p k => g (p ^ k)), by simp⟩
  have hF {n : ℕ} (hn : n ≠ 0) : F n = n.factorization.prod (fun p k => g (p ^ k)) := by
    simp [F, hn]
  have hmult : F.IsMultiplicative := by
    refine IsMultiplicative.iff_ne_zero.mpr ⟨by simp [hF Nat.one_ne_zero], ?_⟩
    intro m n hm hn hcop
    rw [hF (mul_ne_zero hm hn), hF hm, hF hn, Nat.factorization_mul_of_coprime hcop,
      Finsupp.prod_add_index_of_disjoint hcop.disjoint_primeFactors]
  have hg₁ : g 1 = 1 := inv_apply_one hu.map_one
  have hpower (p : ℕ) (hp : p.Prime) (k : ℕ) : F (p ^ k) = g (p ^ k) := by
    rw [hF (pow_ne_zero _ hp.ne_zero), hp.factorization_pow,
      Finsupp.prod_single_index (by simpa only [pow_zero] using hg₁)]
  have hprod : (u : ArithmeticFunction ℝ) * F = 1 := by
    refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ (hu.mul hmult) _
      isMultiplicative_one).mpr fun p k hp => ?_
    calc
      ((u : ArithmeticFunction ℝ) * F) (p ^ k) =
          ((u : ArithmeticFunction ℝ) * g) (p ^ k) :=
        mul_apply_prime_pow_congr hp (fun _ => rfl) (hpower p hp)
      _ = (1 : ArithmeticFunction ℝ) (p ^ k) :=
        congrArg (fun f : ArithmeticFunction ℝ => f (p ^ k)) u.mul_inv
  have hg : g = F := by
    rw [← u.inv_mul_cancel_left F, hprod, mul_one]
  change g.IsMultiplicative
  exact hg.symm ▸ hmult

end dirichletUnits_multiplicative_antimultiplicative_subgroups

open ArithmeticFunction
open dirichletUnits_multiplicative_antimultiplicative_subgroups

/-- **Multiplicative and antimultiplicative units form subgroups.** Let $U$ be the group of units
of the ring of real arithmetical functions under Dirichlet convolution. The units $f$ with
$f(1) = 1$, the multiplicative units and the antimultiplicative units form subgroups $U_1$, $U_M$
and $U_A$ of $U$, respectively. Moreover $U_M \le U_1$, $U_A \le U_1$ and
$U_M \cap U_A = \{\delta\}$, where $\delta$ is the Dirichlet identity.

Source: Pentti Haukkanen and Timo Tossavainen, *Some Perpendicularities of Arithmetical
Functions*, INTEGERS 25 (2025), Article A33, Proposition 1 (`integers-2025-A33-prop-1`). -/
public theorem dirichletUnits_multiplicative_antimultiplicative_subgroups :
    ∃ U₁ UM UA : Subgroup (ArithmeticFunction ℝ)ˣ,
      (∀ u, u ∈ U₁ ↔ (u : ArithmeticFunction ℝ) 1 = 1) ∧
      (∀ u, u ∈ UM ↔ (u : ArithmeticFunction ℝ).IsMultiplicative) ∧
      (∀ u, u ∈ UA ↔ IsAntimultiplicative (u : ArithmeticFunction ℝ)) ∧
      UM ≤ U₁ ∧ UA ≤ U₁ ∧ UM ⊓ UA = ⊥ := by
  let U₁ : Subgroup (ArithmeticFunction ℝ)ˣ :=
    { carrier := {u | (u : ArithmeticFunction ℝ) 1 = 1}
      one_mem' := one_one
      mul_mem' := by
        intro u v hu hv
        simp only [Set.mem_ofPred_eq, Units.val_mul, mul_apply_one] at hu hv ⊢
        rw [hu, hv, mul_one]
      inv_mem' := inv_apply_one }
  let UM : Subgroup (ArithmeticFunction ℝ)ˣ :=
    { carrier := {u | (u : ArithmeticFunction ℝ).IsMultiplicative}
      one_mem' := isMultiplicative_one
      mul_mem' := fun ha hb => IsMultiplicative.mul ha hb
      inv_mem' := isMultiplicative_inv }
  let UA : Subgroup (ArithmeticFunction ℝ)ˣ :=
    { carrier := {u | IsAntimultiplicative (u : ArithmeticFunction ℝ)}
      one_mem' := isAntimultiplicative_one
      mul_mem' := by
        intro u v hu hv
        change IsAntimultiplicative (↑u * ↑v : ArithmeticFunction ℝ)
        refine ⟨by rw [mul_apply_one, hu.1, hv.1, mul_one], fun p k hp hk => ?_⟩
        rw [mul_apply_prime_pow_congr hp (eq_one_on_prime_powers hu hp)
          (eq_one_on_prime_powers hv hp), one_mul,
          one_apply_ne (Nat.one_lt_pow hk.ne' hp.one_lt).ne']
      inv_mem' := by
        intro u hu
        change IsAntimultiplicative (↑u⁻¹ : ArithmeticFunction ℝ)
        refine ⟨inv_apply_one hu.1, fun p k hp hk => ?_⟩
        have h := mul_apply_prime_pow_congr (k := k) hp (eq_one_on_prime_powers hu hp)
          (g := (↑u⁻¹ : ArithmeticFunction ℝ)) (fun _ => rfl)
        rw [u.mul_inv, one_mul, one_apply_ne (Nat.one_lt_pow hk.ne' hp.one_lt).ne'] at h
        exact h.symm }
  refine ⟨U₁, UM, UA, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl,
    fun _ h => IsMultiplicative.map_one h, fun _ h => h.1, ?_⟩
  rw [Subgroup.eq_bot_iff_forall]
  intro u hu
  exact Units.ext ((IsMultiplicative.eq_iff_eq_on_prime_powers _
    (Subgroup.mem_inf.mp hu).1 _ isMultiplicative_one).mpr fun _ k hp =>
      eq_one_on_prime_powers (Subgroup.mem_inf.mp hu).2 hp k)

end MetaMathlibExt
