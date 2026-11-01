/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SelbergClass.Basic

/-!
# Primitive functions in the Selberg class and Selberg's conjectures

The Selberg class `𝒮` is closed under products (Dirichlet convolution of coefficients). A
function `F ∈ 𝒮` is *primitive* if `F ≠ 1` and `F` cannot be written as a product of two
functions of `𝒮` neither of which is `1`.

*Selberg's conjectures* describe the prime coefficients of primitive functions:
(a) `∑_{p ≤ x} |a_F(p)|² / p = log log x + O(1)` for primitive `F`, and
(b) `∑_{p ≤ x} a_F(p) conj (a_G(p)) / p = O(1)` for distinct primitive `F`, `G`.

## Main definitions

* `ArithmeticFunction.IsSelbergPrimitive a`: `a ∈ 𝒮` is primitive.
* `SelbergClass.ConjectureA`, `SelbergClass.ConjectureB`: Selberg's conjectures (a) and (b).

## Main statements

* `ArithmeticFunction.mul_apply_prime`: `(f * g)(p) = f(1) g(p) + f(p) g(1)` at primes.
* `SelbergClass.re_sum_prime_mul_conj_div_sub_isBigO`: under the conjectures, for primitive
  `g, h`, `Re ∑_{p ≤ x} g(p) conj (h(p)) / p = [g = h] log log x + O(1)`.
* `SelbergClass.sum_prime_norm_sq_div_sub_isBigO_of_eq_prod_pow`: under the conjectures, if
  `a = ∏ g^{e g}` over distinct primitive `g`, then
  `∑_{p ≤ x} |a(p)|² / p = (∑ e_g²) log log x + O(1)`.
-/

open Filter Asymptotics

@[expose] public section

namespace ArithmeticFunction

/-- Dirichlet convolution at a prime: `(f * g)(p) = f(1) g(p) + f(p) g(1)`. -/
theorem mul_apply_prime {R : Type*} [Semiring R] (f g : ArithmeticFunction R) {p : ℕ}
    (hp : p.Prime) : (f * g) p = f 1 * g p + f p * g 1 := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a * g b), hp.divisors,
    Finset.sum_pair hp.one_lt.ne, Nat.div_one, Nat.div_self hp.pos]

/-- `a ∈ 𝒮` is **primitive**: `a ≠ 1` (the identity of Dirichlet convolution), and whenever
`a = b * c` with `b, c ∈ 𝒮`, one of `b`, `c` is `1`. -/
def IsSelbergPrimitive (a : ArithmeticFunction ℂ) : Prop :=
  a ∈ selbergClass ∧ a ≠ 1 ∧
    ∀ b ∈ selbergClass, ∀ c ∈ selbergClass, a = b * c → b = 1 ∨ c = 1

end ArithmeticFunction

namespace SelbergClass

open ArithmeticFunction

/-- **Selberg's conjecture (a)**: for every primitive `a`,
`∑_{p ≤ x} |a(p)|² / p = log log x + O(1)` as `x → ∞`. -/
def ConjectureA : Prop :=
  ∀ a : ArithmeticFunction ℂ, IsSelbergPrimitive a →
    (fun x : ℝ => (∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊x⌋₊), ‖a p‖ ^ 2 / (p : ℝ))
        - Real.log (Real.log x)) =O[atTop] (fun _ => (1 : ℝ))

/-- **Selberg's conjecture (b)**: for distinct primitive `a`, `b`,
`∑_{p ≤ x} a(p) conj (b(p)) / p = O(1)` as `x → ∞`. -/
def ConjectureB : Prop :=
  ∀ a b : ArithmeticFunction ℂ, IsSelbergPrimitive a → IsSelbergPrimitive b → a ≠ b →
    (fun x : ℝ => ∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊x⌋₊),
        a p * starRingEnd ℂ (b p) / (p : ℂ)) =O[atTop] (fun _ => (1 : ℂ))

open Classical in
/-- Under Selberg's conjectures (a) and (b), for primitive `g, h`:
`Re ∑_{p ≤ x} g(p) conj (h(p)) / p - [g = h] log log x = O(1)`. -/
theorem re_sum_prime_mul_conj_div_sub_isBigO (hA : ConjectureA) (hB : ConjectureB)
    {g h : ArithmeticFunction ℂ} (hg : IsSelbergPrimitive g) (hh : IsSelbergPrimitive h) :
    (fun x : ℝ => (∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊x⌋₊),
        g p * starRingEnd ℂ (h p) / (p : ℂ)).re - (if g = h then Real.log (Real.log x) else 0))
      =O[atTop] (fun _ => (1 : ℝ)) := by
  by_cases hgh : g = h
  · subst hgh
    refine (hA g hg).congr_left (fun x => ?_)
    simp only [ite_true]
    congr 1
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_natCast,
      ← Complex.ofReal_div, Complex.ofReal_re]
  · have hb := hB g h hg hh hgh
    have h1 : (fun x : ℝ => (∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊x⌋₊),
          g p * starRingEnd ℂ (h p) / (p : ℂ)).re) =O[atTop]
        (fun x : ℝ => ∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊x⌋₊),
          g p * starRingEnd ℂ (h p) / (p : ℂ)) :=
      isBigO_of_le _ (fun x => by
        simp only [Real.norm_eq_abs]
        exact Complex.abs_re_le_norm _)
    have h2 : (fun _ : ℝ => (1 : ℂ)) =O[atTop] (fun _ => (1 : ℝ)) :=
      isBigO_of_le _ (fun x => by simp)
    refine ((h1.trans hb).trans h2).congr_left (fun x => ?_)
    simp [hgh]

/-- Powers at a prime: if `g 1 = 1` then `(g ^ n) 1 = 1` and `(g ^ n)(p) = n g(p)`. -/
private lemma pow_apply_one_and_prime {g : ArithmeticFunction ℂ} (hg : g 1 = 1) (n : ℕ) :
    (g ^ n) 1 = 1 ∧ ∀ p : ℕ, p.Prime → (g ^ n) p = (n : ℂ) * g p := by
  induction n with
  | zero =>
    refine ⟨by simp, fun p hp => ?_⟩
    simp [hp.one_lt.ne']
  | succ n ih =>
    rw [pow_succ]
    refine ⟨by rw [mul_apply_one, ih.1, hg, one_mul], fun p hp => ?_⟩
    rw [mul_apply_prime _ _ hp, ih.1, ih.2 p hp, hg]
    push_cast
    ring

/-- A finite product `∏ g^{e g}` of functions with `g 1 = 1` takes the value `1` at `1` and
`∑ e g · g(p)` at a prime `p`. -/
private lemma prod_pow_apply_one_and_prime (s : Finset (ArithmeticFunction ℂ))
    (e : ArithmeticFunction ℂ → ℕ) (hs : ∀ g ∈ s, g 1 = 1) :
    (∏ g ∈ s, g ^ e g) 1 = 1 ∧
      ∀ p : ℕ, p.Prime → (∏ g ∈ s, g ^ e g) p = ∑ g ∈ s, (e g : ℂ) * g p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simp, fun p hp => ?_⟩
    simp [hp.one_lt.ne']
  | insert g t hg ih =>
    have hg1 : g 1 = 1 := hs g (Finset.mem_insert_self g t)
    obtain ⟨i1, i2⟩ := ih (fun x hx => hs x (Finset.mem_insert_of_mem hx))
    obtain ⟨q1, q2⟩ := pow_apply_one_and_prime hg1 (e g)
    rw [Finset.prod_insert hg]
    refine ⟨by rw [mul_apply_one, q1, i1, one_mul], fun p hp => ?_⟩
    rw [mul_apply_prime _ _ hp, q1, i1, q2 p hp, i2 p hp, Finset.sum_insert hg]
    ring

/-- **Prime coefficients of a product of primitive functions.** Assuming Selberg's conjectures
(a) and (b), if `a = ∏_{g ∈ s} g ^ {e g}` is a product of distinct primitive functions, then
`∑_{p ≤ x} |a(p)|² / p = (∑_{g ∈ s} (e g)²) log log x + O(1)`. -/
theorem sum_prime_norm_sq_div_sub_isBigO_of_eq_prod_pow (hA : ConjectureA) (hB : ConjectureB)
    {a : ArithmeticFunction ℂ} {s : Finset (ArithmeticFunction ℂ)}
    {e : ArithmeticFunction ℂ → ℕ} (hs : ∀ g ∈ s, IsSelbergPrimitive g)
    (ha : a = ∏ g ∈ s, g ^ e g) :
    (fun x : ℝ => (∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊x⌋₊), ‖a p‖ ^ 2 / (p : ℝ))
        - (∑ g ∈ s, (e g : ℝ) ^ 2) * Real.log (Real.log x))
      =O[atTop] (fun _ => (1 : ℝ)) := by
  classical
  have hap : ∀ p : ℕ, p.Prime → a p = ∑ g ∈ s, (e g : ℂ) * g p := by
    intro p hp
    rw [ha]
    exact (prod_pow_apply_one_and_prime s e fun g hg => (hs g hg).1.1).2 p hp
  set P : ℝ → Finset ℕ := fun x => Finset.filter Nat.Prime (Finset.Iic ⌊x⌋₊) with hP
  set R : ArithmeticFunction ℂ → ArithmeticFunction ℂ → ℝ → ℝ := fun g h x =>
    (∑ p ∈ P x, g p * starRingEnd ℂ (h p) / (p : ℂ)).re with hR
  set D : ArithmeticFunction ℂ → ArithmeticFunction ℂ → ℝ → ℝ := fun g h x =>
    R g h x - (if g = h then Real.log (Real.log x) else 0) with hD
  have hDO : ∀ g ∈ s, ∀ h ∈ s, D g h =O[atTop] (fun _ => (1 : ℝ)) :=
    fun g hg h hh => re_sum_prime_mul_conj_div_sub_isBigO hA hB (hs g hg) (hs h hh)
  refine (IsBigO.sum (fun g hg => IsBigO.sum (fun h hh =>
    (hDO g hg h hh).const_mul_left ((e g : ℝ) * e h)))).congr_left (fun x => ?_)
  have key : ∀ p ∈ P x, ‖a p‖ ^ 2 / (p : ℝ) = ∑ g ∈ s, ∑ h ∈ s,
      (e g : ℝ) * e h * (g p * starRingEnd ℂ (h p) / (p : ℂ)).re := by
    intro p hp
    have hpp : p.Prime := (Finset.mem_filter.1 hp).2
    rw [hap p hpp]
    have : (‖∑ g ∈ s, (e g : ℂ) * g p‖ ^ 2 / (p : ℝ) : ℝ) =
        ((∑ g ∈ s, (e g : ℂ) * g p) * starRingEnd ℂ (∑ g ∈ s, (e g : ℂ) * g p) /
          (p : ℂ)).re := by
      rw [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_natCast,
        ← Complex.ofReal_div, Complex.ofReal_re]
    rw [this, map_sum, Finset.sum_mul_sum, Finset.sum_div, Complex.re_sum]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [Finset.sum_div, Complex.re_sum]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    rw [map_mul, Complex.conj_natCast]
    have : (e g : ℂ) * g p * ((e h : ℂ) * starRingEnd ℂ (h p)) / (p : ℂ) =
        (((e g : ℝ) * e h : ℝ) : ℂ) * (g p * starRingEnd ℂ (h p) / (p : ℂ)) := by
      push_cast; ring
    rw [this, Complex.re_ofReal_mul]
  have hdiag : ∑ g ∈ s, ∑ h ∈ s, (e g : ℝ) * e h *
      (if g = h then Real.log (Real.log x) else 0) =
      (∑ g ∈ s, (e g : ℝ) ^ 2) * Real.log (Real.log x) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun g hg => ?_)
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq s g, ite_eq_left hg]
    ring
  have hoff : ∑ g ∈ s, ∑ h ∈ s, (e g : ℝ) * e h * R g h x =
      ∑ p ∈ P x, ‖a p‖ ^ 2 / (p : ℝ) := by
    symm
    rw [Finset.sum_congr rfl key, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    simp only [hR, Complex.re_sum, Finset.mul_sum]
  simp only [Finset.sum_apply]
  rw [← hdiag, ← hoff, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  simp only [hD]
  ring

end SelbergClass
