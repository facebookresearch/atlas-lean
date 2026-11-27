/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.MobiusFermat
import Mathlib.Data.Finsupp.Multiset
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.RingTheory.MvPowerSeries.Derivative
import MathlibExt.NumberTheory.BangZsigmondy

/-!
# Reduction of the Möbius–Fermat function to distinct factors

With the powers of three and seven fixed, replacing repeated Mersenne factors of indices at
least four, excluding six, by equally many distinct admissible factors multiplies the
Möbius–Fermat function by the product of the multiplicity factorials.
-/

open ArithmeticFunction Finsupp Finset MvPowerSeries

namespace MetaMathlibExt
namespace mobiusFermat_mul_factorial_eq_squarefree_part

private abbrev Index := {n : ℕ // 2 ≤ n ∧ n ≠ 6}

private def value (d : Index →₀ ℕ) : ℕ := d.prod fun i m => mersenne i ^ m

private theorem gen_pos (i : Index) : 0 < mersenne i :=
  mersenne_pos.mpr (lt_of_lt_of_le (by decide : 0 < 2) i.2.1)

private theorem value_ne_zero (d : Index →₀ ℕ) : value d ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (gen_pos i).ne'

@[simp] private theorem value_zero : value 0 = 1 := by simp [value]

@[simp] private theorem value_add (a b : Index →₀ ℕ) : value (a + b) = value a * value b :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add ..)

@[simp] private theorem value_single (i : Index) (m : ℕ) :
    value (single i m) = mersenne i ^ m := Finsupp.prod_single_index (pow_zero _)

private theorem primitive (i : Index) :
    ∃ p : ℕ, 0 < (mersenne i).factorization p ∧
      ∀ j : Index, j < i → (mersenne j).factorization p = 0 := by
  by_cases hi : i.val = 2
  · refine ⟨3, ?_, fun j hj => ?_⟩
    · rw [hi]
      exact Nat.prime_three.factorization_pos_of_dvd (by decide) (by decide)
    · have := j.2.1
      change j.val < i.val at hj
      omega
  have hexc : ¬ IsBangZsigmondyExceptional 2 1 i := by
    rintro (⟨_, _, h⟩ | ⟨h, _⟩)
    · exact i.2.2 h
    · exact hi h
  obtain ⟨p, hp⟩ := bangZsigmondy_exists_primitivePrimeDivisor (by decide : 0 < 1)
    (by decide : 1 < 2) (by decide) i.2.1 hexc
  have cast_dvd (n : ℕ) : p ∣ mersenne n ↔ (p : ℤ) ∣ (2 : ℤ) ^ n - (1 : ℤ) ^ n := by
    rw [← Int.natCast_dvd_natCast, mersenne, Nat.cast_sub Nat.one_le_two_pow]
    simp
  exact ⟨p, hp.prime.factorization_pos_of_dvd (gen_pos i).ne' ((cast_dvd i).mpr hp.dvd),
    fun j hj => Nat.factorization_eq_zero_of_not_dvd fun h =>
      hp.not_dvd_of_lt (le_trans (by decide : 1 ≤ 2) j.2.1) hj ((cast_dvd j).mp h)⟩

-- A primitive prime reads off the multiplicity of the largest index still in the product.
private theorem value_injective : Function.Injective value := by
  classical
  intro f g h
  have unique (s : Finset Index)
      (heq : (∏ i ∈ s, mersenne i ^ f i) = ∏ i ∈ s, mersenne i ^ g i) :
      ∀ i ∈ s, f i = g i := by
    induction s using Finset.induction_on_max with
    | empty => simp
    | insert a s hlt ih =>
      have ha : a ∉ s := fun ha => (lt_irrefl a) (hlt a ha)
      obtain ⟨p, hp, hprev⟩ := primitive a
      have valuation (d : Index →₀ ℕ) :
          (∏ i ∈ insert a s, mersenne i ^ d i).factorization p =
            d a * (mersenne a).factorization p := by
        rw [Nat.factorization_prod_apply (fun i _ => pow_ne_zero _ (gen_pos i).ne')]
        simp only [Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
          Finset.sum_insert ha]
        rw [Finset.sum_eq_zero (fun i hi => by rw [hprev i (hlt i hi), mul_zero]), add_zero]
      have hm := congrArg (fun n : ℕ => n.factorization p) heq
      rw [valuation, valuation] at hm
      have hab : f a = g a := Nat.eq_of_mul_eq_mul_right hp hm
      rw [Finset.prod_insert ha, Finset.prod_insert ha, hab] at heq
      exact fun i hi => (Finset.mem_insert.mp hi).elim (fun e => e ▸ hab)
        (ih (Nat.eq_of_mul_eq_mul_left (pow_pos (gen_pos a) _) heq) i)
  let s := f.support ∪ g.support
  rw [value, value, f.prod_of_support_subset (s := s) Finset.subset_union_left _ (by simp),
    g.prod_of_support_subset (s := s) Finset.subset_union_right _ (by simp)] at h
  ext i
  by_cases hi : i ∈ s
  · exact unique s h i hi
  · simp only [s, Finset.mem_union, not_or] at hi
    simp [Finsupp.notMem_support_iff.mp hi.1, Finsupp.notMem_support_iff.mp hi.2]

private abbrev two : Index := ⟨2, by decide⟩
private abbrev three : Index := ⟨3, by decide⟩

private noncomputable def base (a b : ℕ) : Index →₀ ℕ := single two a + single three b

private theorem value_base (a b : ℕ) : value (base a b) = 3 ^ a * 7 ^ b := by
  simp only [base, value_add, value_single]
  rfl

private theorem base_apply {i : Index} (hi : 4 ≤ i.val) (a b : ℕ) : base a b i = 0 := by
  have h2 : two ≠ i := ne_of_lt (show two.val < i.val from lt_of_lt_of_le (by decide) hi)
  have h3 : three ≠ i := ne_of_lt (show three.val < i.val from lt_of_lt_of_le (by decide) hi)
  simp [base, h2, h3]

private theorem generator_cases {n : ℕ} (hn : 1 ≤ n) :
    mersenne n = 1 ∨ mersenne n = value (base 2 1) ∨ ∃ i : Index, mersenne n = mersenne i := by
  by_cases h1 : n = 1
  · subst n; exact Or.inl rfl
  by_cases h6 : n = 6
  · subst n; exact Or.inr (Or.inl (by rw [value_base]; decide))
  exact Or.inr (Or.inr ⟨⟨n, by omega, h6⟩, rfl⟩)

private theorem unit_index {x : ℕ} (hx : fermatUnitFunction x ≠ 0) :
    ∃ n : ℕ, 1 ≤ n ∧ x = mersenne n := by
  change (if x ≠ 0 ∧ _ then (1 : ℤ) else 0) ≠ 0 at hx
  split at hx
  next h =>
    obtain ⟨hx0, h⟩ := h
    refine ⟨Nat.log 2 (x + 1), ?_, by simp [mersenne, h]⟩
    by_contra! hlog
    have hz : Nat.log 2 (x + 1) = 0 := by omega
    simp [hz] at h
    omega
  next => contradiction

private theorem generator_in_range {n : ℕ} (hn : 1 ≤ n) : mersenne n ∈ Set.range value := by
  rcases generator_cases hn with h | h | ⟨i, h⟩
  · exact ⟨0, by simpa using h.symm⟩
  · exact ⟨_, h.symm⟩
  · exact ⟨single i 1, by simpa using h.symm⟩

private theorem inverse_in_range (μ : ArithmeticFunction ℤ) (hμ : μ * fermatUnitFunction = 1)
    {x : ℕ} (hx : μ x ≠ 0) : x ∈ Set.range value := by
  have hmem : x ∈ Submonoid.closure {y : ℕ | ∃ n, 2 ≤ n ∧ y = 2 ^ n - 1} := by
    by_contra h
    exact hx ((mobiusFermat_one_and_vanishing μ hμ).2.2 x h).1
  refine Submonoid.closure_induction (motive := fun y _ => y ∈ Set.range value) ?_
    ⟨0, value_zero⟩ ?_ hmem
  · rintro _ ⟨n, hn, rfl⟩
    exact generator_in_range (by omega : 1 ≤ n)
  · rintro _ _ _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, value_add a b⟩

private def series (u : ArithmeticFunction ℤ) : MvPowerSeries Index ℤ := fun d => u (value d)

-- Only pairs of divisors in the Fermat semigroup contribute to the convolution.
-- Unique representation identifies these pairs with pairs of exponent vectors summing to d.
private theorem series_mul_unit (μ : ArithmeticFunction ℤ) (hμ : μ * fermatUnitFunction = 1) :
    series μ * series fermatUnitFunction = 1 := by
  classical
  ext d
  rw [coeff_mul, coeff_one]
  have h1 : value d = 1 ↔ d = 0 := by rw [← value_zero, value_injective.eq_iff]
  simp only [← h1]
  rw [← ArithmeticFunction.one_apply, ← hμ, ArithmeticFunction.mul_apply]
  let e (p : (Index →₀ ℕ) × (Index →₀ ℕ)) := (value p.1, value p.2)
  apply Finset.sum_of_injOn e (value_injective.prodMap value_injective).injOn
  · intro p hp
    exact Nat.mem_divisorsAntidiagonal.mpr
      ⟨(value_add ..).symm.trans (congrArg value (Finset.mem_antidiagonal.mp hp)), value_ne_zero d⟩
  · rintro ⟨a, b⟩ hab hout
    by_contra! h
    obtain ⟨u, rfl⟩ := inverse_in_range μ hμ (left_ne_zero_of_mul h)
    obtain ⟨n, hn, rfl⟩ := unit_index (right_ne_zero_of_mul h)
    obtain ⟨v, hv⟩ := generator_in_range hn
    apply hout
    refine ⟨(u, v), Finset.mem_antidiagonal.mpr (value_injective ?_), by simp [e, hv]⟩
    rw [value_add, hv]
    exact (Nat.mem_divisorsAntidiagonal.mp hab).1
  · intros; rfl

-- Apart from the monomial for 63, every nonconstant monomial of the unit function
-- is a single variable. In each variable of index at least four its derivative is one.
private theorem derivative_unit (i : Index) (hi : 4 ≤ i.val) :
    pderiv i (series fermatUnitFunction) = 1 := by
  classical
  ext d
  rw [coeff_pderiv, coeff_one]
  change fermatUnitFunction (value (d + single i 1)) * _ = _
  by_cases hd : d = 0
  · subst d
    simp [fermatUnitFunction_two_pow_sub_one (show 1 ≤ i.val by omega), mersenne]
  simp only [hd, ite_false]
  suffices fermatUnitFunction (value (d + single i 1)) = 0 by rw [this, zero_mul]
  by_contra h
  obtain ⟨n, hn, he⟩ := unit_index h
  rcases generator_cases hn with h1 | h6 | ⟨j, hj⟩
  · have eq := value_injective ((he.trans h1).trans value_zero.symm)
    simpa using congrArg (fun f : Index →₀ ℕ => f i) eq
  · have eq := value_injective (he.trans h6)
    simpa [base_apply hi] using congrArg (fun f : Index →₀ ℕ => f i) eq
  · have eq : d + single i 1 = single j 1 := value_injective (by simpa using he.trans hj)
    by_cases hij : j = i
    · subst j
      exact hd (add_right_cancel (b := single i 1) (by simpa only [zero_add] using eq))
    · simpa [Finsupp.single_apply, hij] using congrArg (fun f : Index →₀ ℕ => f i) eq

private theorem derivative_power {u : MvPowerSeries Index ℤ}
    (hu : u * series fermatUnitFunction = 1) (i : Index) (hi : 4 ≤ i.val) (r : ℕ) :
    pderiv i (u ^ (r + 1)) = -((r + 1) • u ^ (r + 2)) := by
  rw [pderiv_pow, (pderiv i).leibniz_of_mul_eq_one hu, derivative_unit i hi, smul_eq_mul,
    mul_one, Nat.add_sub_cancel, nsmul_eq_mul, pow_add u r 2]
  ring

private def factorials (f : Index →₀ ℕ) : ℤ := f.prod fun _ m => (m.factorial : ℤ)

private theorem factorials_succ (f : Index →₀ ℕ) (i : Index) :
    factorials (f + single i 1) = (f i + 1 : ℤ) * factorials f := by
  let g (_ : Index) (m : ℕ) := (m.factorial : ℤ)
  have hg (j : Index) : g j 0 = 1 := rfl
  change (f + single i 1).prod g = _ * f.prod g
  rw [← Finsupp.mul_prod_erase' (f + single i 1) i g hg, ← Finsupp.mul_prod_erase' f i g hg]
  simp [g, Nat.factorial_succ, mul_assoc]

-- Each differentiation uses one of the remaining factors. Its effect depends only
-- on the current power of the inverse, so the normalized coefficient depends only on the count.
private noncomputable def iterCoeff (u : MvPowerSeries Index ℤ) (b : Index →₀ ℕ) :
    ℕ → ℕ → ℤ
  | 0, r => coeff b (u ^ (r + 1))
  | k + 1, r => -((r + 1 : ℕ) : ℤ) * iterCoeff u b k (r + 1)

private theorem normalized_coeff {u : MvPowerSeries Index ℤ}
    (hu : u * series fermatUnitFunction = 1) (a b : ℕ) (f : Index →₀ ℕ)
    (hf : ∀ i ∈ f.support, 4 ≤ i.val) (r : ℕ) :
    coeff (base a b + f) (u ^ (r + 1)) * factorials f =
      iterCoeff u (base a b) (f.sum fun _ => id) r := by
  classical
  obtain ⟨s, rfl⟩ := Multiset.toFinsupp.surjective f
  rw [Multiset.toFinsupp_sum_eq]
  induction s using Multiset.induction generalizing r with
  | empty => simp [Multiset.toFinsupp_zero, factorials, iterCoeff]
  | cons i s ih =>
    have hi : 4 ≤ i.val := hf i (by simp)
    have hs : ∀ j ∈ s.toFinsupp.support, 4 ≤ j.val := by
      intro j hj
      apply hf j
      simpa using (Or.inr (show j ∈ s by simpa using hj) : j = i ∨ j ∈ s)
    have h := congrArg (coeff (base a b + s.toFinsupp)) (derivative_power hu i hi r)
    rw [coeff_pderiv, map_neg, map_nsmul, nsmul_eq_mul] at h
    simp only [Finsupp.add_apply, base_apply hi, zero_add] at h
    rw [Multiset.card_cons, iterCoeff, ← ih (r + 1) hs]
    rw [← Multiset.singleton_add, add_comm ({i} : Multiset Index) s, Multiset.toFinsupp_add,
      Multiset.toFinsupp_singleton, factorials_succ, ← add_assoc, ← mul_assoc, h]
    ring

private theorem normalized_value (μ : ArithmeticFunction ℤ) (hμ : μ * fermatUnitFunction = 1)
    (a b : ℕ) (f : ℕ →₀ ℕ) (hf : ∀ n ∈ f.support, 4 ≤ n ∧ n ≠ 6) :
    μ (3 ^ a * 7 ^ b * f.prod fun n m => (2 ^ n - 1) ^ m) *
        (f.prod fun _ m => (m.factorial : ℤ)) =
      iterCoeff (series μ) (base a b) (f.sum fun _ => id) 0 := by
  have hadm (n : ℕ) (hn : n ∈ f.support) : 2 ≤ n ∧ n ≠ 6 :=
    ⟨le_trans (by decide : 2 ≤ 4) (hf n hn).1, (hf n hn).2⟩
  let d := f.subtypeDomain fun n => 2 ≤ n ∧ n ≠ 6
  have hd (i : Index) (hi : i ∈ d.support) : 4 ≤ i.val :=
    (hf i (Finsupp.mem_support_iff.mpr (show d i ≠ 0 from Finsupp.mem_support_iff.mp hi))).1
  have h := normalized_coeff (series_mul_unit μ hμ) a b d hd 0
  simp only [zero_add, pow_one] at h
  change μ (value (base a b + d)) * factorials d = _ at h
  rw [value_add, value_base] at h
  simpa only [value, factorials, d, mersenne,
    Finsupp.prod_subtypeDomain_index (h := fun (n m : ℕ) => (2 ^ n - 1) ^ m) hadm,
    Finsupp.prod_subtypeDomain_index (h := fun (_ m : ℕ) => (m.factorial : ℤ)) hadm,
    Finsupp.sum_subtypeDomain_index (h := fun _ : ℕ => id) hadm] using h

end mobiusFermat_mul_factorial_eq_squarefree_part

open mobiusFermat_mul_factorial_eq_squarefree_part in
/-- **Reduction of the Möbius–Fermat function to distinct factors.** Let $u_M$ be the Fermat
unit function and let $\mu_M$ be an integer-valued arithmetic function with
$\mu_M * u_M = \varepsilon$, where $*$ is Dirichlet convolution and $\varepsilon$ is its
identity, with $\varepsilon(1) = 1$ and $\varepsilon(l) = 0$ for $l \ne 1$; thus $\mu_M$ is the
Dirichlet inverse of $u_M$, the Möbius–Fermat function.
Let $m_1, m_2 \ge 0$ be integers, let $n_3, \dots, n_k$ be finitely many (possibly no) distinct
integers with $n_j \ge 4$ and $n_j \ne 6$, let $m_3, \dots, m_k \ge 1$ be integers, and put
$l = 3^{m_1} 7^{m_2} \prod_{j=3}^{k} (2^{n_j} - 1)^{m_j}$.
Then for every finite set $T$ of integers $n \ge 4$ with $n \ne 6$ and
$|T| = m_3 + \dots + m_k$,
$$\mu_M(l) \, m_3! \cdots m_k! = \mu_M\Big(3^{m_1} 7^{m_2} \prod_{n \in T} (2^n - 1)\Big).$$
In particular the right-hand side does not depend on the choice of $T$.

Source: J. L. Varona, *The Möbius and the von Mangoldt-type Functions of the Fermat Zeta
Function*, INTEGERS 26 (2026), Article A106, Proposition 6. -/
public theorem mobiusFermat_mul_factorial_eq_squarefree_part (μ : ArithmeticFunction ℤ)
    (hμ : μ * fermatUnitFunction = 1) (m₁ m₂ : ℕ) (f : ℕ →₀ ℕ)
    (hf : ∀ n ∈ f.support, 4 ≤ n ∧ n ≠ 6) (T : Finset ℕ) (hT : ∀ n ∈ T, 4 ≤ n ∧ n ≠ 6)
    (hcard : T.card = f.sum fun _ m => m) :
    μ (3 ^ m₁ * 7 ^ m₂ * f.prod fun n m => (2 ^ n - 1) ^ m) *
        (f.prod fun _ m => (m.factorial : ℤ)) =
      μ (3 ^ m₁ * 7 ^ m₂ * ∏ n ∈ T, (2 ^ n - 1)) := by
  let g := Finsupp.indicator T fun _ _ => (1 : ℕ)
  have hg (n : ℕ) (hn : n ∈ g.support) := hT n (Finsupp.support_indicator_subset _ _ hn)
  have h := normalized_value μ hμ m₁ m₂ g hg
  dsimp only [g] at h
  rw [Finsupp.prod_indicator_index (h := fun n m : ℕ => (2 ^ n - 1) ^ m)
      (fun _ => 1) (by simp),
    Finsupp.prod_indicator_index (h := fun (_ m : ℕ) => (m.factorial : ℤ)) (fun _ => 1) (by simp),
    Finsupp.sum_indicator_index (h := fun _ : ℕ => id) (fun _ => 1) (by simp)] at h
  simp only [id_eq, pow_one, Nat.factorial_one, Nat.cast_one, Finset.prod_const_one,
    Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact (normalized_value μ hμ m₁ m₂ f hf).trans (hcard ▸ h.symm)

end MetaMathlibExt
