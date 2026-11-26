/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Polynomial.Pochhammer
public import MathlibExt.Combinatorics.Enumerative.ReducedUnicellularHypermonopoles
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination
import MathlibExt.Combinatorics.Enumerative.StirlingAscPochhammer
import MathlibExt.Combinatorics.Enumerative.ZagierCyclicPermutationProduct

/-!
# Unicellular hypermonopoles with a cyclic vertex permutation

We count the permutations `α` of `Fin n` such that `α⁻¹ * finRotate n` has exactly one cycle
and `α` has exactly `k` cycles, fixed points included. The count is `cyclicProductNumber n k`.
Writing `α = finRotate n * τ` turns the face condition into `τ` having exactly one cycle.
Conjugation makes each cyclic first factor contribute equally, so Zagier's formula gives the
count for the fixed first factor `finRotate n`.

The generating polynomial of the cyclic product numbers is a scaled difference of rising and
falling factorials: the difference selects precisely the Stirling coefficients of the required
parity.

## References

* Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of Integer
  Sequences 28 (2025), Article 25.3.3, pp. 1–15, Theorems 4–5, Lemma 6, and Corollary 8.
* Simona Grusea and Anthony Labarre, *The distribution of cycles in breakpoint graphs of signed
  permutations*, Discrete Applied Mathematics 161 (2013), pp. 1448–1466, Lemma 8.1.
* Don Zagier, *On the distribution of the number of cycles of elements in symmetric groups*,
  Nieuw Archief voor Wiskunde (4) 13 (1995), pp. 489–495, Theorem 1, application 3.
-/

namespace MetaMathlibExt

namespace card_unicellular_hypermonopoles_finRotate

private theorem cycleCount_eq_cycleType {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    cycleQuotientCount σ = Multiset.card σ.cycleType + (n - σ.cycleType.sum) := by
  rw [cycleQuotientCount_eq, Equiv.Perm.card_fixedPoints, Fintype.card_fin]

private theorem cycleCount_inv {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    cycleQuotientCount σ⁻¹ = cycleQuotientCount σ := by
  rw [cycleCount_eq_cycleType, cycleCount_eq_cycleType, Equiv.Perm.cycleType_inv]

private theorem cycleCount_conj {n : ℕ} (g σ : Equiv.Perm (Fin n)) :
    cycleQuotientCount (g * σ * g⁻¹) = cycleQuotientCount σ := by
  rw [cycleCount_eq_cycleType, cycleCount_eq_cycleType, Equiv.Perm.cycleType_conj]

private theorem cycleCount_le {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    cycleQuotientCount σ ≤ n := by
  rw [cycleQuotientCount]
  calc Nat.card (Quotient (Equiv.Perm.SameCycle.setoid σ)) ≤ Nat.card (Fin n) :=
        Nat.card_le_card_of_surjective _ Quotient.mk_surjective
    _ = n := Nat.card_eq_fintype_card.trans (Fintype.card_fin n)

private theorem cycleCount_pos {n : ℕ} (hn : 0 < n) (σ : Equiv.Perm (Fin n)) :
    0 < cycleQuotientCount σ := by
  rw [cycleQuotientCount]
  have : Nonempty (Quotient (Equiv.Perm.SameCycle.setoid σ)) :=
    ⟨Quotient.mk _ ⟨0, hn⟩⟩
  exact Nat.card_pos

private theorem cycleCount_fin_zero (σ : Equiv.Perm (Fin 0)) : cycleQuotientCount σ = 0 := by
  rw [cycleQuotientCount]
  exact Nat.card_of_isEmpty

/-- A permutation with exactly one cycle has the cycle type of `finRotate n`. -/
private theorem cycleType_eq_of_cycleCount_eq_one {n : ℕ} (σ : Equiv.Perm (Fin n))
    (hσ : cycleQuotientCount σ = 1) : σ.cycleType = (finRotate n).cycleType := by
  match n, σ, hσ with
  | 0, σ, hσ =>
    rw [cycleCount_fin_zero] at hσ
    exact absurd hσ zero_ne_one
  | 1, σ, _ =>
    congr 1
    exact Subsingleton.elim _ _
  | m + 2, σ, hσ =>
    rw [cycleCount_eq_cycleType] at hσ
    have hsum : σ.cycleType.sum ≤ m + 2 := by
      simpa only [Fintype.card_fin] using σ.sum_cycleType_le
    have hcard : Multiset.card σ.cycleType = 1 := by
      have hne : Multiset.card σ.cycleType ≠ 0 := by
        intro h0
        rw [h0, Multiset.card_eq_zero.mp h0, Multiset.sum_zero] at hσ
        omega
      omega
    obtain ⟨r, hr⟩ := Multiset.card_eq_one.mp hcard
    rw [hr, Multiset.sum_singleton] at hsum hσ
    rw [Multiset.card_singleton] at hσ
    rw [hr, cycleType_finRotate, show r = m + 2 by omega]

/-- Conjugating by a permutation carrying `finRotate n` to `σ` shows that every first factor
`σ` with one cycle has as many second factors as `finRotate n`. -/
private theorem card_fiber_eq {n : ℕ} (k : ℕ) (σ : Equiv.Perm (Fin n))
    (hσ : cycleQuotientCount σ = 1) :
    Fintype.card {τ : Equiv.Perm (Fin n) //
      cycleQuotientCount τ = 1 ∧ cycleQuotientCount (σ * τ) = k} =
    Fintype.card {τ : Equiv.Perm (Fin n) //
      cycleQuotientCount τ = 1 ∧ cycleQuotientCount (finRotate n * τ) = k} := by
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (Equiv.Perm.isConj_iff_cycleType_eq.mpr (cycleType_eq_of_cycleCount_eq_one σ hσ).symm)
  symm
  refine Fintype.card_congr (Equiv.subtypeEquiv (MulAut.conj g).toEquiv fun τ ↦ ?_)
  have hmul : g * finRotate n * g⁻¹ * (g * τ * g⁻¹) = g * (finRotate n * τ) * g⁻¹ := by
    group
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
  rw [cycleCount_conj, ← hg, hmul, cycleCount_conj]

private theorem card_cyclic {n : ℕ} (hn : 0 < n) :
    Fintype.card {σ : Equiv.Perm (Fin n) // cycleQuotientCount σ = 1} = (n - 1).factorial := by
  rw [Fintype.card_congr (Equiv.subtypeEquivRight fun σ ↦ by rw [cycleQuotientCount_eq]),
    card_perm_cycleCount_eq_stirlingFirst]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simpa using Nat.stirlingFirst_one_right m

/-- The pairs counted by Zagier's formula number `(n - 1)!` times the second factors that go
with `finRotate n`. -/
private theorem card_pairs_eq {n : ℕ} (hn : 0 < n) (k : ℕ) :
    Fintype.card {p : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) //
      cycleQuotientCount p.1 = 1 ∧ cycleQuotientCount p.2 = 1 ∧
        cycleQuotientCount (p.1 * p.2) = k} =
    (n - 1).factorial * Fintype.card {τ : Equiv.Perm (Fin n) //
      cycleQuotientCount τ = 1 ∧ cycleQuotientCount (finRotate n * τ) = k} := by
  let e : {p : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) //
      cycleQuotientCount p.1 = 1 ∧ cycleQuotientCount p.2 = 1 ∧
        cycleQuotientCount (p.1 * p.2) = k} ≃
      Σ σ : {σ : Equiv.Perm (Fin n) // cycleQuotientCount σ = 1},
        {τ : Equiv.Perm (Fin n) // cycleQuotientCount τ = 1 ∧
          cycleQuotientCount (σ.1 * τ) = k} :=
    { toFun := fun p ↦ ⟨⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩⟩
      invFun := fun q ↦ ⟨(q.1.1, q.2.1), q.1.2, q.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma,
    Finset.sum_congr rfl fun σ _ ↦ card_fiber_eq k σ.1 σ.2, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, card_cyclic hn]

-- Clear Zagier's denominator before using the natural-number division in `cyclicProductNumber`.
private theorem card_cyclic_finRotate_mul_scaled {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (hkn : k ≤ n) :
    (Fintype.card {τ : Equiv.Perm (Fin n) //
      cycleQuotientCount τ = 1 ∧ cycleQuotientCount (finRotate n * τ) = k} : ℚ) *
      ((n + 1 : ℚ) * n) = (1 + (-1 : ℚ) ^ (n - k)) * Nat.stirlingFirst (n + 1) k := by
  let F := Fintype.card {τ : Equiv.Perm (Fin n) //
    cycleQuotientCount τ = 1 ∧ cycleQuotientCount (finRotate n * τ) = k}
  have hZ := zagier_probability_product_two_cyclic_permutations n k hn hk hkn
  have hpairs : Fintype.card {p : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) //
        Multiset.card p.1.cycleType + Fintype.card (Function.fixedPoints p.1) = 1 ∧
        Multiset.card p.2.cycleType + Fintype.card (Function.fixedPoints p.2) = 1 ∧
        Multiset.card (p.1 * p.2).cycleType +
            Fintype.card (Function.fixedPoints (p.1 * p.2)) = k} =
      (n - 1).factorial * F := by
    rw [← card_pairs_eq hn k]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun p ↦ by
      simp only [cycleQuotientCount_eq])
  have hcyc : Fintype.card {σ : Equiv.Perm (Fin n) //
      Multiset.card σ.cycleType + Fintype.card (Function.fixedPoints σ) = 1} =
      (n - 1).factorial := by
    rw [← card_cyclic hn]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun σ ↦ by
      simp only [cycleQuotientCount_eq])
  have hfact : (n + 1).factorial = (n + 1) * n * (n - 1).factorial := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    simp only [Nat.succ_sub_one, Nat.factorial_succ, Nat.succ_eq_add_one, mul_assoc]
  rw [hpairs, hcyc, hfact] at hZ
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast at hZ
  field_simp [hn'] at hZ
  change (F : ℚ) * _ = _
  linear_combination hZ

private theorem even_add_iff_even_sub {n k : ℕ} (hkn : k ≤ n) :
    Even (n + k) ↔ Even (n - k) := by
  rw [show n + k = (n - k) + 2 * k by omega, Nat.even_add]
  simp

/-- The number of permutations `τ` with one cycle such that `finRotate n * τ` has `k` cycles
is the cyclic product number (Theorem 5 of the source). -/
private theorem card_cyclic_finRotate_mul (n k : ℕ) :
    Fintype.card {τ : Equiv.Perm (Fin n) //
      cycleQuotientCount τ = 1 ∧ cycleQuotientCount (finRotate n * τ) = k} =
      cyclicProductNumber n k := by
  set F := Fintype.card {τ : Equiv.Perm (Fin n) //
    cycleQuotientCount τ = 1 ∧ cycleQuotientCount (finRotate n * τ) = k} with hF
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [hF, Fintype.card_eq_zero_iff.mpr ⟨fun τ ↦ by simpa [cycleCount_fin_zero] using τ.2.1⟩]
    simp [cyclicProductNumber]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [hF, Fintype.card_eq_zero_iff.mpr ⟨fun τ ↦ (cycleCount_pos hn _).ne' τ.2.2⟩,
      cyclicProductNumber_zero_right]
  by_cases hkn : k ≤ n
  swap
  · -- A permutation of `Fin n` has at most `n` cycles, and `H(n, k)` vanishes for `k > n`.
    have hF0 : F = 0 := Fintype.card_eq_zero_iff.mpr
      ⟨fun τ ↦ by have := cycleCount_le (finRotate n * τ.1); omega⟩
    rw [hF0, cyclicProductNumber]
    split_ifs with heven
    · rcases Nat.lt_or_ge (n + 1) k with hlt | hge
      · rw [Nat.stirlingFirst_eq_zero_of_lt hlt, Nat.zero_div]
      · obtain rfl : k = n + 1 := by omega
        exact absurd heven (by rw [Nat.not_even_iff_odd]; exact ⟨n, by ring⟩)
    · rfl
  have hscaled : (F : ℚ) * ((n + 1 : ℚ) * n) =
      (1 + (-1 : ℚ) ^ (n - k)) * Nat.stirlingFirst (n + 1) k :=
    card_cyclic_finRotate_mul_scaled hn hk hkn
  have hpar := even_add_iff_even_sub hkn
  by_cases heven : Even (n - k)
  · rw [heven.neg_one_pow, one_add_one_eq_two] at hscaled
    have hchoose : ((n + 1).choose 2 : ℚ) * 2 = (n + 1) * n := by
      have h := Nat.add_one_mul_choose_eq n 1
      rw [Nat.choose_one_right] at h
      exact_mod_cast h.symm
    have hnat : Nat.stirlingFirst (n + 1) k = F * (n + 1).choose 2 := by
      have h2 : ((F * (n + 1).choose 2 : ℕ) : ℚ) * 2 = (Nat.stirlingFirst (n + 1) k : ℚ) * 2 := by
        push_cast
        linear_combination (F : ℚ) * hchoose + hscaled
      exact_mod_cast (mul_right_cancel₀ two_ne_zero h2).symm
    rw [cyclicProductNumber, ite_eq_left (hpar.mpr heven), hnat,
      Nat.mul_div_cancel _ (Nat.choose_pos (by omega))]
  · rw [(Nat.not_even_iff_odd.mp heven).neg_one_pow, add_neg_cancel, zero_mul] at hscaled
    have hF0 := (mul_eq_zero.mp hscaled).resolve_right (by positivity)
    rw [cyclicProductNumber_of_odd (mt hpar.mp heven)]
    exact_mod_cast hF0

end card_unicellular_hypermonopoles_finRotate

open card_unicellular_hypermonopoles_finRotate in
/-- **Unicellular hypermonopoles with a cyclic vertex permutation.** Let $n$ and $k$ be natural
numbers, let $\sigma$ be the cyclic permutation $i \mapsto i + 1$ (modulo $n$) of
$\{0, 1, \dots, n - 1\}$, and write $z(\pi)$ for the number of cycles of a permutation $\pi$,
fixed points included. Then the number of permutations $\alpha$ of $\{0, 1, \dots, n - 1\}$ with
$z(\alpha^{-1} \circ \sigma) = 1$ and $z(\alpha) = k$ is the cyclic product number $H(n, k)$.

In the terms of the source, these $\alpha$ are the unicellular hypermonopoles $(\sigma, \alpha)$
with $\sigma = (1, \dots, n)$ and $z(\alpha) = k$.

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Corollary 8 (`jis-2025-25.3.3-cor-8`). -/
public theorem card_unicellular_hypermonopoles_finRotate (n k : ℕ) :
    Fintype.card {α : Equiv.Perm (Fin n) //
      cycleQuotientCount (α⁻¹ * finRotate n) = 1 ∧ cycleQuotientCount α = k} =
      cyclicProductNumber n k := by
  -- Writing `α = finRotate n * τ` turns the face condition into `τ` having one cycle.
  rw [← card_cyclic_finRotate_mul n k]
  refine Fintype.card_congr
    (Equiv.subtypeEquiv (Equiv.mulLeft (finRotate n)⁻¹) fun α ↦ ?_)
  rw [Equiv.coe_mulLeft, mul_inv_cancel_left, ← cycleCount_inv ((finRotate n)⁻¹ * α),
    mul_inv_rev, inv_inv]

open Polynomial

-- Replacing `X` by `-X` in the rising factorial changes each linear factor by a sign.
private theorem descPochhammer_eq_stirlingFirst_sum (m : ℕ) :
    descPochhammer ℚ m = ∑ k ∈ Finset.range (m + 1),
      C ((-1 : ℚ) ^ (m + k) * Nat.stirlingFirst m k) * X ^ k := by
  have h : descPochhammer ℚ m = C ((-1 : ℚ) ^ m) * (ascPochhammer ℚ m).comp (-X) := by
    have he := ascPochhammer_eval_neg_eq_descPochhammer ℚ[X] X m
    rw [← ascPochhammer_map (C : ℚ →+* ℚ[X]), ← descPochhammer_map (C : ℚ →+* ℚ[X]),
      eval_map, eval_map] at he
    change (ascPochhammer ℚ m).comp (-X) = (-1 : ℚ[X]) ^ m * (descPochhammer ℚ m).comp X at he
    rw [comp_X] at he
    rw [he, map_pow, map_neg, map_one, ← mul_assoc, ← mul_pow]
    simp
  rw [h, ← Nat.sum_stirlingFirst_mul_X_pow, ← coe_compRingHom_apply, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [coe_compRingHom_apply, mul_X_pow_comp, natCast_comp, ← neg_one_mul (X : ℚ[X]),
    mul_pow, pow_add]
  simp only [map_mul, map_pow, map_neg, map_one, C_eq_natCast]
  ring

open card_unicellular_hypermonopoles_finRotate in
/-- **Generating polynomial of the cyclic product numbers.** For every natural number $n$, let
$H(n, k)$ be the cyclic product numbers, viewed as rational numbers. Then in the polynomial
ring $\mathbb{Q}[x]$
$$\sum_{k=0}^{n} H(n, k) x^k = c_n (x (x + 1) \cdots (x + n) - x (x - 1) \cdots (x - n)),$$
where $c_n = \frac{1}{(n + 1) n}$ for $n \ge 1$ and $c_0 = 0$; for $n = 0$ both sides are $0$.

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Lemma 6 (`jis-2025-25.3.3-lem-6`), quoting
S. Grusea and A. Labarre. -/
public theorem sum_cyclicProductNumber_mul_X_pow (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), C (cyclicProductNumber n k : ℚ) * X ^ k =
      C (((n + 1 : ℚ) * n)⁻¹) * (ascPochhammer ℚ (n + 1) - descPochhammer ℚ (n + 1)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [cyclicProductNumber_zero_right]
  have hasc : ascPochhammer ℚ (n + 1) = ∑ k ∈ Finset.range (n + 1 + 1),
      C (Nat.stirlingFirst (n + 1) k : ℚ) * X ^ k := by
    simpa only [C_eq_natCast] using (Nat.sum_stirlingFirst_mul_X_pow ℚ (n + 1)).symm
  -- The leading terms of the two monic factorials cancel.
  rw [hasc, descPochhammer_eq_stirlingFirst_sum, ← Finset.sum_sub_distrib,
    Finset.sum_range_succ _ (n + 1)]
  have heven : Even (n + 1 + (n + 1)) := ⟨n + 1, rfl⟩
  have htop : (-1 : ℚ) ^ (n + 1 + (n + 1)) = 1 := heven.neg_one_pow
  simp only [htop, one_mul, sub_self, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [← sub_mul, ← (C : ℚ →+* ℚ[X]).map_sub, ← mul_assoc, ← (C : ℚ →+* ℚ[X]).map_mul]
  apply congrArg (fun r : ℚ ↦ C r * X ^ k)
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simp [cyclicProductNumber_zero_right, Nat.stirlingFirst_succ_zero]
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hsign : (-1 : ℚ) ^ ((n + 1) + k) = -((-1 : ℚ) ^ (n - k)) := by
    rw [show n + 1 + k = (n + k) + 1 by omega, pow_succ,
      neg_one_pow_congr (even_add_iff_even_sub hkn), mul_neg_one]
  have hscaled := card_cyclic_finRotate_mul_scaled hn hkpos hkn
  rw [card_cyclic_finRotate_mul] at hscaled
  calc
    (cyclicProductNumber n k : ℚ) = (((n + 1 : ℚ) * n)⁻¹) *
        ((cyclicProductNumber n k : ℚ) * ((n + 1 : ℚ) * n)) := by
      rw [mul_left_comm, inv_mul_cancel₀ (by positivity), mul_one]
    _ = _ := by rw [hscaled, hsign]; ring

end MetaMathlibExt
