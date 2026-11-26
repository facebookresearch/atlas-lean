/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.ReducedUnicellularHypermonopoles
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination
import MathlibExt.Combinatorics.Enumerative.ZagierCyclicPermutationProduct

/-!
# Unicellular hypermonopoles with a cyclic vertex permutation

We prove that the number of permutations `α` of `Fin n` such that `α⁻¹ * finRotate n` has
exactly one cycle and `α` has exactly `k` cycles, fixed points included, is the cyclic product
number `cyclicProductNumber n k`. This is Corollary 8 of Cori and Hetyei, *On Reduced
Unicellular Hypermonopoles* (Corollary 2.2 in the arXiv version, arXiv:2403.19569v2, which
numbers its statements by section).

The proof follows the source. Writing `α = finRotate n * τ`, the condition on
`α⁻¹ * finRotate n` says that `τ` has exactly one cycle (Remark 2.1 in the arXiv version), so the
count is the number of such `τ` for which `finRotate n * τ` has `k` cycles (Theorem 1.4 in the
arXiv version). Every permutation with exactly one cycle is conjugate to `finRotate n`, so each
of the `(n - 1)!` choices of the first factor `σ` contributes equally to the number of pairs
`(σ, τ)` of permutations with one cycle each whose product `σ * τ` has `k` cycles; Zagier's
formula `MetaMathlibExt.zagier_probability_product_two_cyclic_permutations` then gives the
count.
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

/-- The number of permutations `τ` with one cycle such that `finRotate n * τ` has `k` cycles
is the cyclic product number (Theorem 1.4 in the arXiv version of the source). -/
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
  -- The main case: Zagier's formula for the pairs of permutations with one cycle each.
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
  rw [hpairs, hcyc] at hZ
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hfact : (m + 1 + 1).factorial = (m + 2) * (m + 1) * m.factorial := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    ring
  rw [Nat.add_sub_cancel, hfact] at hZ
  have hpar : Even (m + 1 + k) ↔ Even (m + 1 - k) := by
    rw [show m + 1 + k = (m + 1 - k) + 2 * k by omega, Nat.even_add]
    simp
  by_cases heven : Even (m + 1 - k)
  · rw [heven.neg_one_pow] at hZ
    have hkey : (F : ℚ) * ((m + 1) * (m + 2)) = 2 * Nat.stirlingFirst (m + 1 + 1) k := by
      push_cast at hZ
      field_simp at hZ
      linear_combination hZ
    have hchoose : ((m + 1 + 1).choose 2 : ℚ) * 2 = (m + 1) * (m + 2) := by
      have h : (m + 1) * (m + 2) = (m + 1 + 1).choose 2 * 2 := by
        have h' := Nat.add_one_mul_choose_eq (m + 1) 1
        rw [Nat.choose_one_right] at h'
        rw [← h']
        ring
      exact_mod_cast h.symm
    have hnat : Nat.stirlingFirst (m + 1 + 1) k = F * (m + 1 + 1).choose 2 := by
      have h2 : ((F * (m + 1 + 1).choose 2 : ℕ) : ℚ) * 2 =
          (Nat.stirlingFirst (m + 1 + 1) k : ℚ) * 2 := by
        push_cast
        linear_combination (F : ℚ) * hchoose + hkey
      exact_mod_cast (mul_right_cancel₀ two_ne_zero h2).symm
    rw [cyclicProductNumber, ite_eq_left (hpar.mpr heven), hnat,
      Nat.mul_div_cancel _ (Nat.choose_pos (by omega))]
  · rw [(Nat.not_even_iff_odd.mp heven).neg_one_pow] at hZ
    have hF0 : (F : ℚ) = 0 := by
      push_cast at hZ
      field_simp at hZ
      have hprod : (F : ℚ) * ((m + 2) * (m + 1)) = 0 := by linear_combination hZ
      exact (mul_eq_zero.mp hprod).resolve_right (by positivity)
    rw [cyclicProductNumber, ite_eq_right (mt hpar.mp heven)]
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

end MetaMathlibExt
