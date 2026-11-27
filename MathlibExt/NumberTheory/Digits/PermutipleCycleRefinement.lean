/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.Permutiple
import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# Cycle-preserving permutiple permutations

Swapping two equal-digit outputs on a cycle preserves the whole permuted digit word and splits
that cycle. To formalize termination, minimize the number of ordered pairs of positions in the
same cycle among all permutations inducing that word. This counts fixed points as singleton
cycles and strictly decreases whenever a cycle splits.

## References

* Benjamin V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25 (2025),
  Article A13, Definition 5 and Theorem 5 (pp. 6–7).
* Benjamin V. Holt, *On Permutiples Having a Fixed Set of Digits*, INTEGERS 17 (2017),
  Article A20, §1 (the definition of a permutiple, cited by Holt).
-/

namespace MetaMathlibExt

open Equiv Equiv.Perm

/-- If every new step stays within an old cycle, the new cycles refine the old ones. -/
private theorem sameCycle_refines {α : Type*} [Finite α] {π τ : Perm α}
    (h : ∀ x, π.SameCycle x (τ x)) {x y : α} (hxy : τ.SameCycle x y) : π.SameCycle x y := by
  obtain ⟨i, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction i with
  | zero => simpa using SameCycle.refl π x
  | succ i ih => simpa only [pow_succ', Perm.mul_apply] using ih.trans (h ((τ ^ i) x))

/-- Swapping the outputs `a` and `b` closes the arc from `a` to the predecessor of the
first occurrence of `b`. In particular, the new cycle through `a` does not contain `b`. -/
private theorem not_sameCycle_swap_mul {α : Type*} [Finite α] [DecidableEq α]
    (π : Perm α) {a b : α} (hab : a ≠ b) (hit : ∃ i : ℕ, (π ^ i) a = b) :
    ¬ (swap a b * π).SameCycle a b := by
  let m := Nat.find hit
  have hm : (π ^ m) a = b := Nat.find_spec hit
  have hmpos : 0 < m := by
    by_contra! h
    have hz : m = 0 := by omega
    simp [hz, hab] at hm
  have hno_b {i : ℕ} (hi : i < m) : (π ^ i) a ≠ b := Nat.find_min hit hi
  let τ := swap a b * π
  have hbefore (i : ℕ) (hi : i < m) : (τ ^ i) a = (π ^ i) a := by
    induction i with
    | zero => rfl
    | succ i ih =>
      have hne : (π ^ (i + 1)) a ≠ a := by
        intro he
        apply hno_b (i := m - (i + 1)) (by omega)
        have hsum : m - (i + 1) + (i + 1) = m := by omega
        calc
          (π ^ (m - (i + 1))) a = (π ^ (m - (i + 1) + (i + 1))) a := by
            rw [pow_add, Perm.mul_apply, he]
          _ = b := by simpa only [hsum] using hm
      rw [pow_succ', Perm.mul_apply, ih (by omega)]
      change swap a b (π ((π ^ i) a)) = _
      have hstep : π ((π ^ i) a) = (π ^ (i + 1)) a := by
        rw [pow_succ', Perm.mul_apply]
      rw [hstep, swap_apply_of_ne_of_ne hne (hno_b hi)]
  have hreturn : (τ ^ m) a = a := by
    obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
    change m = i + 1 at hi
    have hh : (π ^ (i + 1)) a = b := by simpa only [hi] using hm
    rw [hi, pow_succ', Perm.mul_apply, hbefore i (by omega)]
    change swap a b (π ((π ^ i) a)) = a
    have hstep : π ((π ^ i) a) = (π ^ (i + 1)) a := by
      rw [pow_succ', Perm.mul_apply]
    rw [hstep, hh, swap_apply_right]
  intro hc
  obtain ⟨i, hi⟩ := hc.exists_nat_pow_eq
  have havoid (j : ℕ) : (τ ^ j) a ≠ b := by
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      by_cases hj : j < m
      · rw [hbefore j hj]; exact hno_b hj
      · have hj' : j = j - m + m := by omega
        calc
          (τ ^ j) a = (τ ^ (j - m)) a := by
            conv_lhs => rw [hj', pow_add, Perm.mul_apply, hreturn]
          _ ≠ b := ih (j - m) (by omega)
  exact havoid i hi

private theorem exists_distinct_digit_cycles {α : Type*} [Finite α]
    (d : α → ℕ) (σ : Perm α) :
    ∃ π : Perm α, (∀ x, d (π x) = d (σ x)) ∧
      ∀ x (i : ℕ), d ((π ^ i) x) = d x → (π ^ i) x = x := by
  classical
  let _ : Fintype α := Fintype.ofFinite α
  let pairs (π : Perm α) : Finset (α × α) := Finset.univ.filter fun x => π.SameCycle x.1 x.2
  have hex : ∃ c, ∃ π : Perm α, (∀ x, d (π x) = d (σ x)) ∧ (pairs π).card = c :=
    ⟨(pairs σ).card, σ, fun _ => rfl, rfl⟩
  obtain ⟨π, hπ, hcount⟩ := Nat.find_spec hex
  refine ⟨π, hπ, fun a i hd => ?_⟩
  by_contra! hne
  let b := (π ^ i) a
  let τ := swap a b * π
  have hab : a ≠ b := hne.symm
  have hcycle : π.SameCycle a b := (SameCycle.refl π a).pow_right
  have hword (x : α) : d (τ x) = d (σ x) := by
    change d (swap a b (π x)) = d (σ x)
    rw [← hπ x, swap_apply_def]
    split_ifs <;> simp_all [b]
  have hstep (x : α) : π.SameCycle x (τ x) := by
    have hx : π.SameCycle x (π x) := (SameCycle.refl π x).apply_right
    apply hx.trans
    change π.SameCycle (π x) (swap a b (π x))
    rw [swap_apply_def]
    split_ifs with ha hb
    · exact ha ▸ hcycle
    · exact hb ▸ hcycle.symm
    · exact SameCycle.refl _ _
  have hsub : pairs τ ⊆ pairs π := by
    intro x hx
    simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact sameCycle_refines hstep hx
  have hs : pairs τ ⊂ pairs π := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, by
    intro he
    have hmem : (a, b) ∈ pairs π := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcycle⟩
    rw [← he] at hmem
    exact not_sameCycle_swap_mul π hab ⟨i, rfl⟩ (Finset.mem_filter.mp hmem).2⟩
  have hlt := Finset.card_lt_card hs
  exact (not_lt_of_ge (Nat.find_min' hex ⟨τ, hword, rfl⟩)) (hcount ▸ hlt)

/-- **Every permutiple has a cycle-preserving digit permutation.** Let $n$, $b$ and
$d_0, \dots, d_k$ be natural numbers and let $\sigma$ be a permutation of $\{0, \dots, k\}$ such
that $(d_k, \dots, d_0)_b$ is an $(n, b, \sigma)$-permutiple. Then there is a permutation
$\hat\sigma$ of $\{0, \dots, k\}$ such that $(d_k, \dots, d_0)_b$ is also an
$(n, b, \hat\sigma)$-permutiple and the digits along each cycle of $\hat\sigma$ are distinct:
for all $j \in \{0, \dots, k\}$ and all $i \ge 0$, if $d_{\hat\sigma^i(j)} = d_j$ then
$\hat\sigma^i(j) = j$.

Unlike the paper, no assumption $1 < n < b$ is made.

Source: B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25
(2025), Article A13, Theorem 5 (`integers-2025-A13-thm-5`), with Definition 5
(cycle-preserving permutations). -/
public theorem exists_cyclePreserving_permutiple (n b : ℕ) {k : ℕ}
    (d : Fin (k + 1) → ℕ) (σ : Equiv.Perm (Fin (k + 1))) (hp : IsPermutiple n b d σ) :
    ∃ σ' : Equiv.Perm (Fin (k + 1)), IsPermutiple n b d σ' ∧
      ∀ (j : Fin (k + 1)) (i : ℕ), d ((σ' ^ i) j) = d j → (σ' ^ i) j = j := by
  obtain ⟨π, hword, hcycles⟩ := exists_distinct_digit_cycles d σ
  refine ⟨π, ⟨hp.1, ?_⟩, hcycles⟩
  simpa only [hword] using hp.2

end MetaMathlibExt
