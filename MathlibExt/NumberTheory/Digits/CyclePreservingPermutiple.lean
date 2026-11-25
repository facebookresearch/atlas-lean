/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import MathlibExt.NumberTheory.Digits.Permutiple

/-!
# Permutiples with a fixed set of digits (Holt)

Statements from B. V. Holt, *A Method for Finding All Permutiples with a Fixed
Set of Digits from a Single Known Example*, INTEGERS 24 (2024), Article A88
(arXiv:2312.02056).

A `(k+1)`-digit base-`b` numeral `(d_k, …, d_0)_b` is a digit function
`d : Fin (k + 1) → ℕ` (digit `d j` has weight `b ^ j`); for a permutation `π`,
the numeral `(d_{π(k)}, …, d_{π(0)})_b` is `d ∘ π`.
-/

namespace MetaMathlibExt

namespace exists_cyclePreserving_permutiple

variable {k : ℕ} (d : Fin (k + 1) → ℕ) (σ : Equiv.Perm (Fin (k + 1)))

/-- The pairs of distinct positions in the same cycle of `τ` whose digits agree. -/
private def badSet (τ : Equiv.Perm (Fin (k + 1))) : Set (Fin (k + 1) × Fin (k + 1)) :=
  {p | p.1 ≠ p.2 ∧ τ.SameCycle p.1 p.2 ∧ d p.1 = d p.2}

/-- A point and its image under a swapped permutation lie in the same `τ`-cycle. -/
private theorem sameCycle_swap_mul_apply {τ : Equiv.Perm (Fin (k + 1))} {p q : Fin (k + 1)}
    (hpq : τ.SameCycle p q) (x : Fin (k + 1)) :
    τ.SameCycle x ((Equiv.swap p q * τ) x) := by
  rw [Equiv.Perm.mul_apply]
  have hself : τ.SameCycle x (τ x) :=
    (Equiv.Perm.sameCycle_apply_right).2 (Equiv.Perm.SameCycle.refl _ _)
  by_cases hx : τ x = p
  · rw [hx, Equiv.swap_apply_left]
    exact (hx ▸ hself).trans hpq
  · by_cases hx' : τ x = q
    · rw [hx', Equiv.swap_apply_right]
      exact (hx' ▸ hself).trans hpq.symm
    · rw [Equiv.swap_apply_of_ne_of_ne hx hx']
      exact hself

/-- Powers of a swapped permutation stay in the same `τ`-cycle. -/
private theorem sameCycle_of_sameCycle_swap_mul {τ : Equiv.Perm (Fin (k + 1))}
    {p q x y : Fin (k + 1)} (hpq : τ.SameCycle p q)
    (h : (Equiv.swap p q * τ).SameCycle x y) : τ.SameCycle x y := by
  obtain ⟨i, hi⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq h
  have hpow : ∀ i : ℕ, ∀ z : Fin (k + 1), τ.SameCycle z (((Equiv.swap p q * τ) ^ i) z) := by
    intro i
    induction i with
    | zero => intro z; simpa using Equiv.Perm.SameCycle.refl τ z
    | succ i ih =>
      intro z
      rw [pow_succ, Equiv.Perm.mul_apply]
      exact (sameCycle_swap_mul_apply hpq z).trans (ih _)
  rw [← hi]
  exact hpow i x

/-- Swapping the images of two positions with equal digits does not change `d ∘ τ`. -/
private theorem comp_swap_mul {τ : Equiv.Perm (Fin (k + 1))} {p q : Fin (k + 1)}
    (hd : d p = d q) : d ∘ (Equiv.swap p q * τ) = d ∘ τ := by
  funext x
  simp only [Function.comp_apply, Equiv.Perm.mul_apply]
  by_cases hx : τ x = p
  · rw [hx, Equiv.swap_apply_left, hd]
  · by_cases hx' : τ x = q
    · rw [hx', Equiv.swap_apply_right, ← hd]
    · rw [Equiv.swap_apply_of_ne_of_ne hx hx']

/-- The swapped permutation separates the two positions of a repeated digit. -/
private theorem not_sameCycle_swap_mul {τ : Equiv.Perm (Fin (k + 1))} {p q : Fin (k + 1)}
    (hpq : τ.SameCycle p q) (hne : p ≠ q) :
    ¬ (Equiv.swap p q * τ).SameCycle p q := by
  obtain ⟨i₀, hi₀, -, hi₀eq⟩ := Equiv.Perm.SameCycle.exists_pow_eq'' hpq
  have hex : ∃ i : ℕ, 0 < i ∧ (τ ^ i) p = q := ⟨i₀, hi₀, hi₀eq⟩
  classical
  set r := Nat.find hex with hr_def
  have hr := Nat.find_spec hex
  have hmin : ∀ m : ℕ, 0 < m → (τ ^ m) p = q → r ≤ m := fun m hm hmq =>
    Nat.find_min' hex ⟨hm, hmq⟩
  -- The first `r` positions of the `τ`-orbit of `p`, ending just before `q`.
  set S : Finset (Fin (k + 1)) := (Finset.range r).image fun i => (τ ^ i) p with hS_def
  have hrpos : 0 < r := hr.1
  have hqS : q ∉ S := by
    rw [hS_def]
    simp only [Finset.mem_image, Finset.mem_range]
    rintro ⟨i, hi, hqi⟩
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · rw [hi0] at hqi
      simp only [pow_zero, Equiv.Perm.coe_one, id_eq] at hqi
      exact hne hqi
    · exact (Nat.not_lt_of_ge (hmin i hi0 hqi)) hi
  have hstep : ∀ x ∈ S, (Equiv.swap p q * τ) x ∈ S := by
    intro x hx
    rw [hS_def] at hx ⊢
    simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Equiv.Perm.mul_apply]
    have hnext : τ ((τ ^ i) p) = (τ ^ (i + 1)) p := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    rw [hnext]
    by_cases hyq : (τ ^ (i + 1)) p = q
    · rw [hyq, Equiv.swap_apply_right]
      exact ⟨0, hrpos, by simp⟩
    · by_cases hyp : (τ ^ (i + 1)) p = p
      · exfalso
        have hdecomp : (τ ^ (r - (i + 1))) p = q := by
          have hpow : τ ^ r = τ ^ (r - (i + 1)) * τ ^ (i + 1) := by
            rw [← pow_add, Nat.sub_add_cancel (by omega)]
          have hqr := hr.2
          rw [hpow, Equiv.Perm.mul_apply, hyp] at hqr
          exact hqr
        rcases Nat.eq_zero_or_pos (r - (i + 1)) with h0 | h0
        · rw [h0] at hdecomp
          simp only [pow_zero, Equiv.Perm.coe_one, id_eq] at hdecomp
          exact hne hdecomp
        · have hle := hmin _ h0 hdecomp
          omega
      · rw [Equiv.swap_apply_of_ne_of_ne hyp hyq]
        refine ⟨i + 1, ?_, rfl⟩
        rcases Nat.lt_or_ge (i + 1) r with hlt | hge
        · exact hlt
        · have : i + 1 = r := Nat.le_antisymm (Nat.succ_le_of_lt hi) hge
          rw [this] at hyq
          exact absurd hr.2 hyq
  have horbit : ∀ i : ℕ, ((Equiv.swap p q * τ) ^ i) p ∈ S := by
    intro i
    induction i with
    | zero =>
      have hpS : p ∈ S := by
        rw [hS_def]
        exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hrpos, by simp⟩
      simpa using hpS
    | succ i ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact hstep _ ih
  intro hsame
  obtain ⟨i, hi⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq hsame
  rw [← hi] at hqS
  exact hqS (horbit i)

/-- Splitting a cycle at a repeated digit strictly shrinks the set of bad pairs. -/
private theorem badSet_ssubset_of_repeat {τ : Equiv.Perm (Fin (k + 1))} {p q : Fin (k + 1)}
    (hpq : τ.SameCycle p q) (hne : p ≠ q) (hd : d p = d q) :
    badSet d (Equiv.swap p q * τ) ⊂ badSet d τ := by
  rw [Set.ssubset_iff_subset_ne]
  refine ⟨fun x hx => ?_, fun hEq => ?_⟩
  · obtain ⟨hxne, hxsame, hxeq⟩ := hx
    exact ⟨hxne, sameCycle_of_sameCycle_swap_mul hpq hxsame, hxeq⟩
  · have hmem : (p, q) ∈ badSet d τ := ⟨hne, hpq, hd⟩
    rw [← hEq] at hmem
    exact not_sameCycle_swap_mul hpq hne hmem.2.1

/-- A permutation with no bad pair is cycle-preserving, or one step improves it. -/
private theorem exists_good_of_le : ∀ n : ℕ, ∀ τ : Equiv.Perm (Fin (k + 1)),
    d ∘ τ = d ∘ σ → (badSet d τ).ncard ≤ n →
      ∃ τ' : Equiv.Perm (Fin (k + 1)), d ∘ τ' = d ∘ σ ∧
        ∀ (j : Fin (k + 1)) (i : ℕ), d ((τ' ^ i) j) = d j → (τ' ^ i) j = j := by
  intro n
  induction n with
  | zero =>
    intro τ hcomp hcard
    refine ⟨τ, hcomp, fun j i hij => ?_⟩
    by_contra hne
    have hmem : (j, (τ ^ i) j) ∈ badSet d τ := by
      refine ⟨Ne.symm hne, ⟨i, ?_⟩, hij.symm⟩
      rw [zpow_natCast]
    have hpos : 0 < (badSet d τ).ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨_, hmem⟩
    omega
  | succ n ih =>
    intro τ hcomp hcard
    by_cases hgood : ∀ (j : Fin (k + 1)) (i : ℕ), d ((τ ^ i) j) = d j → (τ ^ i) j = j
    · exact ⟨τ, hcomp, hgood⟩
    · push Not at hgood
      obtain ⟨j, i, hij, hne⟩ := hgood
      have hpq : τ.SameCycle j ((τ ^ i) j) := ⟨i, by rw [zpow_natCast]⟩
      have hlt : (badSet d (Equiv.swap j ((τ ^ i) j) * τ)).ncard < (badSet d τ).ncard :=
        Set.ncard_lt_ncard (badSet_ssubset_of_repeat d hpq (Ne.symm hne) hij.symm) (Set.toFinite _)
      obtain ⟨τ', hcomp', hgood'⟩ := ih (Equiv.swap j ((τ ^ i) j) * τ)
        ((comp_swap_mul d hij.symm).trans hcomp) (by omega)
      exact ⟨τ', hcomp', hgood'⟩

end exists_cyclePreserving_permutiple

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
  obtain ⟨τ, hcomp, hgood⟩ :=
    exists_cyclePreserving_permutiple.exists_good_of_le d σ
      ((exists_cyclePreserving_permutiple.badSet d σ).ncard) σ rfl le_rfl
  refine ⟨τ, ⟨hp.1, ?_⟩, hgood⟩
  have hsum : ∑ j, d (τ j) * b ^ (j : ℕ) = ∑ j, d (σ j) * b ^ (j : ℕ) :=
    Finset.sum_congr rfl fun j _ => by
      have hj := congrFun hcomp j
      simp only [Function.comp_apply] at hj
      rw [hj]
  rw [hsum]
  exact hp.2

end MetaMathlibExt
