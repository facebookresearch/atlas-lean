/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.OrderOfElement
public import MathlibExt.Combinatorics.Additive.PerfectSubsetSumCover
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Coordinate orders in perfect subset-sum covers

Project the cover onto the cyclic factor and evaluate its subset-sum generating function at a
nontrivial character. Constant multiplicity makes this evaluation zero, so a factor corresponding
to one index must vanish.

## References

* John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power of 2*,
  Journal of Integer Sequences 28 (2025), Article 25.7.8, pp. 1–18, Corollary 14 (p. 8).
  The argument uses the projection of Lemma 6 (p. 4) and evaluates the generating function from
  the necessity direction of Theorem 12 (p. 7) at a root of unity.
-/

namespace MetaMathlibExt

open PerfectSubsetSumCover

private theorem exists_addOrderOf_of_isPerfectMCover_zmod {n m : ℕ} {ι : Type*} [Fintype ι]
    {s : ι → ZMod (2 ^ n)} (hs : IsPerfectMCover m s) (k : ℕ) (hk : k < n) :
    ∃ i, addOrderOf (s i) = 2 ^ (k + 1) := by
  classical
  let ψ := ZMod.stdAddChar (N := 2 ^ n)
  let χ : AddChar (ZMod (2 ^ n)) ℂ := (2 ^ k : ℕ) • ψ
  have hχ (x : ZMod (2 ^ n)) : χ x = ψ ((2 ^ k : ℕ) • x) := by
    rw [ψ.map_nsmul_eq_pow, AddChar.nsmul_apply]
  have hχne : χ ≠ 0 := by
    intro h
    have heval : χ 1 = ψ 0 := by rw [h, AddChar.zero_apply, ψ.map_zero_eq_one]
    rw [hχ] at heval
    have hzero := ZMod.injective_stdAddChar heval
    have hlt : (2 : ℕ) ^ k < 2 ^ n := Nat.pow_lt_pow_right (by decide) hk
    exact (Nat.not_dvd_of_pos_of_lt (by positivity) hlt)
      (by simpa only [Nat.smul_one_eq_cast, ZMod.natCast_eq_zero_iff] using hzero)
  let subsetSum (I : Finset ι) := ∑ i ∈ I, s i
  have hsum : ∑ I : Finset ι, χ (subsetSum I) = 0 := by
    -- Regroup the subset sum by its value, retaining the multiplicity of each fiber.
    rw [← Finset.sum_fiberwise' Finset.univ subsetSum χ]
    change (∑ x, ∑ _I ∈ Finset.univ.filter (fun I => subsetSum I = x), χ x) = 0
    simp only [Finset.sum_const, nsmul_eq_mul]
    change (∑ x, (coverCount s x : ℂ) * χ x) = 0
    have hcount (x : ZMod (2 ^ n)) : coverCount s x = m := hs x
    simp only [hcount, ← Finset.mul_sum, AddChar.sum_eq_zero_iff_ne_zero.mpr hχne, mul_zero]
  have hprod : ∏ i, (1 + χ (s i)) = 0 := by
    rw [Finset.prod_one_add, Finset.powerset_univ, ← hsum]
    apply Finset.sum_congr rfl
    intro I _
    change (∏ i ∈ I, χ.toMonoidHom (Multiplicative.ofAdd (s i))) =
      χ.toMonoidHom (Multiplicative.ofAdd (∑ i ∈ I, s i))
    rw [ofAdd_sum, map_prod]
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hprod
  have hi' : χ (s i) = -1 := eq_neg_of_add_eq_zero_right hi
  refine ⟨i, addOrderOf_eq_prime_pow (p := 2) ?_ ?_⟩
  · intro hz
    rw [hχ, hz, ψ.map_zero_eq_one] at hi'
    exact (by norm_num : (1 : ℂ) ≠ -1) hi'
  · apply ZMod.injective_stdAddChar
    change ψ ((2 ^ (k + 1) : ℕ) • s i) = ψ 0
    rw [ψ.map_zero_eq_one, ψ.map_nsmul_eq_pow, pow_succ (2 : ℕ), pow_mul,
      ← ψ.map_nsmul_eq_pow, ← hχ, hi', neg_one_sq]

/-- **Orders of second coordinates in perfect $m$-covers.** Let $H$ be a finite abelian group of
order $2^r$ and let $s = (s_i)_{i \in \iota}$ be a family in $H \oplus \mathbb{Z}_{2^n}$ indexed by
a finite type $\iota$. If $s$ is a perfect $m$-cover of $H \oplus \mathbb{Z}_{2^n}$, then for
every $j$ with $1 \le j \le n$ the second coordinate of some $s_i$ has additive order $2^j$.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Corollary 14
(`jis-2025-25.7.8-cor-14`). The family has any finite index type (the record reuses `n`
for its length). -/
public theorem exists_snd_addOrderOf_of_isPerfectMCover {H : Type*} [AddCommGroup H]
    [DecidableEq H] [Fintype H] {r n m : ℕ} (hH : Fintype.card H = 2 ^ r) {ι : Type*}
    [Fintype ι] {s : ι → H × ZMod (2 ^ n)} (hs : IsPerfectMCover m s) :
    ∀ j : ℕ, 1 ≤ j → j ≤ n → ∃ i, addOrderOf (s i).2 = 2 ^ j := by
  intro j hj hjn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  exact exists_addOrderOf_of_isPerfectMCover_zmod
    (isPerfectMCover_fst_snd hH (ZMod.card (2 ^ n)) hs).2 k (by omega)

end MetaMathlibExt
