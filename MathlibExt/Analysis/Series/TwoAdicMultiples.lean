/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import MathlibExt.Analysis.SpecialFunctions.QPochhammer
import Mathlib.Data.Nat.PadicValNat
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Regrouping the multiples of a power of two

`tsum_twoAdic_high_regroup` sums a sequence over positive multiples of `2 ^ J` by
factoring the quotient into its odd part and its power of two.
`tprod_qPochhammer_twoAdic_factorization` groups the factors of the Euler product
by the same decomposition.
-/

namespace MetaMathlibExt
namespace tsum_twoAdic_high_regroup

/-- Enumerate the positive integers, shifted down by one, by exponent and odd cofactor. -/
private def indexEquiv : ℕ × ℕ ≃ ℕ where
  toFun x := (2 * x.2 + 1) * 2 ^ x.1 - 1
  invFun p := (padicValNat 2 (p + 1), (p + 1).divMaxPow 2 / 2)
  left_inv := by
    rintro ⟨j, n⟩
    have hpos : 0 < (2 * n + 1) * 2 ^ j := by positivity
    have hparts : Nat.maxPowDvdDiv 2 ((2 * n + 1) * 2 ^ j) = (j, 2 * n + 1) :=
      Nat.maxPowDvdDiv_of_pow_mul_eq hpos.ne' (Nat.mul_comm _ _) (by omega)
    simp [Nat.sub_add_cancel hpos, padicValNat, Nat.divMaxPow, hparts]
    omega
  right_inv := by
    intro p
    have hodd : ¬ 2 ∣ (p + 1).divMaxPow 2 := Nat.not_dvd_divMaxPow (by decide) p.succ_ne_zero
    have h : 2 * ((p + 1).divMaxPow 2 / 2) + 1 = (p + 1).divMaxPow 2 := by omega
    simp [h]

end tsum_twoAdic_high_regroup

/-- **Regrouping the multiples of a power of 2 by their 2-adic factorization.** For every
natural number $J$ and every sequence $(c_m)_{m \ge 1}$ of complex numbers,
$$\sum_{j \ge J,\, n \ge 1} c_{(2n-1) 2^j} = \sum_{p \ge 1} c_{p 2^J},$$
where the left side is an unconditional sum over the pairs $(j, n)$. No summability is assumed:
$(j, n) \mapsto (2n-1) 2^{j-J}$ is a bijection onto the positive integers, so the two families
are summable together or not at all, and a non-summable family has sum $0$ by convention.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Corollary 14, first display in sum form (`jis-2024-24.5.5-cor-14`). -/
public theorem tsum_twoAdic_high_regroup (J : ℕ) (c : ℕ → ℂ) :
    ∑' x : ℕ × ℕ, c ((2 * x.2 + 1) * 2 ^ (x.1 + J)) = ∑' p : ℕ, c ((p + 1) * 2 ^ J) := by
  have hpos (x : ℕ × ℕ) : 0 < (2 * x.2 + 1) * 2 ^ x.1 := by positivity
  simpa only [tsum_twoAdic_high_regroup.indexEquiv, Equiv.coe_fn_mk, Nat.sub_add_cancel (hpos _),
    pow_add, Nat.mul_assoc] using
    tsum_twoAdic_high_regroup.indexEquiv.tsum_eq (fun p => c ((p + 1) * 2 ^ J))

/-- **2-adic product factorization of the Euler function.** For every complex number $q$ with
$|q| < 1$, with the infinite q-Pochhammer symbol $(a; r)_\infty = \prod_{k \ge 0} (1 - a r^k)$,
the unconditional infinite product over $j \ge 0$ satisfies
$\prod_{j \ge 0} (q^{2^j}; q^{2^{j+1}})_\infty = (q; q)_\infty$.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 19, case `p = 1`, base 2 (`jis-2024-24.5.5-prop-19`). -/
public theorem tprod_qPochhammer_twoAdic_factorization (q : ℂ) (hq : ‖q‖ < 1) :
    ∏' j : ℕ, QPochhammer.qPochhammerInf (q ^ 2 ^ j) (q ^ 2 ^ (j + 1))
        (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity))
      = QPochhammer.qPochhammerInf q q hq := by
  have hbase (j : ℕ) : ‖q ^ 2 ^ (j + 1)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by positivity)
  have hEuler : HasProd (fun n : ℕ => 1 - q ^ (n + 1)) (QPochhammer.qPochhammerInf q q hq) := by
    simpa only [pow_succ'] using QPochhammer.hasProd_qPochhammerInf q q hq
  have hreindexed := tsum_twoAdic_high_regroup.indexEquiv.hasProd_iff.mpr hEuler
  have hf : HasProd (fun x : ℕ × ℕ => 1 - q ^ 2 ^ x.1 * (q ^ 2 ^ (x.1 + 1)) ^ x.2)
      (QPochhammer.qPochhammerInf q q hq) := by
    refine hreindexed.congr_fun ?_
    rintro ⟨j, n⟩
    have hpos : 0 < (2 * n + 1) * 2 ^ j := by positivity
    have hexp : 2 ^ j + 2 ^ (j + 1) * n = (2 * n + 1) * 2 ^ j := by
      rw [pow_succ]
      ring
    change 1 - q ^ 2 ^ j * (q ^ 2 ^ (j + 1)) ^ n = 1 - q ^ ((2 * n + 1) * 2 ^ j - 1 + 1)
    rw [Nat.sub_add_cancel hpos, ← pow_mul, ← pow_add, hexp]
  exact (hf.prod_fiberwise fun j =>
    QPochhammer.hasProd_qPochhammerInf (q ^ 2 ^ j) (q ^ 2 ^ (j + 1)) (hbase j)).tprod_eq

end MetaMathlibExt
