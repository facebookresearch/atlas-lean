/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Series.BaseAdicMultiples
public import MathlibExt.Analysis.SpecialFunctions.QPochhammer
import Mathlib.Data.Nat.PadicValNat
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Regrouping the multiples of three

In base three the finite sum over nonzero residues has two terms, with cofactors
`3 * n + 2` and `3 * n + 1`.
-/

namespace MetaMathlibExt

/-- **Regrouping the multiples of 3 by their 3-adic factorization.** Let $(b_m)_{m \ge 1}$ be a
sequence of complex numbers such that the family $(b_{3m})_{m \ge 1}$ is summable. Then
$$\sum_{j \ge 1,\, n \ge 1} \bigl( b_{(3n-1) 3^j} + b_{(3n-2) 3^j} \bigr) =
\sum_{m \ge 1} b_{3m},$$
where the sum on the left is an unconditional sum over the pairs $(j, n)$.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Corollary 6, deduced identity in sum form (`jis-2024-24.5.5-cor-6`). -/
public theorem tsum_threeAdic_multiples_regroup (b : ℕ → ℂ)
    (hb : Summable fun m : ℕ => b (3 * (m + 1))) :
    ∑' x : ℕ × ℕ, (b ((3 * x.2 + 2) * 3 ^ (x.1 + 1)) + b ((3 * x.2 + 1) * 3 ^ (x.1 + 1)))
      = ∑' m : ℕ, b (3 * (m + 1)) := by
  simpa [Fin.sum_univ_two, Nat.mul_succ] using
    tsum_baseAdic_multiples_regroup 3 (by decide) b hb

-- Index the positive integers, shifted down by one, by valuation, residue, and block.
private def threeAdicIndex : ((ℕ × Fin 2) × ℕ) ≃ ℕ where
  toFun x := 3 ^ x.1.1 * (3 * x.2 + ((x.1.2 : ℕ) + 1)) - 1
  invFun m :=
    let t := (m + 1).divMaxPow 3
    have ht : t % 3 ≠ 0 := Nat.dvd_iff_mod_eq_zero.not.mp
      (Nat.not_dvd_divMaxPow (by decide) (Nat.succ_ne_zero m))
    ((padicValNat 3 (m + 1), ⟨t % 3 - 1, by omega⟩), t / 3)
  left_inv := by
    rintro ⟨⟨j, i⟩, n⟩
    have hi := i.isLt
    have hm : (3 * n + ((i : ℕ) + 1)) % 3 = (i : ℕ) + 1 := by omega
    have hd : (3 * n + ((i : ℕ) + 1)) / 3 = n := by omega
    have hpos : 0 < 3 ^ j * (3 * n + ((i : ℕ) + 1)) := by positivity
    have hparts := Nat.maxPowDvdDiv_of_pow_mul_eq hpos.ne' rfl
      (show ¬3 ∣ 3 * n + ((i : ℕ) + 1) by rw [Nat.dvd_iff_mod_eq_zero, hm]; omega)
    dsimp only
    simp only [Nat.sub_add_cancel hpos, padicValNat, Nat.divMaxPow, hparts, hm, hd,
      Nat.add_sub_cancel, Fin.eta]
  right_inv := by
    intro m
    let t := (m + 1).divMaxPow 3
    have ht : t % 3 ≠ 0 := Nat.dvd_iff_mod_eq_zero.not.mp
      (Nat.not_dvd_divMaxPow (by decide) (Nat.succ_ne_zero m))
    change 3 ^ padicValNat 3 (m + 1) * (3 * (t / 3) + (t % 3 - 1 + 1)) - 1 = m
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero ht), Nat.div_add_mod,
      Nat.mul_comm, Nat.divMaxPow_mul_pow_padicValNat, Nat.add_sub_cancel]

/-- **$3$-adic factorization of the Euler function.** Write
$(x; y)_\infty = \prod_{k \ge 0} (1 - x y^k)$ for the infinite $q$-Pochhammer symbol, where $x$
and $y$ are complex and $|y| < 1$. For every complex number $q$ with $|q| < 1$,
$\prod_{j \ge 0} (q^{3^j}; q^{3^{j+1}})_\infty\, (q^{2 \cdot 3^j}; q^{3^{j+1}})_\infty =
(q; q)_\infty$.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 19, case `p = 1`, base 3 (`jis-2024-24.5.5-prop-19`). -/
public theorem tprod_qPochhammer_threeAdic_factorization (q : ℂ) (hq : ‖q‖ < 1) :
    ∏' j : ℕ, (QPochhammer.qPochhammerInf (q ^ 3 ^ j) (q ^ 3 ^ (j + 1))
          (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity))
        * QPochhammer.qPochhammerInf (q ^ (2 * 3 ^ j)) (q ^ 3 ^ (j + 1))
          (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity)))
      = QPochhammer.qPochhammerInf q q hq := by
  let hbase (j : ℕ) : ‖q ^ 3 ^ (j + 1)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by positivity)
  let f (x : (ℕ × Fin 2) × ℕ) : ℂ :=
    1 - q ^ (((x.1.2 : ℕ) + 1) * 3 ^ x.1.1) * (q ^ 3 ^ (x.1.1 + 1)) ^ x.2
  have hEuler : HasProd (fun n : ℕ => 1 - q ^ (n + 1)) (QPochhammer.qPochhammerInf q q hq) := by
    simpa only [pow_succ'] using QPochhammer.hasProd_qPochhammerInf q q hq
  -- Reindex the ungrouped product before taking either of the fiber products.
  have hreindexed : HasProd ((fun n : ℕ => 1 - q ^ (n + 1)) ∘ threeAdicIndex)
      (QPochhammer.qPochhammerInf q q hq) :=
    threeAdicIndex.hasProd_iff.mpr hEuler
  have hfactors (x : (ℕ × Fin 2) × ℕ) : f x = 1 - q ^ (threeAdicIndex x + 1) := by
    obtain ⟨⟨j, i⟩, n⟩ := x
    change 1 - q ^ (((i : ℕ) + 1) * 3 ^ j) * (q ^ 3 ^ (j + 1)) ^ n =
      1 - q ^ (3 ^ j * (3 * n + ((i : ℕ) + 1)) - 1 + 1)
    have hpos : 0 < 3 ^ j * (3 * n + ((i : ℕ) + 1)) := by positivity
    have he : ((i : ℕ) + 1) * 3 ^ j + 3 ^ (j + 1) * n =
        3 ^ j * (3 * n + ((i : ℕ) + 1)) := by rw [pow_succ]; ring
    rw [Nat.sub_add_cancel hpos, ← pow_mul, ← pow_add, he]
  have hf : HasProd f (QPochhammer.qPochhammerInf q q hq) :=
    hreindexed.congr_fun hfactors
  let g (j : ℕ) (i : Fin 2) : ℂ :=
    QPochhammer.qPochhammerInf (q ^ (((i : ℕ) + 1) * 3 ^ j))
      (q ^ 3 ^ (j + 1)) (hbase j)
  have hblocks (j : ℕ) (i : Fin 2) : HasProd (fun n : ℕ => f ((j, i), n)) (g j i) :=
    QPochhammer.hasProd_qPochhammerInf (q ^ (((i : ℕ) + 1) * 3 ^ j))
      (q ^ 3 ^ (j + 1)) (hbase j)
  have hresidue : HasProd (fun x : ℕ × Fin 2 => g x.1 x.2)
      (QPochhammer.qPochhammerInf q q hq) :=
    hf.prod_fiberwise (fun x => hblocks x.1 x.2)
  have hgrouped : HasProd (fun j : ℕ => ∏ i : Fin 2, g j i)
      (QPochhammer.qPochhammerInf q q hq) :=
    hresidue.prod_fiberwise (fun j => hasProd_fintype (g j))
  simpa only [g, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, zero_add, one_mul] using
    hgrouped.tprod_eq

end MetaMathlibExt
