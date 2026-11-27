/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Defs
public import MathlibExt.Combinatorics.Enumerative.Partition.KTupleRegularPartitions
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.MvPowerSeries.Ideal
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.ZMod
import all MathlibExt.Combinatorics.Enumerative.Partition.KTupleRegularPartitions

/-!
# Prime-power congruences for tuples of regular partitions

For a prime $p$, positive $m$, $\ell$ and $s$, and natural numbers $\alpha \ge s$, $n$ and
$1 \le r \le p^s - 1$, the count of $\ell$-regular $p^\alpha m$-tuples of total $p^s n+r$
is divisible by $p^{\alpha-s+1}$. We apply Frobenius directly to the partition generating
series, then lift the congruence and use the vanishing of coefficients off multiples of $p^s$.

## References

* Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia,
  and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, pp. 1–10,
  Theorem 3 and Lemma 7.
* Robson da Silva and James A. Sellers, *Infinitely Many Congruences for k-Regular Partitions
  with Designated Summands*, Bulletin of the Brazilian Mathematical Society, New Series 51
  (2020), pp. 357–370, Lemma 3, cited by Paudel, Sellers, and Wang for their Lemma 6.
* The generating-series coefficient formula is `coeff_lRegularSeries_pow` in
  `MathlibExt.Combinatorics.Enumerative.Partition.KTupleRegularPartitions`. The prime-power
  lifting step follows `qEulerProduct_iterated_primePower_congruence` in
  `MathlibExt.Combinatorics.Enumerative.Partition.QEulerProductCongruence`.
-/

open PowerSeries

namespace MetaMathlibExt

-- Keep the positivity hypotheses of Theorem 3; the series argument does not need all of them.
set_option linter.unusedVariables false in
/--
**Prime-power congruences for $k$-tuples of $\ell$-regular partitions.** Write $T_{\ell,k}(n)$
for the number of $k$-tuples of $\ell$-regular partitions with total $n$. Let $p$ be a prime,
let $m$, $\ell$ and $s$ be positive integers, let $\alpha \ge s$ and $r$ be natural numbers
with $1 \le r \le p^s - 1$. Then for every natural number $n$,
$$T_{\ell,p^\alpha m}(p^s n + r) \equiv 0 \pmod{p^{\alpha - s + 1}}.$$

Since $s$ is positive, the hypothesis $\alpha \ge s$ also gives $\alpha \ge 1$.

Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia,
and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Theorem 3.
-/
public theorem kTupleRegularPartition_primePower_congruent (p m ℓ α s r n : ℕ)
    (hp : Nat.Prime p) (hm : 0 < m) (hℓ : 0 < ℓ) (hs : 0 < s) (hsα : s ≤ α) (hr₁ : 1 ≤ r) (hrp : r ≤
        p ^ s - 1) :
    Nat.ModEq (p ^ (α - s + 1))
      (kTupleRegularPartitionCount ℓ (p ^ α * m) (p ^ s * n + r)) 0 := by
  let : Fact p.Prime := ⟨hp⟩
  let f := lRegularSeries ℤ ℓ
  have hps : p ^ s ≠ 0 := pow_ne_zero s hp.ne_zero
  let E := expand (p ^ s) hps (R := ℤ)
  let ρ := map (Int.castRingHom (ZMod p))
  have hker : RingHom.ker ρ = Ideal.span {(p : ℤ⟦X⟧)} := by
    change RingHom.ker (MvPowerSeries.map (σ := Unit) (Int.castRingHom (ZMod p))) = _
    rw [MvPowerSeries.ker_map_of_fg, ZMod.ker_intCastRingHom, Ideal.map_span,
      Set.image_singleton, map_natCast]
    rw [ZMod.ker_intCastRingHom]
    exact Submodule.fg_span_singleton _
  have hbase : (p : ℤ⟦X⟧) ∣ f ^ p ^ s - E f := by
    rw [← Ideal.mem_span_singleton, ← hker, RingHom.mem_ker, map_sub, sub_eq_zero]
    dsimp only [E, ρ]
    rw [map_pow, map_expand]
    have hfrob : iterateFrobenius (ZMod p) p s = RingHom.id _ :=
      RingHom.ext fun x => ZMod.pow_card_pow x
    simpa only [hfrob, map_id, id_eq] using (map_iterateFrobenius_expand p hp.ne_zero (ρ f) s).symm
  have hpow : p ^ s * p ^ (α - s) = p ^ α := by rw [← pow_add, Nat.add_sub_of_le hsα]
  have hlift := (dvd_sub_pow_of_dvd_sub hbase (α - s)).trans (sub_dvd_pow_sub_pow _ _ m)
  obtain ⟨g, hg⟩ := hlift
  rw [← pow_mul f (p ^ s), hpow, ← pow_mul f, ← map_pow E, ← map_pow E] at hg
  have hindex : ¬ p ^ s ∣ p ^ s * n + r := by
    rw [← Nat.dvd_add_iff_right (dvd_mul_right (p ^ s) n)]
    exact Nat.not_dvd_of_pos_of_lt hr₁ (by omega)
  have hzero : coeff (p ^ s * n + r) (E ((f ^ p ^ (α - s)) ^ m)) = 0 :=
    coeff_expand_of_not_dvd _ _ _ hindex
  apply Nat.modEq_zero_iff_dvd.mpr
  apply Int.natCast_dvd_natCast.mp
  refine ⟨coeff (p ^ s * n + r) g, ?_⟩
  simpa only [map_sub, hzero, sub_zero, ← Nat.cast_pow, coeff_natCast_mul, f,
    coeff_lRegularSeries_pow] using congrArg (coeff (p ^ s * n + r)) hg

end MetaMathlibExt
