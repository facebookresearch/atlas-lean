/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Basic
import Mathlib.Topology.Instances.ZMod

/-!
# Prime-power congruences for Euler products

Modulo a prime, raising an Euler factor to a power of the prime scales its exponent of
`X` by the same power. Lifting this identity in the integer power series ring gives the
coefficientwise congruence at higher prime powers.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

namespace qEulerProduct_iterated_primePower_congruence

private theorem hasProd_reduction (p l : ℕ) (hl : 0 < l) :
    HasProd (fun i : ℕ ↦ (1 : (ZMod p)⟦X⟧) - X ^ (l * (i + 1)))
      (map (Int.castRingHom (ZMod p)) (qEulerProduct l)) := by
  have hprod : Multipliable (fun i : ℕ ↦ (1 : ℤ⟦X⟧) - X ^ (l * (i + 1))) := by
    simp_rw [sub_eq_add_neg]
    apply WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
    simp only [order_neg, order_X_pow]
    exact ENat.tendsto_natCast_nhds_top.comp <| Filter.tendsto_atTop_mono
      (fun i ↦ Nat.le_mul_of_pos_left (i + 1) hl) (Filter.tendsto_add_atTop_nat 1)
  have hcont : Continuous (map (Int.castRingHom (ZMod p))) :=
    continuous_pi fun d ↦ (continuous_of_discreteTopology (f := fun z : ℤ ↦ (z : ZMod p))).comp
      (continuous_apply d)
  simpa [Function.comp_def, qEulerProduct] using
    hprod.hasProd.map (map (Int.castRingHom (ZMod p))) hcont

private theorem dvd_sub (p l s : ℕ) (hp : Nat.Prime p) (hl : 0 < l) :
    (p : ℤ⟦X⟧) ∣ qEulerProduct (l * p ^ s) - qEulerProduct l ^ p ^ s := by
  let : Fact p.Prime := ⟨hp⟩
  have : CharP (ZMod p)⟦X⟧ p := charP_of_injective_ringHom PowerSeries.C_injective p
  have hprod := (hasProd_reduction p l hl).pow (p ^ s)
  simp only [sub_pow_char_pow, one_pow, ← pow_mul, Nat.mul_right_comm l _ (p ^ s)] at hprod
  have hmap := hprod.unique
    (hasProd_reduction p (l * p ^ s) (Nat.mul_pos hl (pow_pos hp.pos _)))
  have hcoeff (n : ℕ) : (p : ℤ) ∣
      coeff n (qEulerProduct (l * p ^ s)) - coeff n (qEulerProduct l ^ p ^ s) := by
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ p).mp
    simpa only [← map_pow, coeff_map, Int.coe_castRingHom] using congrArg (coeff n) hmap
  choose a ha using hcoeff
  exact ⟨mk a, PowerSeries.ext fun n ↦ by simpa using ha n⟩

end qEulerProduct_iterated_primePower_congruence

set_option linter.unusedVariables false in
/--
**Iterated prime-power congruence for Euler products.** For a natural number $l$ write
$f_l = \prod_{i \ge 1} (1 - q^{li})$, an integer power series in $q$. Let $p$ be a prime and let
$k, l, s, m$ be natural numbers with $l \ge 1$, $s \ge 1$, $m \ge 1$ and $s \le k$. Then for
every natural number $n$, the coefficients of $q^n$ in $f_l^{p^k m}$ and in
$f_{l p^s}^{p^{k-s} m}$ are congruent modulo $p^{k-s+1}$.

Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia,
and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Lemma 7, equation
cor.modp^k.
-/
public theorem qEulerProduct_iterated_primePower_congruence (p k l s m : ℕ)
    (hp : Nat.Prime p) (hl : 0 < l) (hs : 0 < s) (hm : 0 < m) (hsk : s ≤ k) (n : ℕ) :
    PowerSeries.coeff n (qEulerProduct l ^ (p ^ k * m)) ≡
      PowerSeries.coeff n (qEulerProduct (l * p ^ s) ^ (p ^ (k - s) * m))
        [ZMOD (p : ℤ) ^ (k - s + 1)] := by
  have h := dvd_sub_pow_of_dvd_sub
    (qEulerProduct_iterated_primePower_congruence.dvd_sub p l s hp hl) (k - s)
  obtain ⟨f, hf⟩ := h.trans (sub_dvd_pow_sub_pow _ _ m)
  have hexp : p ^ s * p ^ (k - s) = p ^ k := by
    rw [← pow_add, Nat.add_sub_of_le hsk]
  apply Int.modEq_iff_dvd.mpr
  refine ⟨coeff n f, ?_⟩
  simpa only [← pow_mul, hexp, map_sub, ← Nat.cast_pow, coeff_natCast_mul] using
    congrArg (coeff n) hf

end MetaMathlibExt
