/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Ring

/-!
# A signed Euler product identity

Substituting `-X` into the first Euler product and multiplying by the first and fourth
Euler products gives the cube of the second Euler product.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

namespace rescale_neg_one_qEulerProduct_identity

private theorem multipliable_factors (e : ℕ → ℕ) (he : ∀ n, n ≤ e n) :
    Multipliable (fun n ↦ (1 : ℤ⟦X⟧) - X ^ e n) := by
  simp_rw [sub_eq_add_neg]
  apply WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
  simp only [order_neg, order_X_pow]
  exact ENat.tendsto_natCast_nhds_top.comp (Filter.tendsto_atTop_mono he Filter.tendsto_id)

private theorem hasProd_first :
    HasProd (fun n : ℕ ↦ (1 : ℤ⟦X⟧) - X ^ (n + 1)) (qEulerProduct 1) := by
  simpa only [qEulerProduct, one_mul] using (WithPiTopology.multipliable_one_sub_X_pow ℤ).hasProd

private theorem hasProd_signed :
    HasProd (fun n : ℕ ↦ (1 : ℤ⟦X⟧) - (-X) ^ (n + 1)) (rescale (-1) (qEulerProduct 1)) := by
  have hcont : Continuous (rescale (-1 : ℤ)) := by
    refine continuous_iff_continuousAt.mpr fun f ↦
      (WithPiTopology.tendsto_iff_coeff_tendsto ℤ _ _ _).mpr fun d ↦ ?_
    simp only [coeff_rescale]
    exact (continuous_const.mul (WithPiTopology.continuous_coeff ℤ d)).continuousAt
  simpa only [Function.comp_def, map_sub, map_one, map_pow, rescale_neg_one_X] using
    hasProd_first.map (rescale (-1 : ℤ)) hcont

end rescale_neg_one_qEulerProduct_identity

open rescale_neg_one_qEulerProduct_identity

/--
**A signed Euler product identity.** Write $f_k = \prod_{i \ge 1} (1 - q^{ki})$ for the Euler
products, as integer power series in $q$, and let $(-q;-q)_\infty = \prod_{i \ge 1} (1 - (-q)^i)$
be $f_1$ with $q$ replaced by $-q$. Then
$$(-q;-q)_\infty \, f_1 f_4 = f_2^3.$$
This is the identity $(-q;-q)_\infty = f_2^3 / (f_1 f_4)$ with the denominator cleared.

Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia,
and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Lemma 4, equation
f1-q.
-/
public theorem rescale_neg_one_qEulerProduct_identity :
    PowerSeries.rescale (-1) (qEulerProduct 1) * qEulerProduct 1 * qEulerProduct 4 =
      qEulerProduct 2 ^ 3 := by
  let oddProduct := ∏' n : ℕ, ((1 : ℤ⟦X⟧) - X ^ (2 * (2 * n + 1)))
  have hOdd : HasProd (fun n : ℕ ↦ (1 : ℤ⟦X⟧) - X ^ (2 * (2 * n + 1))) oddProduct :=
    (multipliable_factors _ (by intro n; omega)).hasProd
  have h₂ : HasProd (fun n : ℕ ↦ (1 : ℤ⟦X⟧) - X ^ (2 * (n + 1))) (qEulerProduct 2) :=
    (multipliable_factors _ (by intro n; omega)).hasProd
  have h₄ : HasProd (fun n : ℕ ↦ (1 : ℤ⟦X⟧) - X ^ (4 * (n + 1))) (qEulerProduct 4) :=
    (multipliable_factors _ (by intro n; omega)).hasProd
  -- The exponents in the second Euler product are either 2 or 0 modulo 4.
  have hsplit : oddProduct * qEulerProduct 4 = qEulerProduct 2 :=
    (hOdd.even_mul_odd (f := fun n : ℕ ↦ (1 : ℤ⟦X⟧) - X ^ (2 * (n + 1)))
      (h₄.congr_fun fun n ↦ by ring_nf)).unique h₂
  -- Pair the signed and unsigned factors before splitting by parity.
  have hpair : oddProduct * qEulerProduct 2 ^ 2 = rescale (-1) (qEulerProduct 1) *
      qEulerProduct 1 := by
    apply HasProd.unique _ (hasProd_signed.mul hasProd_first)
    apply HasProd.even_mul_odd
    · apply hOdd.congr_fun
      intro n
      rw [(odd_two_mul_add_one n).neg_pow]
      ring
    · apply (h₂.pow 2).congr_fun
      intro n
      rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega, (even_two_mul _).neg_pow]
      ring
  calc
    _ = (oddProduct * qEulerProduct 4) * qEulerProduct 2 ^ 2 := by rw [← hpair]; ring
    _ = _ := by rw [hsplit]; ring

end MetaMathlibExt
