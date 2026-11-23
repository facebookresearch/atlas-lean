/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Nat.PadicValNat
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Regrouping a series along the multiples of a base

The maximal power of the base dividing a positive integer determines its exponent.
Dividing the remaining factor by the base determines the block and its nonzero residue.
-/

namespace MetaMathlibExt
namespace tsum_baseAdic_multiples_regroup

variable {B : ℕ}

/-- The factor in the block above `B * n` with residue `B - (i + 1)`. -/
private def cofactor (n : ℕ) (i : Fin (B - 1)) : ℕ := B * n + (B - (i + 1))

private theorem cofactor_pos (n : ℕ) (i : Fin (B - 1)) : 0 < cofactor n i := by
  have hi := i.isLt
  unfold cofactor
  omega

private theorem cofactor_mod (n : ℕ) (i : Fin (B - 1)) :
    cofactor n i % B = B - (i + 1) := by
  have hi := i.isLt
  simp [cofactor, Nat.mod_eq_of_lt (show B - (i + 1) < B by omega)]

private theorem cofactor_div (n : ℕ) (i : Fin (B - 1)) :
    cofactor n i / B = n := by
  have hi := i.isLt
  simp [cofactor, Nat.mul_add_div (show 0 < B by omega),
    Nat.div_eq_of_lt (show B - (i + 1) < B by omega)]

/-- Enumerate positive integers (shifted down by one) by exponent, block, and residue. -/
private def indexEquiv (hB : 2 ≤ B) : ((ℕ × ℕ) × Fin (B - 1)) ≃ ℕ where
  toFun x := B ^ x.1.1 * cofactor x.1.2 x.2 - 1
  invFun m :=
    let t := (m + 1).divMaxPow B
    have ht : t % B ≠ 0 := Nat.dvd_iff_mod_eq_zero.not.mp
      (Nat.not_dvd_divMaxPow hB (Nat.succ_ne_zero m))
    ((padicValNat B (m + 1), t / B), ⟨B - 1 - t % B, by omega⟩)
  left_inv := by
    rintro ⟨⟨j, n⟩, i⟩
    have hi := i.isLt
    have hnd : ¬B ∣ cofactor n i := by
      rw [Nat.dvd_iff_mod_eq_zero, cofactor_mod]
      omega
    have hpos : 0 < B ^ j * cofactor n i :=
      Nat.mul_pos (Nat.pow_pos (by omega)) (cofactor_pos n i)
    have hparts := Nat.maxPowDvdDiv_of_pow_mul_eq hpos.ne' rfl hnd
    dsimp only
    simp only [Nat.sub_add_cancel hpos, padicValNat, Nat.divMaxPow, hparts,
      cofactor_mod, cofactor_div, Prod.mk.injEq, true_and]
    apply Fin.ext
    dsimp
    omega
  right_inv := by
    intro m
    let t := (m + 1).divMaxPow B
    have hlt : t % B < B := Nat.mod_lt _ (by omega)
    have hne : t % B ≠ 0 := Nat.dvd_iff_mod_eq_zero.not.mp
      (Nat.not_dvd_divMaxPow hB (Nat.succ_ne_zero m))
    have hr : B - (B - 1 - t % B + 1) = t % B := by omega
    change B ^ padicValNat B (m + 1) * (B * (t / B) + (B - (B - 1 - t % B + 1))) - 1 = m
    rw [hr, Nat.div_add_mod, Nat.padicValNat_def, Nat.pow_multiplicity_mul_divMaxPow,
      Nat.add_sub_cancel]

private theorem indexEquiv_summand (hB : 2 ≤ B) (x : (ℕ × ℕ) × Fin (B - 1)) :
    B * (indexEquiv hB x + 1) = (B * (x.1.2 + 1) - (x.2 + 1)) * B ^ (x.1.1 + 1) := by
  obtain ⟨⟨j, n⟩, i⟩ := x
  have hi := i.isLt
  have hpos := Nat.mul_pos (Nat.pow_pos (n := j) (show 0 < B by omega)) (cofactor_pos n i)
  change B * (B ^ j * cofactor n i - 1 + 1) = (B * (n + 1) - (i + 1)) * B ^ (j + 1)
  rw [Nat.sub_add_cancel hpos, pow_succ, Nat.mul_succ, Nat.add_sub_assoc (by omega)]
  unfold cofactor
  ac_rfl

end tsum_baseAdic_multiples_regroup

open tsum_baseAdic_multiples_regroup

/-- **Regrouping the multiples of B by their B-adic factorization.** Let $B \ge 2$ be a natural
number and let $(c_m)_{m \ge 1}$ be a sequence of complex numbers such that the family
$(c_{Bm})_{m \ge 1}$ is summable. Then
$$\sum_{j \ge 1,\, n \ge 1} \sum_{k=1}^{B-1} c_{(Bn-k) B^j} = \sum_{m \ge 1} c_{Bm},$$
where the outer sum on the left is an unconditional sum over the pairs $(j, n)$.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 7, deduced identity in sum form (`jis-2024-24.5.5-prop-7`). -/
public theorem tsum_baseAdic_multiples_regroup (B : ℕ) (hB : 2 ≤ B) (c : ℕ → ℂ)
    (hc : Summable fun m : ℕ => c (B * (m + 1))) :
    ∑' x : ℕ × ℕ, ∑ i : Fin (B - 1), c ((B * (x.2 + 1) - (i + 1)) * B ^ (x.1 + 1))
      = ∑' m : ℕ, c (B * (m + 1)) := by
  have h := (indexEquiv hB).hasSum_iff.mpr hc.hasSum
  simp only [Function.comp_def, indexEquiv_summand] at h
  exact (h.prod_fiberwise fun _ => hasSum_fintype _).tsum_eq

end MetaMathlibExt
