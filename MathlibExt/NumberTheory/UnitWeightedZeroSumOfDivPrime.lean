/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Units

/-!
# Unit-weighted zero sums of multiples of a prime

Let `n = p n'` with `p` prime and let `z_1, …, z_k ∈ ℤ_n`. If the reductions of the `z_i` modulo
`n'` have a zero sum with weights in the units of `ℤ_{n'}`, then `p z_1, …, p z_k` have a zero
sum with weights in the units of `ℤ_n` (Mondal, Paul and Paul, *On Unit-Weighted Zero-Sum
Constants of `ℤ_n`*, Lemma 6.7). Two facts give this: every unit of `ℤ_{n'}` is the reduction of
a unit of `ℤ_n` (`ZMod.unitsMap_surjective`; for `n' = 0` both rings are `ℤ`), and multiplication
by `p` kills every element of `ℤ_n` whose reduction modulo `n'` vanishes.

The statement of `unitWeightedZeroSum_of_div_prime` spells out the wishlist's notation for
unit-weighted zero-sum sequences without simplifying it: the sequences stay functions `fun i => …`
applied to the index, so that the statement is the same term as the wishlist's.
-/

namespace MetaMathlibExt
namespace unitWeightedZeroSum_of_div_prime

/-- Every unit of `ℤ_{n'}` is the reduction modulo `n'` of a unit of `ℤ_{p n'}`, for `p ≠ 0`. -/
private theorem exists_isUnit_castHom_eq {p n' : ℕ} (hp : p ≠ 0) {u : ZMod n'}
    (hu : IsUnit u) :
    ∃ v : ZMod (p * n'), IsUnit v ∧ ZMod.castHom (dvd_mul_left n' p) (ZMod n') v = u := by
  rcases eq_or_ne n' 0 with rfl | hn'
  · -- For `n' = 0` both rings are `ℤ` and the reduction is the identity.
    let g := ZMod.castHom (show p * 0 ∣ 0 by simp) (ZMod (p * 0))
    refine ⟨g u, hu.map g, ?_⟩
    exact RingHom.congr_fun
      (RingHom.ext_zmod ((ZMod.castHom (dvd_mul_left 0 p) (ZMod 0)).comp g) (RingHom.id _)) u
  · have : NeZero (p * n') := ⟨mul_ne_zero hp hn'⟩
    obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective (dvd_mul_left n' p) hu.unit
    refine ⟨v, v.isUnit, ?_⟩
    rw [ZMod.castHom_apply, ← ZMod.unitsMap_val (dvd_mul_left n' p), hv, hu.unit_spec]

/-- Multiplication by `p` kills every element of `ℤ_{p n'}` whose reduction modulo `n'`
vanishes. -/
private theorem natCast_mul_eq_zero {p n' : ℕ} {w : ZMod (p * n')}
    (hw : ZMod.castHom (dvd_mul_left n' p) (ZMod n') w = 0) : (p : ZMod (p * n')) * w = 0 := by
  rw [← ZMod.intCast_zmod_cast w] at hw ⊢
  rw [map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at hw
  obtain ⟨c, hc⟩ := hw
  rw [hc, Int.cast_mul, Int.cast_natCast, ← mul_assoc, ← Nat.cast_mul, ZMod.natCast_self,
    zero_mul]

end unitWeightedZeroSum_of_div_prime

open unitWeightedZeroSum_of_div_prime in
/-- **Unit-weighted zero sums of multiples of a prime.** Let $p$ be a prime, let $n'$ and $k$ be
natural numbers, put $n = p n'$, and let $z_1, \dots, z_k \in \mathbb{Z}/n\mathbb{Z}$. Write
$\bar z_i$ for the reduction of $z_i$ modulo $n'$. If there are units $a_1, \dots, a_k$ of
$\mathbb{Z}/n'\mathbb{Z}$ with $\sum_i a_i \bar z_i = 0$, then there are units $b_1, \dots, b_k$
of $\mathbb{Z}/n\mathbb{Z}$ with $\sum_i b_i \, p z_i = 0$.

In the source the sequence $(p z_1, \dots, p z_k)$ determines the $z_i$ only modulo $n'$, so the
hypothesis does not depend on the choice of the $z_i$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Lemma 6.7 (`integers-2024-A38-lem-6-7`). -/
public theorem unitWeightedZeroSum_of_div_prime {p n' k : ℕ} (hp : p.Prime)
    (z : Fin k → ZMod (p * n'))
    (h : ∃ a : Fin k → ZMod n', (∀ i, IsUnit (a i)) ∧
      ∑ i, a i * (fun i => ZMod.castHom (dvd_mul_left n' p) (ZMod n') (z i)) i = 0) :
    ∃ a : Fin k → ZMod (p * n'), (∀ i, IsUnit (a i)) ∧
      ∑ i, a i * (fun i => (p : ZMod (p * n')) * z i) i = 0 := by
  obtain ⟨a, ha, hsum⟩ := h
  choose b hb hba using fun i => exists_isUnit_castHom_eq hp.ne_zero (ha i)
  refine ⟨b, hb, ?_⟩
  have hred : ZMod.castHom (dvd_mul_left n' p) (ZMod n') (∑ i, b i * z i) = 0 := by
    simpa only [map_sum, map_mul, hba] using hsum
  calc ∑ i, b i * ((p : ZMod (p * n')) * z i) = (p : ZMod (p * n')) * ∑ i, b i * z i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _
    _ = 0 := natCast_mul_eq_zero hred

end MetaMathlibExt
