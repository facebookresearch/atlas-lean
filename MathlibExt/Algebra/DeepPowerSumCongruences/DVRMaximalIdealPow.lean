/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import MathlibExt.Algebra.DeepPowerSumCongruences.DividedPowerIdeal

import Mathlib.Algebra.CharP.Invertible
import MathlibExt.Algebra.DeepPowerSumCongruences.DividedPowerSpan
import MathlibExt.RingTheory.LocalRing.CharP

/-!
# The divided-power criterion for powers of a DVR maximal ideal

## References

- Samuele Anni, Alexandru Ghitza and Anna Medvedovsky, *Elementary Symmetric Functions and Deep
  Power-Sum Congruences*, INTEGERS 24 (2024), Article A46, pp. 1–26, Lemma 7. We use their
  generator test (Proposition 5) and compare the valuations of the two principal ideals.
  Membership requires a weak inequality, in agreement with Corollary 8 for `k = 1`, rather than
  the strict inequality printed in Lemma 7.
- Pierre Berthelot and Arthur Ogus, *Notes on Crystalline Cohomology*, Mathematical Notes 21,
  Princeton University Press and University of Tokyo Press, 1978, §3, cited in §2.2 for the
  divided-power structure in the torsion-free setting.
- Matthieu Romagny, *Some useful p-adic formulas*, notes cited in the proof of Proposition 3
  for the digit-sum form of Legendre's formula used upstream of the generator criterion.
-/

namespace MetaMathlibExt

open IsDiscreteValuationRing IsLocalRing

/-- **Powers of the maximal ideal of a DVR that are divided-power ideals.** Let $p$ be a prime and
let $O$ be a discrete valuation ring with maximal ideal $\mathfrak{m}$ such that
$pO = \mathfrak{m}^e$ for some integer $e \ge 1$. Then for every $k \ge 0$, the ideal
$\mathfrak{m}^k$ is a divided-power ideal if and only if $e \le (p - 1)k$.

Equivalently, with $v_p(\mathfrak{m}) = 1/e$, the condition is $v_p(\mathfrak{m}^k) \ge 1/(p - 1)$.
The paper states this for $p$-adic discrete valuation rings and remarks that it also holds for
localizations of rings of integers; here $O$ is any such ring, and the zero ideal is omitted.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Lemma 7 (`integers-2024-A46-lem-7`). -/
public theorem isDividedPowerIdeal_maximalIdeal_pow_iff {p : ℕ} [Fact p.Prime]
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {e : ℕ} (he0 : e ≠ 0)
    (he : Ideal.span {(p : O)} = IsLocalRing.maximalIdeal O ^ e) (k : ℕ) :
    IsDividedPowerIdeal (IsLocalRing.maximalIdeal O ^ k) ↔ e ≤ (p - 1) * k := by
  have hpMem : (p : O) ∈ maximalIdeal O := by
    apply Ideal.pow_le_self he0
    rw [← he]
    exact Ideal.mem_span_singleton_self _
  let : CharP (ResidueField O) p := charP_residueField_of_natCast_mem_maximalIdeal O p hpMem
  have hUnit (n : ℕ) : ¬ p ∣ n → IsUnit (n : O) := by
    rw [← residue_ne_zero_iff_isUnit, map_natCast, ← isUnit_iff_ne_zero]
    exact (CharP.isUnit_natCast_iff (Fact.out : p.Prime)).mpr
  let I := maximalIdeal O ^ k
  let a := Submodule.IsPrincipal.generator I
  have hI : Ideal.span {a} = I := Ideal.span_singleton_generator I
  calc
    IsDividedPowerIdeal I ↔ ∃ c ∈ I, a ^ p = (p : O) * c := by
      rw [← hI, isDividedPowerIdeal_span_iff hUnit]
      simp only [Set.mem_singleton_iff, forall_eq]
    _ ↔ I ^ p ≤ Ideal.span {(p : O)} * I := by
      rw [← hI, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem,
        Ideal.mem_span_singleton_mul]
      simp only [eq_comm]
    _ ↔ e + k ≤ k * p := by
      change (maximalIdeal O ^ k) ^ p ≤ Ideal.span {(p : O)} * maximalIdeal O ^ k ↔ _
      rw [he, ← pow_add, ← pow_mul, ← idealOrderIsoENat_symm_apply_coe O (k * p),
        ← idealOrderIsoENat_symm_apply_coe O (e + k), OrderIso.le_iff_le]
      exact ENat.natCast_le_natCast
    _ ↔ e ≤ (p - 1) * k := by
      rw [Nat.sub_mul, Nat.one_mul, Nat.mul_comm p k]
      omega

end MetaMathlibExt
