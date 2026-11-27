/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import MathlibExt.Algebra.DeepPowerSumCongruences.DividedPowerIdeal

import MathlibExt.Algebra.DeepPowerSumCongruences.DividedPowerSpan
import MathlibExt.RingTheory.LocalRing.CharP

/-!
# The divided-power criterion for the maximal ideal of a DVR

## References

- Samuele Anni, Alexandru Ghitza and Anna Medvedovsky, *Elementary Symmetric Functions and Deep
  Power-Sum Congruences*, INTEGERS 24 (2024), Article A46, pp. 1–26, Corollary 8. The proof uses
  the generator test of Proposition 5 and the valuation argument of Lemma 7.
- Pierre Berthelot and Arthur Ogus, *Notes on Crystalline Cohomology*, Mathematical Notes 21,
  Princeton University Press and University of Tokyo Press, 1978, §3, cited in §2.2 for the
  divided-power structure in the torsion-free setting.
- Matthieu Romagny, *Some useful p-adic formulas*, notes cited in the proof of Proposition 3
  for the digit-sum form of Legendre's formula used upstream of the generator criterion.
-/

namespace MetaMathlibExt

open IsDiscreteValuationRing IsLocalRing

/-- **When the maximal ideal of a DVR is a divided-power ideal.** Let $p$ be a prime and let $O$ be
a discrete valuation ring with maximal ideal $\mathfrak{m}$ such that $pO = \mathfrak{m}^e$ for
some integer $e \ge 1$. Then $\mathfrak{m}$ is a divided-power ideal if and only if $e \le p - 1$.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Corollary 8 (`integers-2024-A46-cor-8`). -/
public theorem isDividedPowerIdeal_maximalIdeal_iff {p : ℕ} [Fact p.Prime]
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {e : ℕ} (he0 : e ≠ 0)
    (he : Ideal.span {(p : O)} = IsLocalRing.maximalIdeal O ^ e) :
    IsDividedPowerIdeal (IsLocalRing.maximalIdeal O) ↔ e ≤ p - 1 := by
  have hpMem : (p : O) ∈ maximalIdeal O :=
    Ideal.pow_le_self he0 (he ▸ Ideal.mem_span_singleton_self (p : O))
  let : CharP (ResidueField O) p := charP_residueField_of_natCast_mem_maximalIdeal O p hpMem
  have hUnit (n : ℕ) (hn : ¬ p ∣ n) : IsUnit (n : O) := by
    apply (residue_ne_zero_iff_isUnit _).mp
    rw [map_natCast]
    exact (CharP.cast_eq_zero_iff (ResidueField O) p n).not.mpr hn
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible O
  have hmul : Ideal.span {(p : O)} * Ideal.span {ϖ} = Ideal.span {ϖ ^ (e + 1)} := by
    rw [he, ← hϖ.maximalIdeal_eq, ← pow_succ, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  rw [hϖ.maximalIdeal_eq, isDividedPowerIdeal_span_iff hUnit]
  simp only [Set.mem_singleton_iff, forall_eq]
  suffices ϖ ^ p ∈ Ideal.span {(p : O)} * Ideal.span {ϖ} ↔ e ≤ p - 1 by
    simpa only [Ideal.mem_span_singleton_mul, eq_comm] using this
  rw [hmul, Ideal.mem_span_singleton, ← addVal_le_iff_dvd, hϖ.addVal_pow, hϖ.addVal_pow,
    ENat.natCast_le_natCast]
  omega

end MetaMathlibExt
