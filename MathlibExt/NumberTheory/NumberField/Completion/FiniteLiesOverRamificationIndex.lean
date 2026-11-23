/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

public import MathlibExt.NumberTheory.NumberField.Completion.FiniteLiesOverInertiaDegree
public import MathlibExt.RingTheory.RamificationInertia.Valuation

/-!
# Ramification index under finite-place completion

## ATLAS source correspondence

This proves the ramification-index half of ATLAS NumberTheoryI N265, Theorem
13.5's local-degree compatibility. At atlas-lean commit
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`, the exact source theorem is
[`part_3a_ramification_idx_preserved` in
`v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean`, lines 2155--2186](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean#L2155-L2186).
It states
that for primes `𝔮 ∣ 𝔭`, the ramification index of the extension of completed
integer rings equals the original ideal-theoretic ramification index
`e(𝔮/𝔭)`. Its comparison engine is
[`ch8_10_completion_ramificationIdx_eq`, lines 2090--2119](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean#L2090-L2119).

## Source-to-API map

Here `A = 𝓞 K`, `B = 𝓞 L`, `𝔭 = v.asIdeal`, and `𝔮 = w.asIdeal`.
`ramificationIdx_adicCompletionIntegersMap` is exactly the source equality,
using the canonical map `adicCompletionIntegersMap v w`; its injectivity and
locality are established immediately above/in the proof, while the preceding
completion stages supply lies-over and compatibility with the field map.

The valuation normalization is explicit. `valued_irreducible_eq_exp_neg_one`
uses Mathlib's surjective rank-one discrete valuation on each completion and
shows every uniformizer has value `WithZero.exp (-1)`. The prior valuation
formula then sends a downstairs uniformizer to value
`WithZero.exp (-e(𝔮/𝔭))`, so it is associated to the `e(𝔮/𝔭)`-th power of an
upstairs uniformizer. `addVal_algebraMap_eq_ramificationIdx_mul` converts that
associatedness into the same ideal-theoretic ramification index used in the
source. Thus no alternate absolute-value normalization or reciprocal exponent
is being used.

This module proves only preservation of ramification index. Preservation of
residue degree and the final local-degree/tensor-product statements are
separate N265 stages.
-/

@[expose] public section

namespace IsDedekindDomain.HeightOneSpectrum

open scoped WithZero NumberField NumberField.LiesOver

variable {F : Type*} [Field F] [NumberField F]
variable (v : HeightOneSpectrum (𝓞 F))

private theorem valued_irreducible_eq_exp_neg_one
    {pi : v.adicCompletionIntegers F} (hpi : Irreducible pi) :
    Valued.v (pi : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
  have hU : Valuation.IsUniformizer (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)
      (pi : v.adicCompletion F) :=
    Valuation.isUniformizer_of_maximalIdeal_eq_span _ hpi.maximalIdeal_eq
  rw [Valuation.IsUniformizer.val hU]
  exact congrArg Units.val
    (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (valuedAdicCompletion_surjective F v))

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable [w.asIdeal.LiesOver v.asIdeal]
/-- **The map of completed integer rings is injective.** Let $L/K$ be an extension of number
fields, let $v$ be a nonzero prime ideal of $\mathcal{O}_K$ and $w$ a nonzero prime ideal of
$\mathcal{O}_L$ lying over $v$. Then the canonical map $\mathcal{O}_{K_v} \to \mathcal{O}_{L_w}$
from the ring of integers of the completion $K_v$ to the ring of integers of the completion $L_w$
is injective. -/
theorem adicCompletionIntegersMap_injective :
    Function.Injective (adicCompletionIntegersMap v w) := by
  intro x y h
  apply Subtype.ext
  apply adicCompletionMap_injective v w
  simpa only [adicCompletionIntegersMap_apply] using congrArg Subtype.val h

/-- **Completion preserves the ramification index.** Let $L/K$ be an extension of number fields,
let $v$ be a nonzero prime ideal of $\mathcal{O}_K$ and $w$ a nonzero prime ideal of
$\mathcal{O}_L$ lying over $v$. Let $\mathcal{O}_{K_v}$ and $\mathcal{O}_{L_w}$ be the rings of
integers of the completions $K_v$ and $L_w$, with $\mathcal{O}_{L_w}$ an algebra over
$\mathcal{O}_{K_v}$ via the canonical map. Then the ramification index of the maximal ideal of
$\mathcal{O}_{L_w}$ over $\mathcal{O}_{K_v}$ equals the ramification index of $w$ over $v$. -/
theorem ramificationIdx_adicCompletionIntegersMap :
    (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)).ramificationIdx
      (v.adicCompletionIntegers K) =
      w.asIdeal.ramificationIdx (𝓞 K) := by
  let _ : Algebra (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) :=
    (adicCompletionIntegersMap v w).toAlgebra
  have halg : algebraMap (v.adicCompletionIntegers K)
      (w.adicCompletionIntegers L) = adicCompletionIntegersMap v w := rfl
  let _ : FaithfulSMul (v.adicCompletionIntegers K)
      (w.adicCompletionIntegers L) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (halg ▸ adicCompletionIntegersMap_injective v w)
  let _ : Module.IsTorsionFree (v.adicCompletionIntegers K)
      (w.adicCompletionIntegers L) := inferInstance
  let _ : IsLocalHom (algebraMap (v.adicCompletionIntegers K)
      (w.adicCompletionIntegers L)) :=
    IsLocalHom.mk (fun x hx => by
      by_contra hxnu
      have hxmem : x ∈ IsLocalRing.maximalIdeal
          (v.adicCompletionIntegers K) :=
        (IsLocalRing.mem_maximalIdeal x).mpr ((mem_nonunits_iff).mpr hxnu)
      have hcomap := comap_maximalIdeal_adicCompletionIntegersMap v w
      have himg : algebraMap (v.adicCompletionIntegers K)
          (w.adicCompletionIntegers L) x ∈ IsLocalRing.maximalIdeal
          (w.adicCompletionIntegers L) := by
        rw [halg]
        have hmem : x ∈ Ideal.comap (adicCompletionIntegersMap v w)
            (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)) := by
          rw [hcomap]
          exact hxmem
        exact hmem
      exact (((mem_nonunits_iff).mp ((IsLocalRing.mem_maximalIdeal _).mp himg)) hx))
  obtain ⟨pi_v, hpi_v⟩ :=
    IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  obtain ⟨pi_w, hpi_w⟩ :=
    IsDiscreteValuationRing.exists_irreducible (w.adicCompletionIntegers L)
  have hval : Valued.v
      ((adicCompletionIntegersMap v w pi_v : w.adicCompletionIntegers L) :
        w.adicCompletion L) =
      Valued.v (((pi_w ^ w.asIdeal.ramificationIdx (𝓞 K) :
        w.adicCompletionIntegers L)) : w.adicCompletion L) := by
    rw [adicCompletionIntegersMap_apply, valuation_adicCompletionMap,
      valued_irreducible_eq_exp_neg_one v hpi_v]
    change _ = Valued.v ((pi_w : w.adicCompletion L) ^ w.asIdeal.ramificationIdx (𝓞 K))
    rw [map_pow,
      valued_irreducible_eq_exp_neg_one w hpi_w,
      Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]
  have hassoc : Associated (adicCompletionIntegersMap v w pi_v)
      (pi_w ^ w.asIdeal.ramificationIdx (𝓞 K)) := by
    have hv : Valuation.Integers (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰)
        (w.adicCompletionIntegers L) :=
      Valuation.valuationSubring.integers _
    apply associated_of_dvd_dvd
    · exact hv.dvd_of_le (by
        change Valued.v (((pi_w ^ w.asIdeal.ramificationIdx (𝓞 K) :
            w.adicCompletionIntegers L)) : w.adicCompletion L) ≤
          Valued.v (((adicCompletionIntegersMap v w pi_v :
            w.adicCompletionIntegers L)) : w.adicCompletion L)
        exact hval.ge)
    · exact hv.dvd_of_le (by
        change Valued.v (((adicCompletionIntegersMap v w pi_v :
            w.adicCompletionIntegers L)) : w.adicCompletion L) ≤
          Valued.v (((pi_w ^ w.asIdeal.ramificationIdx (𝓞 K) :
            w.adicCompletionIntegers L)) : w.adicCompletion L)
        exact hval.le)
  have hadd : IsDiscreteValuationRing.addVal (w.adicCompletionIntegers L)
      (algebraMap (v.adicCompletionIntegers K)
        (w.adicCompletionIntegers L) pi_v) =
      IsDiscreteValuationRing.addVal (w.adicCompletionIntegers L)
        (pi_w ^ w.asIdeal.ramificationIdx (𝓞 K)) := by
    have hassoc' : Associated (algebraMap (v.adicCompletionIntegers K)
        (w.adicCompletionIntegers L) pi_v)
        (pi_w ^ w.asIdeal.ramificationIdx (𝓞 K)) := halg ▸ hassoc
    have h := (IsDiscreteValuationRing.addVal_eq_iff_associated _ _).mpr hassoc'
    exact h
  rw [hpi_w.addVal_pow] at hadd
  have hscale := IsDiscreteValuationRing.addVal_algebraMap_eq_ramificationIdx_mul
    (A := v.adicCompletionIntegers K) (B := w.adicCompletionIntegers L) pi_v
  rw [halg] at hscale hadd
  simp only [IsDiscreteValuationRing.addVal_uniformizer hpi_v, mul_one] at hscale
  have hchain : ((IsLocalRing.maximalIdeal
      (w.adicCompletionIntegers L)).ramificationIdx
      (v.adicCompletionIntegers K) : ℕ∞) =
      ((w.asIdeal.ramificationIdx (𝓞 K) : ℕ) : ℕ∞) := by
    rw [← hadd, hscale]
  exact ENat.natCast_inj.mp hchain
end IsDedekindDomain.HeightOneSpectrum

-- End of file.
