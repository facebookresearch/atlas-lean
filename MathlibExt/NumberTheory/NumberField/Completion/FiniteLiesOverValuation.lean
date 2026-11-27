/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.Completion.FiniteLiesOver

/-!
# Valuation formula for maps between finite-place completions

## ATLAS source-to-API map

This file is only a supporting/prerequisite stage for ATLAS NumberTheoryI item
N265; it does not prove the full tensor-product equivalence. The N265 target is
the source module `Atlas.NumberTheoryI.GlobalFields` at ATLAS revision
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`, final declaration
[`theorem_13_5_finite_place_Kv`, lines 1152--1211](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/GlobalFields.lean#L1152-L1211).

Source-to-API correspondences used here:

* Source completion map
  [`completionEmbedding_finite`, lines 693--713](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/GlobalFields.lean#L693-L713)
  is the imported `adicCompletionMap` used here. Its construction uses
  [`completionEmbedding_finite_ringHom`, lines 534--539](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/GlobalFields.lean#L534-L539),
  and the continuity work ending at
  [`completionEmbedding_finite_continuous`, lines 668--672](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/GlobalFields.lean#L668-L672).
* The second exact source is
  [`CompleteFields.valuation_extends_with_ramificationIdx`, lines 275--301](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/CompleteFields.lean#L275-L301).
  Its
  source exponent `Ideal.ramificationIdx` is Mathlib's
  `Ideal.ramificationIdx'` here (written `v.asIdeal.ramificationIdx' w.asIdeal`).
* Source [`FinitePlace.LiesAbove w v`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/GlobalFields.lean#L75-L78) corresponds to
  `[w.asIdeal.LiesOver v.asIdeal]` here (stored as a comap equality).
* `[NumberField K] [NumberField L] [Algebra K L]` plus the lies-over instance
  correspond to the source number-field extension `L/K` and finite place `w`
  above `v`.

Local API roles: `valuation_adicCompletionMap` extends the source valuation
identity from the dense embedded copy of `K` to all of `v.adicCompletion K` by
continuity; `adicCompletionMap_mem_integers` translates it to the
valuation-subring condition; and `adicCompletionIntegersMap` restricts the same
map to the integer rings.
-/

@[expose] public section

namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField
open WithZeroTopology

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

/-- **Valuation of the image under the completion map.** Let $L/K$ be an extension of number
fields, let $v$ be a finite place of $K$, given as a height-one prime of the ring of integers
$\mathcal{O}_K$, let $w$ be a finite place of $L$ lying over $v$, and let $e$ be the ramification
index of $w$ over $v$. Let $\iota : K_v \to L_w$ be the continuous ring homomorphism between the
completions that extends $K \to L$. Then for every $x \in K_v$, the valuation of $\iota(x)$ on
$L_w$ equals the $e$-th power of the valuation of $x$ on $K_v$, where both valuations are the
multiplicative adic valuations extended to the completions. -/
theorem valuation_adicCompletionMap (x : v.adicCompletion K) :
    Valued.v (adicCompletionMap v w x) =
      Valued.v x ^ v.asIdeal.ramificationIdx' w.asIdeal := by
  have hvalL :
      Continuous (Valued.v : w.adicCompletion L → WithZero (Multiplicative ℤ)) :=
    Valued.continuous_valuation_of_surjective
      (valuedAdicCompletion_surjective (R := 𝓞 L) (K := L) (v := w))
  have hvalK :
      Continuous (Valued.v : v.adicCompletion K → WithZero (Multiplicative ℤ)) :=
    Valued.continuous_valuation_of_surjective
      (valuedAdicCompletion_surjective (R := 𝓞 K) (K := K) (v := v))
  have hcontL :
      Continuous (fun x : v.adicCompletion K => Valued.v (adicCompletionMap v w x)) :=
    hvalL.comp (continuous_adicCompletionMap v w)
  have hcontR :
      Continuous
        (fun x : v.adicCompletion K =>
          Valued.v x ^ v.asIdeal.ramificationIdx' w.asIdeal) :=
    (continuous_pow _).comp hvalK
  have hdense : DenseRange (algebraMap K (v.adicCompletion K)) :=
    denseRange_algebraMap (R := 𝓞 K) (K := K) (v := v)
  refine congrFun (DenseRange.equalizer hdense hcontL hcontR ?_) x
  funext k
  change Valued.v (adicCompletionMap v w (algebraMap K (v.adicCompletion K) k)) =
    Valued.v (algebraMap K (v.adicCompletion K) k) ^
      v.asIdeal.ramificationIdx' w.asIdeal
  rw [adicCompletionMap_algebraMap v w]
  simp only [algebraMap_adicCompletion, Function.comp_apply,
    valuedAdicCompletion_eq_valuation', Algebra.algebraMap_self_apply]
  rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]
  exact (valuation_liesOver L v w k).symm

/-- **The completion map preserves integrality.** Let $L/K$ be an extension of number fields, let
$v$ be a finite place of $K$, given as a height-one prime of the ring of integers $\mathcal{O}_K$,
and let $w$ be a finite place of $L$ lying over $v$. The continuous ring homomorphism
$K_v \to L_w$ between the completions that extends $K \to L$ maps every element of the ring of
integers of $K_v$ into the ring of integers of $L_w$. -/
theorem adicCompletionMap_mem_integers (x : v.adicCompletion K)
    (hx : x ∈ v.adicCompletionIntegers K) :
    adicCompletionMap v w x ∈ w.adicCompletionIntegers L := by
  have hpow : Valued.v x ^ v.asIdeal.ramificationIdx' w.asIdeal ≤ 1 := by
    have h := pow_mem hx (v.asIdeal.ramificationIdx' w.asIdeal)
    rw [mem_adicCompletionIntegers, map_pow] at h
    exact h
  rw [mem_adicCompletionIntegers, valuation_adicCompletionMap v w]
  exact hpow

/-- **Restriction of the completion map to the rings of integers.** Let $L/K$ be an extension of
number fields, let $v$ be a finite place of $K$, given as a height-one prime of the ring of
integers $\mathcal{O}_K$, and let $w$ be a finite place of $L$ lying over $v$. Let $K_v$ and $L_w$
be the completions, with rings of integers $\mathcal{O}_v$ and $\mathcal{O}_w$. The continuous
ring homomorphism $K_v \to L_w$ extending $K \to L$ restricts to a ring homomorphism
$\mathcal{O}_v \to \mathcal{O}_w$. -/
noncomputable def adicCompletionIntegersMap :
    v.adicCompletionIntegers K →+* w.adicCompletionIntegers L where
  toFun x := ⟨adicCompletionMap v w x.val, adicCompletionMap_mem_integers v w x.val x.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' := fun _x _y => Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' := fun _x _y => Subtype.ext (map_add _ _ _)

@[simp]
theorem adicCompletionIntegersMap_apply (x : v.adicCompletionIntegers K) :
    ((adicCompletionIntegersMap v w x : w.adicCompletionIntegers L) :
      w.adicCompletion L) = adicCompletionMap v w (x : v.adicCompletion K) :=
  rfl

end IsDedekindDomain.HeightOneSpectrum
