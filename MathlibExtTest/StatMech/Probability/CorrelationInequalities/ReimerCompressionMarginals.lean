/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.ReimerCompressionMarginals

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.ReimerCompressionMarginals`

* `iterDoubleCompress` on the empty list is the identity and preserves cardinality.
* `fmarg_le_upCompression` and `fmarg_le_doubleCompress` with the constant weight `1` (counting
  measure), which satisfies the dominance hypotheses.
* `fmarg_doubleCompress_symm_eq` and `wdpairs_le_iterDoubleCompress_of_symm` with the constant
  weight `1/2` on `Fin 2`.
-/

@[expose] public section

open StatMech Finset

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerCompressionMarginals

example (𝒰 : Finset (Finset (Fin 2 ⊕ Fin 2))) : iterDoubleCompress [] 𝒰 = 𝒰 := rfl

example (𝒰 : Finset (Finset (Fin 2 ⊕ Fin 2))) :
    (iterDoubleCompress [0, 1] 𝒰).card = 𝒰.card :=
  iterDoubleCompress_card _ _

example (𝒜 : Finset (Finset (Fin 2))) :
    fmarg (fun _ _ => (1 : ℝ)) 𝒜 ≤
      fmarg (fun _ _ => (1 : ℝ)) (UV.compression ({0} : Finset (Fin 2)) ∅ 𝒜) :=
  fmarg_le_upCompression (fun _ _ => zero_le_one) 0 le_rfl 𝒜

example (𝒰 : Finset (Finset (Fin 2 ⊕ Fin 2))) :
    fmarg (fun _ _ => (1 / 2 : ℝ)) (doubleCompress 0 𝒰) = fmarg (fun _ _ => (1 / 2 : ℝ)) 𝒰 :=
  fmarg_doubleCompress_symm_eq (fun _ => rfl) 0 𝒰

example (𝒜 ℬ : Finset (Finset (Fin 2))) :
    wdpairs (fun _ _ => (1 / 2 : ℝ)) 𝒜 ℬ ≤
      fmarg (doubleWeight (fun _ _ => (1 / 2 : ℝ))) (iterDoubleCompress [0, 1] (boxDoubled 𝒜 ℬ)) :=
  wdpairs_le_iterDoubleCompress_of_symm (fun _ _ => by norm_num) (fun _ => rfl) _ 𝒜 ℬ

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerCompressionMarginals
