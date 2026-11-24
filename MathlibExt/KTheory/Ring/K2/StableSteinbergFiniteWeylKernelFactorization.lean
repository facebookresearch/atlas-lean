/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteWeylKernelPairedWord
public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteWeylHurwitzNormalForm

/-! # Finite central-kernel cocycle–finite-torus factorization

For `n : ℕ` and `[Field F]`, every
`g ∈ StableSteinberg.finiteCentralKernelSubgroup (R := F) n` factors head-left as
`g = c * t`, with `c` in `StableSteinberg.torusCocycleSubgroup` and `t` in
`StableSteinberg.finiteTorusSubgroup (R := F) n`.

The proof composes only the accepted paired-word bridge
`finiteCentralKernel_exists_paired_word` with the accepted normal form
`weightedWeylProd_mem_torusCocycle_mul_finiteTorus`, preserving their equality
orientations by transitivity: `g = weightedWeylProd wc` then
`weightedWeylProd wc = c * t`. Orientation is head-left throughout, matching
`weightedWeylProd`. The empty word gives `1 = 1 * 1`, uniform in ranks
`n = 0, 1` with no nonempty hypothesis.

Nonclaims: this is only the factorization; no finite-torus-kernel landing,
cocycle containment, finite-stage reduction, TWT, inverse, naturality, or
Matsumoto claim.
-/

@[expose] public section

namespace AlgebraicKTheory

universe u

/-- Finite central-kernel elements factor as cocycle times finite torus.

Purpose: compose the paired-word bridge with the weighted normal form so that
`g ∈ StableSteinberg.finiteCentralKernelSubgroup (R := F) n` over `[Field F]`
yields `c` in the torus cocycle subgroup and `t` in the rank-`n` finite torus
subgroup with `g = c * t`. Orientation is head-left throughout, matching
`weightedWeylProd`; the factors are existential. The empty word gives
`1 = 1 * 1`, uniform in ranks `n = 0, 1`.

Nonclaims: factorization only; no finite-torus-kernel landing, cocycle
containment, finite-stage reduction, TWT, inverse, naturality, or Matsumoto
claim. -/
public theorem finiteCentralKernel_mem_torusCocycle_mul_finiteTorus
    {F : Type u} [Field F] (n : ℕ) (g : StableSteinberg F)
    (hg : g ∈ StableSteinberg.finiteCentralKernelSubgroup (R := F) n) :
    ∃ c t : StableSteinberg F,
      c ∈ StableSteinberg.torusCocycleSubgroup (F := F) ∧
      t ∈ StableSteinberg.finiteTorusSubgroup (R := F) n ∧ g = c * t := by
  obtain ⟨wc, hwc, hprod⟩ := finiteCentralKernel_exists_paired_word (F := F) n g hg
  obtain ⟨c, t, hc, ht, hnt⟩ :=
    weightedWeylProd_mem_torusCocycle_mul_finiteTorus wc hprod
  exact ⟨c, t, hc, ht, hwc.trans hnt⟩

end AlgebraicKTheory

end
