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

public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteTorusKernelLanding
public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteWeylKernelFactorization

/-! # Finite central-kernel containment in the torus-cocycle subgroup

For `[Field F]` and arbitrary `n : ℕ` with no rank bound,
`finiteCentralKernelSubgroup (R := F) n ≤ torusCocycleSubgroup (F := F)`.

The proof factors `g` head-left by the accepted
`finiteCentralKernel_mem_torusCocycle_mul_finiteTorus` as `g = c * t`, with `c`
in the torus-cocycle subgroup and `t` in `finiteTorusSubgroup n`. It pushes `g`
into `ker toStableE` by `finiteCentralKernelSubgroup_le_ker` and `c` by
`torusCocycleSubgroup_le_ker_toStableE`, then cancels with `map_mul`, the
head-left equality, and `one_mul` to get `t ∈ ker toStableE` without any
inverse or commutativity argument. Finally it lands `t` by the accepted
`ker_toStableE_inf_finiteTorus_le_torusCocycleSubgroup`, rewrites by
`g = c * t`, and closes under subgroup multiplication. Uniform for `n = 0`,
`n = 1`, and larger ranks.

Nonclaims: this is not finite-stage reduction, full kernel equality, a TWT
theorem, an inverse, naturality, or Matsumoto's theorem.
-/

@[expose] public section

namespace AlgebraicKTheory

namespace StableSteinberg

universe u

/-- Finite central-kernel elements lie in the torus-cocycle subgroup.

For `[Field F]` and arbitrary `n : ℕ` with no rank bound, every
`g ∈ finiteCentralKernelSubgroup (R := F) n` lies in
`torusCocycleSubgroup (F := F)`, via head-left cocycle–finite-torus
factorization followed by finite-torus kernel landing.

Nonclaims: containment only; no finite-stage reduction, full kernel equality,
TWT theorem, inverse, naturality, or Matsumoto claim. -/
public theorem finiteCentralKernelSubgroup_le_torusCocycleSubgroup
    {F : Type u} [Field F] {n : ℕ} :
    finiteCentralKernelSubgroup (R := F) n ≤ torusCocycleSubgroup (F := F) := by
  intro g hg
  obtain ⟨c, t, hc, ht, hg_eq⟩ :=
    finiteCentralKernel_mem_torusCocycle_mul_finiteTorus (F := F) n g hg
  have hg_one : toStableE (R := F) g = 1 :=
    MonoidHom.mem_ker.mp (finiteCentralKernelSubgroup_le_ker (R := F) n hg)
  have hc_one : toStableE (R := F) c = 1 :=
    MonoidHom.mem_ker.mp (torusCocycleSubgroup_le_ker_toStableE (F := F) hc)
  have ht_one : toStableE (R := F) t = 1 := by
    have hmap : toStableE (R := F) c * toStableE (R := F) t = 1 := by
      rw [← map_mul, ← hg_eq]
      exact hg_one
    rw [hc_one, one_mul] at hmap
    exact hmap
  have ht_mem : t ∈ MonoidHom.ker (toStableE (R := F)) ⊓
      finiteTorusSubgroup (R := F) n :=
    Subgroup.mem_inf.mpr ⟨MonoidHom.mem_ker.mpr ht_one, ht⟩
  have ht_coc : t ∈ torusCocycleSubgroup (F := F) :=
    ker_toStableE_inf_finiteTorus_le_torusCocycleSubgroup ht_mem
  rw [hg_eq]
  exact (torusCocycleSubgroup (F := F)).mul_mem hc ht_coc

end StableSteinberg

end AlgebraicKTheory

end
