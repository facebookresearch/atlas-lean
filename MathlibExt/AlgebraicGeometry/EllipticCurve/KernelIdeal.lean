/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_WeierstrassCurve_KernelIdeal.lean`
`Definitions/Def_WeierstrassCurve_RationalEnd.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.RationalEnd

@[expose] public section

/-!
# Kernel ideal data for rationally represented point maps

For an additive map `χ` from the `k`-points of a Weierstrass curve `W₀` to those of `W`, this file
defines `kernelIdealSet k W₀ W χ`: the elements of the subring `rationalEndSubring k W₀` of
additive endomorphisms that factor through `χ` as `ρ.comp χ` with `ρ` zero or rationally
represented. It is a subset, not an ideal.
-/

namespace WeierstrassCurve

universe u v

variable {F : Type u} [Field F] (k : Type v) [Field k] [Algebra F k] [DecidableEq k]
  [IsAlgClosed k]

/-- The set of elements of `rationalEndSubring k W₀` that factor as `ρ.comp χ` with
`ρ ∈ rationalHomSet k W W₀`. It is a subset of `rationalEndSubring k W₀`, not an ideal: closure
under addition and under multiplication by `rationalEndSubring k W₀` is not part of the
definition. -/
def kernelIdealSet (W₀ W : WeierstrassCurve F)
    (χ : (W₀.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point) :
    Set (rationalEndSubring k W₀) :=
  {a | ∃ ρ ∈ rationalHomSet k W W₀,
    (a : AddMonoid.End (W₀.baseChange k).toAffine.Point) = ρ.comp χ}

theorem zero_mem_kernelIdealSet (W₀ W : WeierstrassCurve F)
    (χ : (W₀.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point) :
    (0 : rationalEndSubring k W₀) ∈ kernelIdealSet k W₀ W χ :=
  ⟨0, zero_mem_rationalHomSet k W W₀, by rw [AddMonoidHom.zero_comp]; rfl⟩

theorem one_mem_kernelIdealSet_id (W : WeierstrassCurve F) :
    (1 : rationalEndSubring k W) ∈ kernelIdealSet k W W (AddMonoidHom.id _) :=
  ⟨AddMonoidHom.id _, id_mem_rationalHomSet k W, rfl⟩

end WeierstrassCurve
