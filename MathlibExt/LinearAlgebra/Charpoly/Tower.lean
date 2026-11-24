/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.LinearAlgebra.Charpoly.DependentPi

/-!
# Characteristic polynomials of left multiplication in a tower

For a tower of finite extensions of fields `k ⊆ F ⊆ E` and an element
`θ₀ : F` of the intermediate field, left multiplication on `E` by the
image of `θ₀` has characteristic polynomial over `k` equal to the
`Module.finrank F E`-th power of the characteristic polynomial of left
multiplication by `θ₀` on `F`:

```text
(Algebra.lmul k E (algebraMap F E θ₀)).charpoly
  = (Algebra.lmul k F θ₀).charpoly ^ Module.finrank F E.
```

This is leaf `B8` of the weighted branch multiplicity proof tree: for a
normalization branch, `F` is the residue field of the reduced place,
`θ₀` is the class of `X` (a primitive element of `F` over `k`, whose
characteristic polynomial on `F` over `k` is its minimal polynomial over
`k`), and `E` is the full
branch residue field, so the characteristic polynomial of the reduced
root is a power of its minimal polynomial with exponent the relative
residue degree.

## Informal proof

Choose an `F`-basis of `E` indexed by `Fin (Module.finrank F E)`
(`Module.finBasis`).  The coordinate equivalence `Module.Basis.equivFun`
identifies `E` with `Fin (finrank F E) → F` as `F`-modules, hence also
as `k`-modules after restricting scalars.  Multiplication by
`algebraMap F E θ₀` is the scalar action of `θ₀` on `E` as an
`F`-module, so in coordinates it acts componentwise as multiplication
by `θ₀` on `F` — the matrix is block-diagonal with `finrank F E`
identical blocks.  Conjugation invariance of the characteristic
polynomial and the dependent-product formula
`LinearMap.charpoly_pi_dependent` then give a product of
`finrank F E` copies of `(Algebra.lmul k F θ₀).charpoly`.

Only the bottom two entries of the tower need to be fields: `E` may be
any ring with compatible algebra structures.  The finiteness of `E`
over `k` is listed separately because the statement's characteristic
polynomial needs it; it follows from the other two finiteness
assumptions.
-/

@[expose] public section

set_option autoImplicit false

open Polynomial

namespace Algebra

section Tower

variable {k F E : Type*} [Field k] [Field F] [Ring E]
  [Algebra k F] [Algebra F E] [Algebra k E] [IsScalarTower k F E]
  [FiniteDimensional k F] [FiniteDimensional F E] [FiniteDimensional k E]

/-- Characteristic polynomial of left multiplication by an
intermediate-field element in a finite tower: if `θ₀` lies in the
intermediate field `F`, the characteristic polynomial of left
multiplication by its image in `E` is the `Module.finrank F E`-th power
of the characteristic polynomial of left multiplication by `θ₀` on
`F`. -/
theorem lmul_charpoly_algebraMap_tower (θ₀ : F) :
    (Algebra.lmul k E (algebraMap F E θ₀)).charpoly =
      (Algebra.lmul k F θ₀).charpoly ^ Module.finrank F E := by
  classical
  let n := Module.finrank F E
  let b : Module.Basis (Fin n) F E := Module.finBasis F E
  let e : E ≃ₗ[k] (Fin n → F) := b.equivFun.restrictScalars k
  have he : ∀ x i, e x i = b.repr x i := fun x i =>
    congrFun (Module.Basis.equivFun_apply b x) i
  have hconj : e.conj (Algebra.lmul k E (algebraMap F E θ₀)) =
      LinearMap.pi
        (fun i => (Algebra.lmul k F θ₀).comp (LinearMap.proj i)) := by
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    funext i
    simp only [LinearEquiv.conj_apply_apply,
      LinearEquiv.symm_apply_apply, LinearMap.pi_apply,
      LinearMap.comp_apply, LinearMap.proj_apply, he]
    have hmul : (Algebra.lmul k E (algebraMap F E θ₀)) x = θ₀ • x := by
      simp only [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply',
        Algebra.smul_def]
    rw [hmul, map_smul, Finsupp.smul_apply, smul_eq_mul]
    simp only [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
  calc
    (Algebra.lmul k E (algebraMap F E θ₀)).charpoly =
        (e.conj (Algebra.lmul k E (algebraMap F E θ₀))).charpoly :=
      (LinearEquiv.charpoly_conj e _).symm
    _ = ∏ _i : Fin n, (Algebra.lmul k F θ₀).charpoly := by
      rw [hconj, LinearMap.charpoly_pi_dependent]
    _ = (Algebra.lmul k F θ₀).charpoly ^ n := by simp
    _ = (Algebra.lmul k F θ₀).charpoly ^ Module.finrank F E := rfl

end Tower

end Algebra
