/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_FLTPrelim_Ramification.lean`,
`Definitions/Def_GaloisRep_Residual.lean`,
`Theorems/Thm_WeierstrassCurve_residualGaloisRepOf_isUnramifiedAt_iff.lean`
and
`P2M/Sol/S_WeierstrassCurve_residualGaloisRepOf_isUnramifiedAt_iff.lean`
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

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Algebra.Field.ZMod
public import MathlibExt.AlgebraicGeometry.EllipticCurve.PointGaloisAction
public import MathlibExt.AlgebraicGeometry.EllipticCurve.ResidualModularity
public import MathlibExt.FieldTheory.Galois.ResidualGaloisRep
public import MathlibExt.RingTheory.Valuation.InertiaRootsOfUnity
public import MathlibExt.RingTheory.Valuation.LiesOverPrime

/-!
# Unramified residual representations of Weierstrass curves

Let `W` be a rational Weierstrass curve and `p` a prime. Assume that the `p`-torsion of `W`
over `AlgebraicClosure ℚ` has `p ^ 2` points and that the Galois action on it is trivial on
the automorphisms fixing some finite extension of `ℚ`; these two hypotheses construct the
residual representation `WeierstrassCurve.residualGaloisRepOf` of `W` at `p`. That
representation is unramified at `q` exactly when inertia at every valuation subring lying
over `q` fixes every `p`-torsion point.

The Galois action on points, the residual representation and the valuation predicates are
the existing ones from `PointGaloisAction`, `ResidualModularity`, `ResidualGaloisRep`,
`InertiaRootsOfUnity` and `LiesOverPrime`; this file adds only the torsion-point predicate
and the equivalence.
-/

-- The point API needs decidable equality on `AlgebraicClosure ℚ`. Take it from classical
-- logic for this file only, so that importers do not inherit a global instance.
attribute [local instance] Classical.decEq

@[expose] public section

open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine.Point

variable {R : Type*} {S : Type*} {K : Type*} [CommRing R] [Field S]
  [Field K] [DecidableEq K] [Algebra R S] [Algebra R K]
  [Algebra S K] [IsScalarTower R S K]

/-- **Unramified Galois action on torsion points.** The Galois action on the `n`-torsion points
of `W'` over `K` is unramified at `q` when, at every valuation subring of `K` lying over `q`,
every element of its inertia subgroup in `K ≃ₐ[S] K` fixes every `n`-torsion point. -/
def GaloisRepUnramifiedAt (W' : Affine R) (n : ℕ) (q : ℕ) : Prop :=
  ∀ A : ValuationSubring K, A.LiesOverPrime q →
    ∀ σ ∈ A.inertiaSubgroupIn S,
    ∀ x : Submodule.torsionBy ℤ (W'⁄K).Point n, σ • x = x

end WeierstrassCurve.Affine.Point

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point in
/-- **The residual representation is unramified exactly when inertia fixes torsion points.**
Let `W` be a Weierstrass curve over `ℚ` and `p` a prime. Assume that the `p`-torsion of `W` over
`AlgebraicClosure ℚ` has `p ^ 2` points and that the Galois action on it is trivial on the
automorphisms fixing some finite extension of `ℚ`; these two hypotheses construct the residual
representation of `W` at `p`, whose space is that `p`-torsion. Then this representation is
unramified at `q`, that is, every inertia element at every valuation subring of
`AlgebraicClosure ℚ` lying over `q` acts on it as the identity, exactly when every such inertia
element fixes every `p`-torsion point of `W`. -/
theorem WeierstrassCurve.residualGaloisRepOf_isUnramifiedAt_iff
    (W : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime]
    (hcard : Nat.card
      (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
        (S := ℚ) (K := AlgebraicClosure ℚ) W p))
    (q : ℕ) :
    (W.residualGaloisRepOf p hcard hker).IsUnramifiedAt q ↔
      WeierstrassCurve.Affine.Point.GaloisRepUnramifiedAt
        (S := ℚ) (K := AlgebraicClosure ℚ) W p q := by
  refine forall_congr' fun A => forall_congr' fun _ =>
    forall_congr' fun σ => forall_congr' fun _ => ?_
  constructor
  · intro h x
    have hx : σ • x = x := LinearMap.congr_fun h x
    exact hx
  · intro h
    exact LinearMap.ext fun x => h x
