/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_WeierstrassCurve_MapPoint.lean`,
`Definitions/Def_WeierstrassCurve_PointAddEquivOfEq.lean`
and
`Definitions/Def_WeierstrassCurve_VariableChangePointEquiv.lean`
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

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import MathlibExt.AlgebraicGeometry.EllipticCurve.VariableChangePoint

/-!
# Transport of affine Weierstrass points

This file transports nonsingular affine points of a Weierstrass curve
along three kinds of identification: a ring homomorphism between
fields (`mapPoint`, a group homomorphism), an equality of curves
(`pointAddEquivOfEq`, an additive equivalence), and an admissible
variable change whose transformed curve equals a given curve
(`Point.equivOfVariableChangeEq`, an equivalence with an explicit
coordinate formula).

`mapPoint` is Mathlib's `Affine.Point.map` for the `F`-algebra structure
that `f` puts on `k`, applied to `W₀.toAffine.Point`, which is the
self-base-change `(W₀.toAffine⁄F).Point` by definition. It takes the ring
homomorphism itself, so it also applies to an endomorphism `F →+* F`, where
installing `f.toAlgebra` next to `Algebra.id F` does not elaborate. Zero,
addition, negation, scalar multiples and additive order go through Mathlib's
generic lemmas: `map_zero`, `map_add`, `map_neg`, `map_nsmul`, `map_zsmul`, and
`addOrderOf_injective` with `mapPoint_injective`.
`Point.equivOfVariableChangeEq` transports
`Affine.Point.variableChangeAddEquiv` along the equality of curves.
-/

@[expose] public section

namespace WeierstrassCurve

universe u v w

variable {F : Type u} {k : Type v} [Field F] [Field k] [DecidableEq F] [DecidableEq k]
  (f : F →+* k) {W₀ : WeierstrassCurve F}

/-- **Affine points under a ring homomorphism.** For a Weierstrass curve $W$ over a field $F$
and a ring homomorphism $f \colon F \to k$ into a field $k$, the homomorphism from the group of
nonsingular points of $W$ to the group of nonsingular points of the curve obtained by applying $f$
to the coefficients of $W$; it sends the point at infinity to the point at infinity and an affine
point $(x, y)$ to $(f(x), f(y))$. -/
noncomputable def mapPoint : W₀.toAffine.Point →+ (W₀.map f).toAffine.Point :=
  letI := f.toAlgebra
  Affine.Point.map (W' := W₀.toAffine) (Algebra.ofId F k)

lemma mapPoint_some {x y : F} (h : W₀.toAffine.Nonsingular x y) :
    mapPoint f (.some x y h) =
      .some (f x) (f y) ((W₀.toAffine.map_nonsingular f.injective x y).mpr h) :=
  rfl

lemma mapPoint_injective : Function.Injective (mapPoint f (W₀ := W₀)) :=
  letI := f.toAlgebra
  Affine.Point.map_injective (W' := W₀.toAffine) (Algebra.ofId F k)

/-- **Points of equal Weierstrass curves.** For Weierstrass curves $W_1 = W_2$ over a field $L$,
the additive equivalence between their groups of nonsingular points induced by the equality; it
sends each point to the point with the same coordinates. -/
def pointAddEquivOfEq {L : Type w} [Field L] [DecidableEq L]
    {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) :
    W₁.toAffine.Point ≃+ W₂.toAffine.Point :=
  e ▸ AddEquiv.refl _

@[simp]
theorem pointAddEquivOfEq_refl {L : Type w} [Field L] [DecidableEq L]
    (W : WeierstrassCurve L) :
    pointAddEquivOfEq (rfl : W = W) = AddEquiv.refl _ :=
  rfl

theorem pointAddEquivOfEq_symm {L : Type w} [Field L] [DecidableEq L]
    {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) :
    (pointAddEquivOfEq e).symm = pointAddEquivOfEq e.symm := by
  subst e; rfl

theorem pointAddEquivOfEq_some {L : Type w} [Field L] [DecidableEq L]
    {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) {x y : L}
    (h : W₁.toAffine.Nonsingular x y) :
    pointAddEquivOfEq e (.some x y h) = .some x y (e ▸ h) := by
  subst e; rfl

end WeierstrassCurve

namespace WeierstrassCurve.Affine.Point

universe u

variable {K : Type u} [Field K] {C : VariableChange K} {W : WeierstrassCurve K}

open VariableChange

/-- **Points under a variable change onto a given curve.** Let $W$ and $V$ be Weierstrass curves
over a field $K$ and let $C = (u, r, s, t)$ be a variable change with $C \cdot W = V$. The
bijection from the nonsingular points of $V$ to those of $W$ that sends the point at infinity to
the point at infinity and an affine point $(x, y)$ to $(u^2 x + r,\ u^3 y + u^2 s x + t)$. -/
noncomputable def equivOfVariableChangeEq {V : WeierstrassCurve K}
    (h : C • W = V) : V.toAffine.Point ≃ W.toAffine.Point := by
  subst h
  exact open scoped Classical in (variableChangeAddEquiv C W).toEquiv

@[simp]
lemma equivOfVariableChangeEq_zero {V : WeierstrassCurve K} (h : C • W = V) :
    equivOfVariableChangeEq h 0 = 0 := by
  subst h
  classical
  exact _root_.map_zero (variableChangeAddEquiv C W)

@[simp]
lemma equivOfVariableChangeEq_some {V : WeierstrassCurve K} (h : C • W = V) {x y : K}
    (hxy : V.toAffine.Nonsingular x y) :
    equivOfVariableChangeEq h (.some x y hxy) =
      .some (mapAffineCoordinates C (x, y)).1 (mapAffineCoordinates C (x, y)).2
        ((nonsingular_mapAffineCoordinates_iff C W (x, y)).mp (h ▸ hxy)) := by
  subst h
  classical
  exact variableChangeAddEquiv_some hxy

end WeierstrassCurve.Affine.Point
