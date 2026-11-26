/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.FormalGroup

@[expose] public section

open MvPowerSeries

-- The bundled formal group carries `formalGroupLaw`, over any commutative ring.
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    W.formalGroup.toPowerSeries = W.formalGroupLaw :=
  W.formalGroup_toPowerSeries

-- Higher-universe consumer: the law is commutative.
example {R : Type 1} [CommRing R] (W : WeierstrassCurve R) : W.formalGroup.IsComm :=
  inferInstance

-- Mathlib's formal group API consumes it: `F(f, 0) = f` and `F(0, f) = f`.
example {R σ : Type*} [CommRing R] (W : WeierstrassCurve R) {f : MvPowerSeries σ R}
    (hf : PowerSeries.HasSubst f) :
    W.formalGroupLaw.subst ![f, 0] = f ∧ W.formalGroupLaw.subst ![0, f] = f :=
  ⟨W.formalGroup.add_zero hf, W.formalGroup.zero_add hf⟩

-- Points of the formal group form a commutative monoid.
example {R σ : Type*} [CommRing R] (W : WeierstrassCurve R) (x y z : W.formalGroup.Point σ) :
    x + y + z = z + (y + x) := by
  rw [add_comm x y, add_comm (y + x) z]

-- Associativity at substituted series, from the bundled law.
example {R σ : Type*} [CommRing R] (W : WeierstrassCurve R) {f g h : MvPowerSeries σ R}
    (hf : PowerSeries.HasSubst f) (hg : PowerSeries.HasSubst g) (hh : PowerSeries.HasSubst h) :
    W.formalGroupLaw.subst ![W.formalGroupLaw.subst ![f, g], h] =
      W.formalGroupLaw.subst ![f, W.formalGroupLaw.subst ![g, h]] :=
  W.formalGroup.assoc' hf hg hh

-- The curve `y² + xy = x³` over `ℤ`: the law has no `X²` term and `F(X, 0) = X`.
example : MvPowerSeries.coeff (Finsupp.single 0 2)
    (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve ℤ).formalGroupLaw = 0 :=
  WeierstrassCurve.coeff_sq_formalGroupLaw _ 0

example : (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve ℤ).formalGroup.Xzero = PowerSeries.X :=
  FormalGroup.Xzero_eq_X _

-- Base change commutes with the construction.
example {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (f : R →+* S) :
    (W.map f).formalGroup = W.formalGroup.map f ∧
      (W.map f).formalW = PowerSeries.map f W.formalW :=
  ⟨W.map_formalGroup f, W.map_formalW f⟩
