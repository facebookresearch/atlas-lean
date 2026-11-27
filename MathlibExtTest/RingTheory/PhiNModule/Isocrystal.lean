/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.PhiNModule.Isocrystal

/-! # Tests for isocrystals as `φ`-modules

The `(φ, N)`-module of an isocrystal has `N = 0`; the standard one-dimensional isocrystal of slope
`m` has Newton number `m` for the `p`-adic valuation of `K(p, k)`, for instance over `ZMod p`; and
over an algebraically closed field the Newton number of a one-dimensional isocrystal is the slope
of Mathlib's classification.
-/

open Module WittVector
open scoped Isocrystal

namespace MathlibExtTest.RingTheory.PhiNModule.Isocrystal

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p] [PerfectRing k p]

example (V : Type*) [AddCommGroup V] [WittVector.Isocrystal p k V] :
    (WittVector.Isocrystal.toPhiNModule p k V).N = 0 :=
  rfl

example (V : Type*) [AddCommGroup V] [WittVector.Isocrystal p k V] (x : V) :
    (WittVector.Isocrystal.toPhiNModule p k V).φ x = Φ(p, k) x :=
  rfl

example (m : ℤ) :
    (WittVector.Isocrystal.toPhiNModule p k (StandardOneDimIsocrystal p k m)).newtonNumber
      (FractionRing.addValuation p k) = m :=
  WittVector.Isocrystal.newtonNumber_standardOneDimIsocrystal p k m

/-- Over `𝔽_p = ZMod p`, the standard isocrystal of slope `-2` has Newton number `-2`. -/
example :
    (WittVector.Isocrystal.toPhiNModule p (ZMod p)
      (StandardOneDimIsocrystal p (ZMod p) (-2))).newtonNumber
        (FractionRing.addValuation p (ZMod p)) = -2 :=
  WittVector.Isocrystal.newtonNumber_standardOneDimIsocrystal p (ZMod p) (-2)

/-- Over an algebraically closed field, a one-dimensional isocrystal is isomorphic to the
standard one whose slope is its Newton number. -/
example (k : Type*) [Field k] [IsAlgClosed k] [CharP k p] (V : Type*) [AddCommGroup V]
    [WittVector.Isocrystal p k V] (h : finrank K(p, k) V = 1) :
    ∃ m : ℤ, ∃ _ : FiniteDimensional K(p, k) V,
      (WittVector.Isocrystal.toPhiNModule p k V).newtonNumber
        (FractionRing.addValuation p k) = m ∧
      Nonempty (StandardOneDimIsocrystal p k m ≃ᶠⁱ[p, k] V) :=
  WittVector.Isocrystal.exists_newtonNumber_eq p k V h

end MathlibExtTest.RingTheory.PhiNModule.Isocrystal
