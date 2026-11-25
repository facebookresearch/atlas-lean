/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NaturalPullbackMultiplierModules

/-!
# The actual global limiting multiplier ideal

Every positive-degree candidate is the fixed pushforward image from its
actual principalized fractional canonical module. The global limiting
ideal is their native ideal-sheaf supremum, whose affine components are
the already computed local supremum. Directedness, independence and a
maximal member are separate theorem requests.

Reference: de Fernex--Hacon, arXiv:0805.1767v2, Definition 4.3.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LimitingMultiplierFamilies

open CategoryTheory _root_.AlgebraicGeometry
open LogPairs NaturalPullbackMultiplierModules

variable {k : Type} [Field k] {n : ℕ} {V : NormalVariety k n} {C : CanonicalData V}
  [∀ p : PrimePoint V, IsDiscreteValuationRing (LocalRing V p.val)]
  {I : V.X.left.IdealSheafData} {c : ℝ}

/-- The native supremum of the full global candidate ideal sheaves. -/
def limitingIdeal (F : LimitingFamily V C I c) : V.X.left.IdealSheafData :=
  ⨆ m : PNat, (F.image m).ideal

theorem limitingIdeal_affine (F : LimitingFamily V C I c) (U : V.X.left.affineOpens) :
    (limitingIdeal F).ideal U = localLimitingIdeal V C F U := by
  simp only [limitingIdeal, localLimitingIdeal, Scheme.IdealSheafData.ideal_iSup, iSup_apply]

end MathlibExt.AlgebraicGeometry.LimitingMultiplierFamilies
