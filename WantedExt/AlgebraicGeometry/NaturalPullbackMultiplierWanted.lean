/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NaturalPullbackMultiplierModules
public import Batteries.Util.ProofWanted

/-!
# Exact image of the actual limiting multiplier module

de Fernex--Hacon, arXiv0805.1767v2, Definition 4.3 and Theorem 1.1.
The model principalizes the *full* pulled fractional module O(-mK),
the actual ideal and actual exceptional boundary, with genuine SNC
support. The target is pinned on every affine section by the actual
pushforward/rational-field map. No Q-Gorenstein hypothesis is imposed.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NaturalPullbackMultiplierModules

open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs

def_wanted limitingMultiplierImage
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (V : NormalVariety k n) (C : CanonicalData V)
    [∀ p : PrimePoint V, IsDiscreteValuationRing (LocalRing V p.val)]
    (I : V.X.left.IdealSheafData) (m : ℕ+) (c : ℝ) (hc : 0 ≤ c)
    (R : ResolvedMultiplierModel V C I m) :
    CandidateImage V C R.model I m c R.naturalSupport R.idealSupport

end MathlibExt.AlgebraicGeometry.NaturalPullbackMultiplierModules
