/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeCanonicalBaseChangeModels
public import Batteries.Util.ProofWanted

/-!
# Native single-sheaf top-cohomology pullback comparison

This is the native adapter to the completed ordinary right-exact
pullback comparison. It asserts only the actual degree-d map is
invertible, allowing all lower Tor terms. It supplies no Kollár
compatibility or pluricanonical base-change conclusion.
Sources: Stacks Project, Tags 06YI and 0A9Y.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RelativeCanonicalBaseChangeModelsWanted

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.RelativeCanonicalBaseChangeModels

theorem_wanted nativeSingleHomologyPullback [HasDerivedPullbacks.{0}]
    (X Y : Scheme.{0}) (p : X ⟶ Y) (M : Y.Modules) (d : ℤ) :
    IsIso (singleHomologyCounit p M d)

end WantedExt.AlgebraicGeometry.RelativeCanonicalBaseChangeModelsWanted
