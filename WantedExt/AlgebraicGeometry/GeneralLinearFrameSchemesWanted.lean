/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.GeneralLinearFrameSchemes

/-!
# Native general linear frame group construction

Construct the group structure and frame-point equivalence of the literal
determinant-localized matrix Spec, normalized on every matrix-coordinate
section and every actual free-module pullback. This is ordinary frame
geometry support for Simpson's Proposition 4.1 and general bundle families;
no lambda representability or quotient theorem is an input or conclusion.
The source and native license/revision credits are retained in the core.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.GeneralLinearFrameSchemesWanted

open MathlibExt.AlgebraicGeometry.GeneralLinearFrameSchemes

def_wanted general_linear_frames (n : ℕ) : FrameTheory n

end WantedExt.AlgebraicGeometry.GeneralLinearFrameSchemesWanted
