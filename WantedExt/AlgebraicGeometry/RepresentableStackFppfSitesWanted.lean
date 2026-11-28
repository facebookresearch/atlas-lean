/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RepresentableStackFppfSites

/-!
# Native arbitrary-domain small-fppf site realization

The actual cartesian chart functors, invertible triangles, compatible
two-isomorphism quotient and native identity/composition components are
fixed by the target. Covers test the actual represented scheme fibres.
No Kummer-flat equivalence or root reconstruction conclusion is an input.
Source: Talpo--Vistoli arXiv:1410.1164v2, Section4.1 and Definition6.2.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RepresentableStackFppfSites

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.StackCycleGeometry
open MathlibExt.AlgebraicGeometry.RepresentableStackFppfSites

public def_wanted nativeSmallFppfSite (S : Scheme.{0}) (R : Stack S) :
  NativeSiteCategory R

end WantedExt.AlgebraicGeometry.RepresentableStackFppfSites
