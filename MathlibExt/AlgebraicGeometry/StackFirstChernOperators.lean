/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StackBundleCones

/-!
# Stack first-Chern operators of line bundles

The zero section and the rank-one first Chern operator are those of
`StackBundleCones`: the zero section is normalized by the literal zero element
of the full cartesian module presheaf, including every affine-point arrow, and
the cap is the actual zero-section push followed by the inverse of the
normalized bundle projection pull, regraded by the exact rank. `FirstChernData`
packages these ingredients for a line bundle; no free operator called c1 is
supplied.

The underlying Chow carrier is Kresch's integral group. Rational extension is
the native tensor operation. Homotopy and native stack descent remain
construction requests; the ordinary scheme zero-section and line-bundle Chow
identities are completed source integration from AxiomMath/Stacks
c496df0d9beea9deaeabcea8492605f9a0a2313b, Apache 2.0,
Chow/AffineBundle/{ZeroSectionPushforward,LineBundleChowBijective}.lean.
References: Kresch, arXiv:math/9810166v1, Theorem 2.1.12;
Fulton, Intersection Theory, Sections 2.1 and 3.3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace AlgebraicGeometry.StackFirstChernOperators

open CategoryTheory CategoryTheory.Limits Opposite
open StackCycleGeometry StackCycleRelations StackAffineModules StackVectorBundles StackChowGroups

variable {S : Scheme.{0}} {scope : Stack S → Prop}

/-- The ingredients of the first Chern cap of a line bundle: its zero section,
the flat projection pull, the proper zero-section push, and the homotopy
identification normalized by that projection pull. -/
structure FirstChernData (D : CycleConstructionData S scope)
    (K : KreschPresentation D) {X : Stack S} (hX : scope X)
    (E : VectorBundle X) where
  rank_one : E.rank = 1
  bundleScope : scope E.total
  zero : StackBundleCones.ZeroSection E
  pull : FlatChowPullData D K bundleScope hX E.projection E.rank
  push : ProjectiveChowPushData D K hX bundleScope zero.map
  homotopy : StackBundleCones.BundleHomotopyData D K hX E bundleScope pull

/-- The cap `c₁(L) ∩ - = s^* s_*`, with `s^*` the inverse of the projection pull:
`StackBundleCones.firstChernOperator`. -/
def firstChern {D : CycleConstructionData S scope} {K : KreschPresentation D}
    {X : Stack S} {hX : scope X} {E : VectorBundle X}
    (C : FirstChernData D K hX E) (d : ℤ) :
    ChowGroup D K X hX d →+ ChowGroup D K X hX (d - 1) :=
  StackBundleCones.firstChernOperator C.homotopy C.zero C.push C.rank_one d

def rationalFirstChern {D : CycleConstructionData S scope} {K : KreschPresentation D}
    {X : Stack S} {hX : scope X} {E : VectorBundle X}
    (C : FirstChernData D K hX E) (d : ℤ) :
    RationalChowGroup D K X hX d →ₗ[ℚ] RationalChowGroup D K X hX (d - 1) :=
  rationalMap (firstChern C d)

/-- The projection pull of the Euler class cap is the zero-section push. -/
theorem isomorphism_eulerOperator {D : CycleConstructionData S scope}
    {K : KreschPresentation D} {X : Stack S} {hX : scope X}
    {E : VectorBundle X} (C : FirstChernData D K hX E) (d : ℤ)
    (a : ChowGroup D K X hX d) :
    C.homotopy.isomorphism d (StackBundleCones.eulerOperator C.homotopy C.zero C.push d a) =
      C.push.map d a :=
  (C.homotopy.isomorphism d).apply_symm_apply _

end AlgebraicGeometry.StackFirstChernOperators
