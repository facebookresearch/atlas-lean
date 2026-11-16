/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StackChowGroups

/-!
# Actual stack zero sections and first-Chern operators

The zero section is normalized by the literal zero element of the full
cartesian module presheaf, including every affine-point arrow. Its first
Chern cap is the actual zero-section push followed by the inverse of the
actual line-bundle projection pull. No free operator called c1 is supplied.

The underlying Chow carrier is Kresch's integral group. Rational extension
is the native tensor operation. Homotopy and native stack descent remain
construction requests; the ordinary scheme zero-section and line-bundle
Chow identities are completed source integration from AxiomMath/Stacks
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

/-- Zero on every actual affine module, with its literal restriction maps. -/
def zeroElements {X : Stack S} (E : VectorBundle X) :
    AffinePoint X ⥤ (sectionPresheaf E.module.val).Elementsᵒᵖ where
  obj a := op ((sectionPresheaf E.module.val).elementsMk (op a)
    (0 : E.module.val.presheaf.obj (op a)))
  map f := (Functor.Elements.homMk f.op (by
    change E.module.val.presheaf.presheaf.map f.op 0 = 0
    exact map_zero _)).op
  map_id a := by
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    rfl
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    rfl

/-- The global map represents the zero element on objects and all arrows. -/
structure ZeroSection {X : Stack S} (E : VectorBundle X) where
  map : StackHom X E.total
  overBase : StackVectorBundles.TwoIso
    (Pseudofunctor.StrongTrans.vcomp map E.projection)
    (Pseudofunctor.StrongTrans.id X.toPseudofunctor)
  normalized : affineMap map ⋙ E.comparison.functor ≅ zeroElements E

/-- Reindexing is the actual Cartesian bundle square and literal zero map. -/
structure ZeroSectionBaseChange {T X : Stack S} (p : StackHom T X)
    (E : VectorBundle X) (P : BundlePullback p E)
    (z : ZeroSection E) (z' : ZeroSection P.bundle) where
  comparison : StackVectorBundles.TwoIso
    (Pseudofunctor.StrongTrans.vcomp z'.map P.map)
    (Pseudofunctor.StrongTrans.vcomp p z.map)

/-- The native flat projection pull, regraded by the exact line rank. -/
def lineProjectionPull {D : CycleConstructionData S scope}
    {K : KreschPresentation D} {X : Stack S} {hX : scope X}
    (E : VectorBundle X) (hE : scope E.total)
    (P : FlatChowPullData D K hE hX E.projection 1) (d : ℤ) :
    ChowGroup D K X hX (d - 1) →+ ChowGroup D K E.total hE d :=
  (chowRegrade D K E.total hE (by omega)).comp (P.map (d - 1))

/-- Homotopy concerns the fixed genuine projection map, not an assigned
isomorphism of arbitrary group carriers. -/
structure LineHomotopy {D : CycleConstructionData S scope}
    {K : KreschPresentation D} {X : Stack S} {hX : scope X}
    (E : VectorBundle X) (hE : scope E.total)
    (P : FlatChowPullData D K hE hX E.projection 1) : Prop where
  bijective : ∀ d : ℤ, Function.Bijective (lineProjectionPull E hE P d)

/-- All ingredients are actual geometric maps on the same Kresch carrier. -/
structure FirstChernData (D : CycleConstructionData S scope)
    (K : KreschPresentation D) {X : Stack S} (hX : scope X)
    (E : VectorBundle X) where
  rank_one : E.rank = 1
  bundleScope : scope E.total
  zero : ZeroSection E
  pull : FlatChowPullData D K bundleScope hX E.projection 1
  push : ProjectiveChowPushData D K hX bundleScope zero.map
  homotopy : LineHomotopy E bundleScope pull

def zeroGysin {D : CycleConstructionData S scope} {K : KreschPresentation D}
    {X : Stack S} {hX : scope X} {E : VectorBundle X}
    (C : FirstChernData D K hX E) (d : ℤ) :
    ChowGroup D K E.total C.bundleScope d ≃+ ChowGroup D K X hX (d - 1) :=
  (AddEquiv.ofBijective (lineProjectionPull E C.bundleScope C.pull d)
    (C.homotopy.bijective d)).symm

/-- c1(L) cap is s! s*, with s! computed as inverse projection pull. -/
def firstChern {D : CycleConstructionData S scope} {K : KreschPresentation D}
    {X : Stack S} {hX : scope X} {E : VectorBundle X}
    (C : FirstChernData D K hX E) (d : ℤ) :
    ChowGroup D K X hX d →+ ChowGroup D K X hX (d - 1) :=
  (zeroGysin C d).toAddMonoidHom.comp (C.push.map d)

def rationalFirstChern {D : CycleConstructionData S scope} {K : KreschPresentation D}
    {X : Stack S} {hX : scope X} {E : VectorBundle X}
    (C : FirstChernData D K hX E) (d : ℤ) :
    RationalChowGroup D K X hX d →ₗ[ℚ] RationalChowGroup D K X hX (d - 1) :=
  rationalMap (firstChern C d)

theorem projectionPull_firstChern {D : CycleConstructionData S scope}
    {K : KreschPresentation D} {X : Stack S} {hX : scope X}
    {E : VectorBundle X} (C : FirstChernData D K hX E) (d : ℤ)
    (a : ChowGroup D K X hX d) :
    lineProjectionPull E C.bundleScope C.pull d (firstChern C d a) = C.push.map d a :=
  (AddEquiv.ofBijective (lineProjectionPull E C.bundleScope C.pull d)
    (C.homotopy.bijective d)).apply_symm_apply _

end AlgebraicGeometry.StackFirstChernOperators
