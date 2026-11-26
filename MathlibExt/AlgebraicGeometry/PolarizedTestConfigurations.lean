/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GenericSectionMaps
public import MathlibExt.AlgebraicGeometry.LinearizedLineBundles
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import MathlibExt.AlgebraicGeometry.RelativeProjectivity
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import MathlibExt.AlgebraicGeometry.ProjectiveLineSystems

/-!
# Actual polarized test-configuration geometry

The base is Spec k[t] and the torus is Spec k[t,t^-1] with its native Hopf
group structure. Actions, linearizations, generic trivializations, fibres,
flatness and projectivity refer to literal scheme maps. A test configuration
is not encoded by its weight sequence or an arbitrary degeneration score. Its
linearized polarization is ample on the total space, which over the affine base
`𝔸¹` is relative ampleness: these are BHJ's ample test configurations.

Source: Boucksom--Hisamoto--Jonsson, arXiv1504.06568v3, Definition 2.1.
Mathlib's completed Laurent Hopf algebra and affine group-scheme producer,
and Axiom's completed equivariant-module cocycles (ported in
LinearizedLineBundles), are reused.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PolarizedTestConfigurations

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.LinearizedLineBundles
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts

variable (k : Type) [Field k]

abbrev Base := Spec (CommRingCat.of k)
abbrev AffineLine : Over (Base k) := (Spec (.of (Polynomial k))).asOver (Base k)
abbrev Torus : Over (Base k) := (Spec (.of (LaurentPolynomial k))).asOver (Base k)

/-- The native group structure is computed from the actual Laurent Hopf algebra. -/
instance torusGroup : GrpObj (Torus k) := inferInstance

/-- The actual inclusion Spec k[t,t^-1] → Spec k[t]. -/
def torusInclusion : Torus k ⟶ AffineLine k :=
  (algSpec (CommRingCat.of k)).map
    (CommAlgCat.ofHom (Polynomial.toLaurentAlg : Polynomial k →ₐ[k]
      LaurentPolynomial k)).op

/-- The scalar point of the actual affine line. -/
def affinePoint (a : k) : Over.mk (𝟙 (Base k)) ⟶ AffineLine k :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Polynomial.aeval a).toRingHom)) (by
    change Spec.map (CommRingCat.ofHom (Polynomial.aeval a).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = 𝟙 (Base k)
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h : (Polynomial.aeval a).toRingHom.comp (algebraMap k (Polynomial k)) =
        RingHom.id k := by
      ext z
      exact (Polynomial.aeval a).commutes z
    rw [h]
    exact Spec.map_id _)

/-- A test configuration for `(X, L)`: a flat, proper, H-projective `𝔾ₘ`-equivariant family over
`𝔸¹` with a linearized polarization restricting to `L^r` (`r = exponent`) on the fibre over one
and trivial off zero. The polarization is ample on the (Noetherian) total space, equivalently
relatively ample over the affine base `𝔸¹` (BHJ, Definition 2.2, ample test configurations).
No stability conclusion is included. -/
structure TestConfiguration (X : Over (Base k)) (L : X.left.Modules) where
  total : Over (Base k)
  projection : total ⟶ AffineLine k
  [flat : Flat projection.left]
  [proper : IsProper projection.left]
  projective : RelativeProjectivity.IsHProjectiveOver projection
  [action : ModObj (Torus k) total]
  baseAction : ModObj (Torus k) (AffineLine k)
  equivariant :
    letI := baseAction
    γ[Torus k,total] ≫ projection = (Torus k ◁ projection) ≫ γ[Torus k,AffineLine k]
  base_coordinate :
    letI := baseAction
    (γ[Torus k,AffineLine k]).left.appTop
        ((Scheme.ΓSpecIso (.of (Polynomial k))).inv Polynomial.X) =
      (fst (Torus k) (AffineLine k)).left.appTop
          ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv (LaurentPolynomial.T 1)) *
        (snd (Torus k) (AffineLine k)).left.appTop
          ((Scheme.ΓSpecIso (.of (Polynomial k))).inv Polynomial.X)
  polarization : total.left.Modules
  line : IsLineBundle polarization
  [noetherian : IsNoetherian total.left]
  ample : ProjectiveLineSystems.IsAmpleLine ⟨polarization, line⟩
  linearization : Linearization (Torus k) total polarization
  exponent : ℕ
  positiveExponent : 0 < exponent
  fibreOne : (pullback projection (affinePoint k 1)) ≅ X
  fibrePolarization : (Scheme.Modules.pullback
    (pullback.fst projection (affinePoint k 1)).left).obj polarization ≅
      (Scheme.Modules.pullback fibreOne.hom.left).obj (power L exponent)
  genericTrivialization :
    pullback projection (torusInclusion k) ≅ X ⊗ Torus k
  genericOverTorus :
    genericTrivialization.hom ≫ snd X (Torus k) = pullback.snd _ _
  genericPolarization : (Scheme.Modules.pullback
    (pullback.fst projection (torusInclusion k)).left).obj polarization ≅
      (Scheme.Modules.pullback genericTrivialization.hom.left).obj
        ((Scheme.Modules.pullback (fst X (Torus k)).left).obj (power L exponent))

attribute [instance] TestConfiguration.flat TestConfiguration.proper
  TestConfiguration.action TestConfiguration.noetherian


/-- The actual inclusion of the identified fibre over one into the total scheme. -/
def fibreInclusion {X : Over (Base k)} {L : X.left.Modules}
    (T : TestConfiguration k X L) : X ⟶ T.total :=
  T.fibreOne.inv ≫ pullback.fst T.projection (affinePoint k 1)

/-- The actual fibre-one line comparison, with all native pullback compositions. -/
def fibreLineIso {X : Over (Base k)} {L : X.left.Modules}
    (T : TestConfiguration k X L) :
    (Scheme.Modules.pullback (fibreInclusion k T).left).obj T.polarization ≅ power L T.exponent :=
  ((Scheme.Modules.pullbackComp T.fibreOne.inv.left
    (pullback.fst T.projection (affinePoint k 1)).left).app T.polarization).symm ≪≫
  (Scheme.Modules.pullback T.fibreOne.inv.left).mapIso T.fibrePolarization ≪≫
  (Scheme.Modules.pullbackComp T.fibreOne.inv.left T.fibreOne.hom.left).app (power L T.exponent) ≪≫
  (Scheme.Modules.pullbackCongr
    (congrArg Over.Hom.left T.fibreOne.inv_hom_id)).app (power L T.exponent) ≪≫
  (Scheme.Modules.pullbackId X.left).app (power L T.exponent)

/-- The actual torus/fibre-one action pair; no generic trivialization is freely selected. -/
def actionPair {X : Over (Base k)} {L : X.left.Modules} (T : TestConfiguration k X L) :
    X ⊗ Torus k ⟶ Torus k ⊗ T.total :=
  (β_ X (Torus k)).hom ≫ (Torus k ◁ fibreInclusion k T)

theorem actionPair_projection {X : Over (Base k)} {L : X.left.Modules}
    (T : TestConfiguration k X L) :
    actionPair k T ≫ snd (Torus k) T.total = fst X (Torus k) ≫ fibreInclusion k T := by
  simp [actionPair, Category.assoc]

/-- The given generic line comparison transported to the actual X×G_m scheme. -/
def givenGenericLineMap {X : Over (Base k)} {L : X.left.Modules}
    (T : TestConfiguration k X L) :
    (Scheme.Modules.pullback
      (T.genericTrivialization.inv ≫ pullback.fst T.projection (torusInclusion k)).left).obj
        T.polarization ⟶
    (Scheme.Modules.pullback (fst X (Torus k)).left).obj (power L T.exponent) :=
  (Scheme.Modules.pullbackComp T.genericTrivialization.inv.left
    (pullback.fst T.projection (torusInclusion k)).left).inv.app T.polarization ≫
  (Scheme.Modules.pullback T.genericTrivialization.inv.left).map T.genericPolarization.hom ≫
  (Scheme.Modules.pullbackComp T.genericTrivialization.inv.left
    T.genericTrivialization.hom.left).hom.app
      ((Scheme.Modules.pullback (fst X (Torus k)).left).obj (power L T.exponent)) ≫
  (Scheme.Modules.pullbackCongr
    (congrArg Over.Hom.left T.genericTrivialization.inv_hom_id)).hom.app
      ((Scheme.Modules.pullback (fst X (Torus k)).left).obj (power L T.exponent)) ≫
  (Scheme.Modules.pullbackId (X ⊗ Torus k).left).hom.app
      ((Scheme.Modules.pullback (fst X (Torus k)).left).obj (power L T.exponent))

/-- The canonical generic line comparison computed from the actual action and fibre-one line. -/
def canonicalGenericLineMap {X : Over (Base k)} {L : X.left.Modules}
    (T : TestConfiguration k X L)
    (h : T.genericTrivialization.inv ≫ pullback.fst T.projection (torusInclusion k) =
      actionPair k T ≫ γ[Torus k,T.total]) :
    (Scheme.Modules.pullback
      (T.genericTrivialization.inv ≫ pullback.fst T.projection (torusInclusion k)).left).obj
        T.polarization ⟶
    (Scheme.Modules.pullback (fst X (Torus k)).left).obj (power L T.exponent) :=
  (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left h)).hom.app T.polarization ≫
  LinearizedLineBundles.reindexHom (actionPair k T).left T.linearization.comparison.hom ≫
  (Scheme.Modules.pullbackCongr
    (congrArg Over.Hom.left (actionPair_projection k T))).hom.app T.polarization ≫
  (Scheme.Modules.pullbackComp (fst X (Torus k)).left (fibreInclusion k T).left).inv.app
    T.polarization ≫
  (Scheme.Modules.pullback (fst X (Torus k)).left).map (fibreLineIso k T).hom

/-- A genuinely normalized test configuration: both scheme and line generic trivializations
are fixed by the actual action, rather than independent isomorphisms. -/
structure NormalizedTestConfiguration (X : Over (Base k)) (L : X.left.Modules)
    extends TestConfiguration k X L where
  actionNormalized :
    toTestConfiguration.genericTrivialization.inv ≫
      pullback.fst toTestConfiguration.projection (torusInclusion k) =
        actionPair k toTestConfiguration ≫ γ[Torus k,toTestConfiguration.total]
  lineNormalized : givenGenericLineMap k toTestConfiguration =
    canonicalGenericLineMap k toTestConfiguration actionNormalized

end MathlibExt.AlgebraicGeometry.PolarizedTestConfigurations
