/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CotangentTransversalTests
public import MathlibExt.AlgebraicGeometry.IntegerSchemeChow
public import MathlibExt.AlgebraicGeometry.TropicalTorIntersection
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.FieldTheory.Perfect

/-!
# Native local intersections with cotangent sections

Curve tests use arbitrary actual étale charts and maps to smooth curves.
A local frame is a section of the actual pulled one-form sheaf, generating
it on every scheme over the curve neighborhood. The differential section
is computed by the normalized Kähler differential and the total-space
universal property.

Components are the actual maximal irreducible closed subsets of the cone.
Their reduced ideal sheaves are pulled through the literal cotangent
pullback and the whole scheme differential. The local graph ideal is the
kernel of the actual section. Both local ideals use every affine germ
into the actual cotangent stalk ring. The pairing is the existing native
alternating Tor-length sum, with finite lengths and isolated proper
support recorded separately; no number or numerical callback is supplied.

Reference: Saito, arXiv:1510.03018v4, Definition 4.3 and formula (4.5),
printed pages 39--40; Fulton, Intersection Theory, Sections 7.1 and 8.2.
Integral scheme cycles and local Tor reuse `IntegerSchemeChow` and
`TropicalTorIntersection`, retaining their AxiomMath/Stacks revision
c496df0d9beea9deaeabcea8492605f9a0a2313b and Apache 2.0 notices.
Native Tor is Kim Morrison (2021); regular sequences are Brendan Murphy
(2024); module lengths are Andrew Yang (2025), Mathlib Apache 2.0 at
56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CotangentLocalIntersectionModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.TopologicalSpace _root_.Opposite
open GeneralModuleTotalSpaces AlgebraicDifferentialSheaves LocalDifferentialPullbacks
open CotangentBundleTestModels CotangentTransversalTests
open scoped BigOperators

variable {k : Type} [Field k] {X : Over (Spec (.of k))}
  {BX : CotangentBundle X} (C : ClosedCone X BX)

/-- Actual irreducible components of the closed cone, with no presentation names. -/
abbrev Component := {Z : Closeds BX.total //
  IsIrreducible (Z : Set BX.total) ∧ (Z : Set BX.total) ⊆ C.support ∧
    ∀ W : Closeds BX.total, IsIrreducible (W : Set BX.total) →
      (W : Set BX.total) ⊆ C.support → (Z : Set BX.total) ⊆ W → (W : Set BX.total) ⊆ Z}

def componentPoint (Z : Component C) : BX.total := Z.property.1.genericPoint

def componentIdeal (Z : Component C) : BX.total.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal Z.val

/-- Pure dimension of the actual scheme's irreducible closed subsets. -/
def PureDimension (V : Scheme.{0}) (n : ℕ) : Prop :=
  ∀ Z ∈ irreducibleComponents V, topologicalKrullDim Z = (n : ℕ)

def PureConeDimension (n : ℕ) : Prop :=
  ∀ Z : Component C, topologicalKrullDim (Z.val : Set BX.total) = (n : ℕ)

/-- Every actual étale chart and curve map is allowed; global quasicompactness
of the chart or of the curve is not part of this test carrier. -/
structure CurveTest where
  U : Over (Spec (.of k))
  Y : Over (Spec (.of k))
  [smoothU : Smooth U.hom]
  [curve : SmoothOfRelativeDimension 1 Y.hom]
  h : U ⟶ X
  [etale : Etale h.left]
  f : U ⟶ Y
  dh : PullbackDifferential X h
  df : PullbackDifferential Y f

attribute [instance] CurveTest.smoothU CurveTest.curve CurveTest.etale

def CurveTest.IsTransversalAt (P : CurveTest (X := X)) (Ω : GeometricField)
    (u : Spec (.of Ω.carrier) ⟶ P.U.left) : Prop :=
  CTransversalAt C P.h P.dh Ω u ∧
    ∀ v : Covector P.Y Ω (u ≫ P.f.left),
      PullImageAt C P.h P.dh Ω u (CotangentBundleTestModels.dh P.f P.df Ω u v) → v = 0

/-- Definition 4.3.1, including noncharacteristic points. -/
def AtMostIsolated (P : CurveTest (X := X)) (u : P.U.left) : Prop :=
  IsClosed ({u} : Set P.U.left) ∧ ∃ V : P.U.left.Opens, u ∈ V ∧
    ∀ (Ω : GeometricField) (v : Spec (.of Ω.carrier) ⟶ P.U.left),
      Set.range v ⊆ (V : Set P.U.left) \ {u} → P.IsTransversalAt C Ω v

variable (P : CurveTest (X := X)) (BU : CotangentBundle P.U) (u : P.U.left)

/-- A local basis is an actual one-form, with the scalar-generation property
on all scheme-valued tests over its curve neighborhood. -/
structure CurveFrame where
  targetOpen : P.Y.left.Opens
  contains : P.f.left u ∈ targetOpen
  oneForm : Γ((Scheme.Modules.pullback targetOpen.ι).obj (forms k P.Y 1), ⊤)
  basis : ∀ (T : Scheme.{0}) (g : T ⟶ targetOpen.toScheme),
    Function.Bijective (fun a : Γ(T, ⊤) ↦ a •
      pulledSection (forms k P.Y 1) targetOpen.ι oneForm
        (g ≫ targetOpen.ι) g rfl)

namespace CurveFrame

variable {P u} (ω : CurveFrame P u)

abbrev sourceOpen : P.U.left.Opens := P.f.left ⁻¹ᵁ ω.targetOpen
abbrev source : Scheme.{0} := ω.sourceOpen.toScheme
abbrev inclusion : ω.source ⟶ P.U.left := ω.sourceOpen.ι
abbrev curveMap : ω.source ⟶ ω.targetOpen.toScheme := P.f.left ∣_ ω.targetOpen
def sourcePoint : ω.source := ⟨u, ω.contains⟩

/-- Pulling the literal local curve basis through the same normalized df. -/
def differentialSection : Γ((Scheme.Modules.pullback ω.inclusion).obj (forms k P.U 1), ⊤) :=
  fibreMap P.df ω.inclusion
    (pulledSection (forms k P.Y 1) ω.targetOpen.ι ω.oneForm
      (ω.inclusion ≫ P.f.left) ω.curveMap (morphismRestrict_ι _ _))

def sectionMap : ω.source ⟶ BU.total := BU.lift ω.inclusion ω.differentialSection

abbrev ambient : Scheme.{0} := pullback BU.projection ω.inclusion
abbrev ambientMap : ω.ambient BU ⟶ BU.total := pullback.fst BU.projection ω.inclusion

/-- The section graph in the actual cotangent bundle restricted to its domain. -/
def graph : ω.source ⟶ ω.ambient BU :=
  pullback.lift (ω.sectionMap BU) (𝟙 ω.source) (by
    simpa only [sectionMap, Category.id_comp] using
      BU.lift_over ω.inclusion ω.differentialSection)

def point : ω.ambient BU := ω.graph BU ω.sourcePoint

abbrev stalkRing := (ω.ambient BU).presheaf.stalk (ω.point BU)

def graphIdeal : (ω.ambient BU).IdealSheafData := (ω.graph BU).ker

end CurveFrame

def pulledComponentIdeal (Z : Component C) : BU.total.IdealSheafData :=
  ((componentIdeal C Z).comap (pullback.fst BX.projection P.h.left)).map
    (CotangentBundleDifferentialMaps.bundleDifferential BX BU P.h P.dh)

/-- The ideal's actual stalk is generated by all affine germs. -/
def stalkIdeal {V : Scheme.{0}} (I : V.IdealSheafData) (q : V) :
    Ideal (V.presheaf.stalk q) :=
  ⨆ (W : V.affineOpens) (h : q ∈ W.1), (I.ideal W).map (V.presheaf.germ W.1 q h).hom

variable (ω : CurveFrame P u)

def localComponentIdeal (Z : Component C) : Ideal (ω.stalkRing BU) :=
  stalkIdeal ((pulledComponentIdeal C P BU Z).comap (ω.ambientMap BU)) (ω.point BU)

def localGraphIdeal : Ideal (ω.stalkRing BU) := stalkIdeal (ω.graphIdeal BU) (ω.point BU)

/-- Actual regular graph coordinates; higher-Tor vanishing is not assumed. -/
structure GraphCoordinates (n : ℕ) where
  parameters : List (ω.stalkRing BU)
  length : parameters.length = n
  ideal : Ideal.ofList parameters = localGraphIdeal P BU u ω
  regular : RingTheory.Sequence.IsRegular (ω.stalkRing BU) parameters

/-- Source local intersection data consists of genuine geometric and
finiteness properties of the already fixed ideals. -/
structure LocalIntersection (n : ℕ) where
  [finiteComponents : Finite (Component C)]
  [differentialIso : IsIso
    (CotangentBundleDifferentialMaps.bundleDifferential BX BU P.h P.dh)]
  [graphClosed : IsClosedImmersion (ω.graph BU)]
  coordinates : GraphCoordinates P BU u ω n
  ambientDimension : ringKrullDim (ω.stalkRing BU) = (2 * n : ℕ)
  isolatedSupport : ∃ N : (ω.ambient BU).Opens, ω.point BU ∈ N ∧
    ∀ Z : Component C, (N : Set (ω.ambient BU)) ∩
      (((pulledComponentIdeal C P BU Z).comap (ω.ambientMap BU)).support ∩
        (ω.graphIdeal BU).support) ⊆ {ω.point BU}
  finiteTor : ∀ Z : Component C, TropicalTorIntersection.FiniteTor (ω.stalkRing BU)
    (localComponentIdeal C P BU u ω Z) (localGraphIdeal P BU u ω)

def componentPairing {n : ℕ} (I : LocalIntersection C P BU u ω n) (Z : Component C) : ℤ :=
  TropicalTorIntersection.torCoefficient (ω.stalkRing BU) (I.finiteTor Z)

/-- The local pairing is the coefficient-weighted actual Tor-length sum. -/
def localPairing {n : ℕ} (I : LocalIntersection C P BU u ω n)
    (A : AlgebraicCycle BX.total ℚ) : ℚ := by
  classical
  letI := I.finiteComponents
  letI := Fintype.ofFinite (Component C)
  exact ∑ Z : Component C, A (componentPoint C Z) * (componentPairing C P BU u ω I Z : ℚ)

end MathlibExt.AlgebraicGeometry.CotangentLocalIntersectionModels
