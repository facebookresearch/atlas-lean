/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CotangentBundleDifferentialMaps
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Differential-normalized cotangent test pairs

Inverse transversality removes the nonzero intersection with the actual
kernel of dh. Forward transversality removes nonzero covectors in the
inverse image of C under df. The two tests use the same normalized Kähler
sheaf morphisms and their actual geometric fibres. The pulled cone image
is the image of those covectors under dh, without an arbitrary cone map.

Reference: Beilinson, arXiv:1505.06768v8, Section 1.2. Local acyclicity
and microsupport require a separately normalized étale comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CotangentTransversalTests

open _root_.CategoryTheory _root_.AlgebraicGeometry
open AlgebraicDifferentialSheaves LocalDifferentialPullbacks CotangentBundleTestModels

variable {k : Type} [Field k] {X : Over (Spec (.of k))}
  {B : CotangentBundle X} (C : ClosedCone X B)

/-- Ker(dh) intersects the cone only at zero, in the actual cotangent fibre. -/
def CTransversalAt {U : Over (Spec (.of k))} (h : U ⟶ X)
    (D : PullbackDifferential X h) (Ω : GeometricField)
    (u : Spec (.of Ω.carrier) ⟶ U.left) : Prop :=
  ∀ v : Covector X Ω (u ≫ h.left), C.memFibre Ω (u ≫ h.left) v → dh h D Ω u v = 0 → v = 0

/-- Inverse transversality is tested at every geometric point. -/
def CTransversal {U : Over (Spec (.of k))} (h : U ⟶ X)
    (D : PullbackDifferential X h) : Prop :=
  ∀ (Ω : GeometricField) (u : Spec (.of Ω.carrier) ⟶ U.left), CTransversalAt C h D Ω u

/-- The nonzero inverse image under df is empty. The source covector lives
in the target's actual cotangent module, so this is not the kernel test. -/
def ForwardCTransversalAt {Y : Over (Spec (.of k))} (f : X ⟶ Y)
    (D : PullbackDifferential Y f) (Ω : GeometricField)
    (x : Spec (.of Ω.carrier) ⟶ X.left) : Prop :=
  ∀ v : Covector Y Ω (x ≫ f.left), C.memFibre Ω x (dh f D Ω x v) → v = 0

def ForwardCTransversal {Y : Over (Spec (.of k))} (f : X ⟶ Y)
    (D : PullbackDifferential Y f) : Prop :=
  ∀ (Ω : GeometricField) (x : Spec (.of Ω.carrier) ⟶ X.left),
    ForwardCTransversalAt C f D Ω x

/-- Membership in the actual dh image over the specified geometric point. -/
def PullImageAt {U : Over (Spec (.of k))} (h : U ⟶ X)
    (D : PullbackDifferential X h) (Ω : GeometricField)
    (u : Spec (.of Ω.carrier) ⟶ U.left) (v : Covector U Ω u) : Prop :=
  ∃ a : Covector X Ω (u ≫ h.left), C.memFibre Ω (u ≫ h.left) a ∧ dh h D Ω u a = v

/-- The geometric image inside the actual cotangent total space of U. -/
def geometricPullImageSupport {U : Over (Spec (.of k))} (h : U ⟶ X)
    (D : PullbackDifferential X h) (BU : CotangentBundle U) : Set BU.total :=
  {q | ∃ (Ω : GeometricField) (u : Spec (.of Ω.carrier) ⟶ U.left)
    (a : Covector X Ω (u ≫ h.left)),
    C.memFibre Ω (u ≫ h.left) a ∧ q ∈ Set.range (covectorPoint U BU Ω u (dh h D Ω u a))}

/-- The cone image is the actual image under the whole scheme differential. -/
def pullImageSupport {U : Over (Spec (.of k))} (h : U ⟶ X)
    (D : PullbackDifferential X h) (BU : CotangentBundle U) : Set BU.total :=
  CotangentBundleDifferentialMaps.coneImage B BU h D C

/-- A test pair of actual smooth varieties and source-normalized differentials. -/
structure TestPair where
  U : Over (Spec (.of k))
  Y : Over (Spec (.of k))
  [smoothU : Smooth U.hom]
  [smoothY : Smooth Y.hom]
  [finiteU : LocallyOfFiniteType U.hom]
  [compactU : QuasiCompact U.hom]
  [finiteY : LocallyOfFiniteType Y.hom]
  [compactY : QuasiCompact Y.hom]
  h : U ⟶ X
  f : U ⟶ Y
  dh : PullbackDifferential X h
  df : PullbackDifferential Y f

attribute [instance] TestPair.smoothU TestPair.smoothY TestPair.finiteU TestPair.finiteY
  TestPair.compactU TestPair.compactY

/-- Both source tests at u, with h°C computed by the same dh on the same fibre. -/
def TestPair.IsTransversalAt (P : TestPair (X := X)) (Ω : GeometricField)
    (u : Spec (.of Ω.carrier) ⟶ P.U.left) : Prop :=
  CTransversalAt C P.h P.dh Ω u ∧
    ∀ v : Covector P.Y Ω (u ≫ P.f.left),
      PullImageAt C P.h P.dh Ω u (CotangentBundleTestModels.dh P.f P.df Ω u v) → v = 0

def TestPair.IsTransversal (P : TestPair (X := X)) : Prop :=
  ∀ (Ω : GeometricField) (u : Spec (.of Ω.carrier) ⟶ P.U.left),
    P.IsTransversalAt C Ω u

/-- Closed conical subsets of the cotangent bundle $T^*U$ whose support is the image of
$C \times_X U$ under the differential $dh : T^*X \times_X U \to T^*U$ of $h : U \to X$. -/
abbrev ClosedPullImage {U : Over (Spec (.of k))} (h : U ⟶ X)
    (D : PullbackDifferential X h) (BU : CotangentBundle U) :=
  {CU : ClosedCone U BU // CU.support = pullImageSupport C h D BU}

end MathlibExt.AlgebraicGeometry.CotangentTransversalTests
