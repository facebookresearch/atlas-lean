/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CotangentTransversalTests

/-!
# Native cotangent bundle and transversality source adapters

The actual one-form sheaf, all local differential generators, the
section-representing total space, and the full scheme differential are
fixed in MathlibExt. The cotangent constructor applies the source's
V(E) = Spec Sym(E) to the dual of Ω¹, representing sections of Ω¹.
The source construction requests supply those exact
objects and their finite-image comparison. They do not introduce an
arbitrary cone map or a microsupport theorem as background input.

Sources: Beilinson, arXiv:1505.06768v8, Section 1.2, Lemma (ii);
AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
Constructions/VectorBundleOfModule.lean and
Topology/Sheaves/Modules/Differentials.lean (Apache 2.0).
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CotangentTransversalTestsWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry
open AlgebraicDifferentialSheaves LocalDifferentialPullbacks
open CotangentBundleTestModels CotangentTransversalTests

def_wanted nativeCotangentBundle (k : Type) [Field k]
    (X : Over (Spec (.of k))) [Smooth X.hom] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] : CotangentBundle X

def_wanted nativeKahlerDifferential (k : Type) [Field k]
    (X U : Over (Spec (.of k))) (h : U ⟶ X) : PullbackDifferential X h

def_wanted nativeClosedCotangentImage (k : Type) [Field k]
    (X U : Over (Spec (.of k))) [Smooth X.hom] [Smooth U.hom]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType U.hom]
    [QuasiCompact X.hom] [QuasiCompact U.hom]
    (BX : CotangentBundle X) (BU : CotangentBundle U)
    (C : ClosedCone X BX) (h : U ⟶ X) (D : PullbackDifferential X h)
    (transversal : CTransversal C h D) : ClosedPullImage C h D BU

theorem_wanted nativeImageGeometricNormalization (k : Type) [Field k]
    (X U : Over (Spec (.of k))) [Smooth X.hom] [Smooth U.hom]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType U.hom]
    [QuasiCompact X.hom] [QuasiCompact U.hom]
    (BX : CotangentBundle X) (BU : CotangentBundle U)
    (C : ClosedCone X BX) (h : U ⟶ X) (D : PullbackDifferential X h) :
    pullImageSupport C h D BU = geometricPullImageSupport C h D BU

private def check_nativeCotangentBundle (k : Type) [Field k]
    (X : Over (Spec (.of k))) [Smooth X.hom] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] : DefWanted (CotangentBundle X) := nativeCotangentBundle k X

private def check_nativeKahlerDifferential (k : Type) [Field k]
    (X U : Over (Spec (.of k))) (h : U ⟶ X) : DefWanted (PullbackDifferential X h) :=
  nativeKahlerDifferential k X U h

private def check_nativeClosedCotangentImage (k : Type) [Field k]
    (X U : Over (Spec (.of k))) [Smooth X.hom] [Smooth U.hom]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType U.hom]
    [QuasiCompact X.hom] [QuasiCompact U.hom]
    (BX : CotangentBundle X) (BU : CotangentBundle U)
    (C : ClosedCone X BX) (h : U ⟶ X) (D : PullbackDifferential X h)
    (transversal : CTransversal C h D) : DefWanted (ClosedPullImage C h D BU) :=
  nativeClosedCotangentImage k X U BX BU C h D transversal

private def check_nativeImageGeometricNormalization (k : Type) [Field k]
    (X U : Over (Spec (.of k))) [Smooth X.hom] [Smooth U.hom]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType U.hom]
    [QuasiCompact X.hom] [QuasiCompact U.hom]
    (BX : CotangentBundle X) (BU : CotangentBundle U)
    (C : ClosedCone X BX) (h : U ⟶ X) (D : PullbackDifferential X h) :
    ProofWanted (pullImageSupport C h D BU = geometricPullImageSupport C h D BU) :=
  nativeImageGeometricNormalization k X U BX BU C h D

end WantedExt.AlgebraicGeometry.CotangentTransversalTestsWanted
