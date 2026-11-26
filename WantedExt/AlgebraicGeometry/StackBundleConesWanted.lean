/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.StackBundleCones

/-!
# Native bundle-stack and intrinsic-cone construction requests

Every existence statement retains the source-qualified finite-type
Artin/field scope. Bundle-stack objects carry a global O-linear quotient
pseudofunctor and source-compatible local frames. Intrinsic-cone objects
carry all actual local views and coherent Rees/Kähler-normalized descent,
whose comparison 2-cells preserve zero and all-algebra homotheties.
Conical embeddings test the actual global map in E.linear, including
coefficient arrows and refinement cells; a local embedding isomorphism
does not supply the global compatibility.
Bundle-stack homotopy retains quotient stratification. Cone base change
chooses compatible source presentations and supplies a closed map into
the actual pulled cone; arbitrary source maps need not be flat.

Sources: Kresch arXiv:math/9810166v1, Theorem 2.1.12(vi),(x),
Proposition 4.5.5(iii) and Proposition 5.3.2;
Behrend--Fantechi arXiv:alg-geom/9601010, Sections 1--3;
Manolache arXiv:0805.2065v2, Definitions 2.7--2.10 and Proposition 2.26.
The Rees producer and its scheme maps are completed Mathlib/Axiom source
integration, with revision and Apache attribution in AffineNormalConeMaps.
-/

@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.StackBundleConesWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.StackCycleGeometry _root_.AlgebraicGeometry.StackCycleRelations
open _root_.AlgebraicGeometry.StackAffineModules _root_.AlgebraicGeometry.StackFibreModels
open _root_.AlgebraicGeometry.StackVectorBundles _root_.AlgebraicGeometry.StackProjectiveModels
open _root_.AlgebraicGeometry.StackChowGroups _root_.AlgebraicGeometry.StackBundleCones

public def_wanted vector_bundle (k : Type) [Field k]
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (r : ℕ) (M : VectorModule X r) :
    {E : VectorBundle X // E.rank = r ∧ E.module.val = M.val ∧ FiniteTypeArtin k E.total}

public theorem_wanted vector_bundle_finite_type (k : Type) [Field k]
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (E : VectorBundle X) :
    FiniteTypeArtin k E.total

public def_wanted projectivization (k : Type) [Field k]
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (M : FPModule X) :
    {P : ProjectiveBundle M // FiniteTypeArtin k P.total}

public def_wanted zero_section (k : Type) [Field k]
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (E : VectorBundle X) : ZeroSection E

public def_wanted quotient_stack (k : Type) [Field k]
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X)
    (E F : VectorBundle X) (d : BundleMap E F) :
    {Q : QuotientStackModel d // FiniteTypeArtin k Q.total}

public def_wanted bundle_stack_pullback (k : Type) [Field k]
    (T X : Stack (Spec (.of k))) (hT : FiniteTypeArtin k T) (hX : FiniteTypeArtin k X)
    (p : StackHom T X) (E : VectorBundleStack X) : BundleStackPullback p E

/-- **The bundle stack of a two-term complex of vector bundles.** For a field $k$, a finite-type
Artin stack $X$ over $k$ (`FiniteTypeArtin k X`: representable, separated and quasi-compact
diagonal, and a smooth atlas locally of finite type and quasi-compact over $k$) and a map of vector
bundles $d : E \to F$ on $X$: a vector bundle stack $B$ on $X$ of virtual rank
$\operatorname{rk} F - \operatorname{rk} E$ that is the quotient of $d$ (`IsQuotientOf B d`: its
linear model is equivalent, coherently over all affine points of $X$, to the strict linear diagram
of $d$). -/
public def_wanted bundle_stack_from_quotient (k : Type) [Field k]
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X)
    (E F : VectorBundle X) (d : BundleMap E F) :
    {B : VectorBundleStack X // IsQuotientOf B d ∧ B.virtualRank = (F.rank : ℤ) - E.rank}

public theorem_wanted bundle_stack_finite_type (k : Type) [Field k]
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (E : VectorBundleStack X) :
    FiniteTypeArtin k E.total

public def_wanted bundle_projection_pullback (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (E : VectorBundle X)
    (hE : FiniteTypeArtin k E.total) : FlatChowPullData D K hE hX E.projection E.rank

public def_wanted bundle_homotopy (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (E : VectorBundle X)
    (hE : FiniteTypeArtin k E.total) (P : FlatChowPullData D K hE hX E.projection E.rank) :
    BundleHomotopyData D K hX E hE P

public def_wanted bundle_stack_projection_pullback (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (E : VectorBundleStack X)
    (hE : FiniteTypeArtin k E.total) : FlatChowPullData D K hE hX E.projection E.virtualRank

public def_wanted bundle_stack_homotopy (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (strata : QuotientStratification X)
    (E : VectorBundleStack X) (hE : FiniteTypeArtin k E.total)
    (P : FlatChowPullData D K hE hX E.projection E.virtualRank) :
    BundleStackHomotopyData D K hX E hE P

public def_wanted DM_quotient_stratification (k : Type) [Field k]
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (DM : X.IsDeligneMumfordStack) :
    QuotientStratification X

public def_wanted intrinsic_cone (k : Type) [Field k]
    (F G : Stack (Spec (.of k))) (hF : FiniteTypeArtin k F) (hG : FiniteTypeArtin k G)
    (f : StackHom F G) (DM : IsDMType f) :
    {C : IntrinsicConeModel f // FiniteTypeArtin k C.total}

public def_wanted cone_base_change (k : Type) [Field k]
    (F G T : Stack (Spec (.of k))) (hF : FiniteTypeArtin k F) (hG : FiniteTypeArtin k G)
    (hT : FiniteTypeArtin k T) (f : StackHom F G) (g : StackHom T G) (DM : IsDMType f)
    (P : TwoCartesianSquare f g) (hP : FiniteTypeArtin k P.apex) (C : IntrinsicConeModel f)
    (hC : FiniteTypeArtin k C.total) :
    Σ C' : {C' : IntrinsicConeModel P.snd // FiniteTypeArtin k C'.total},
      ConeBaseChangeData P.snd f P.fst g C'.val C

private def check_vector_bundle (k : Type) [Field k]
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (r : ℕ) (M : VectorModule X r) :
    DefWanted {E : VectorBundle X // E.rank = r ∧ E.module.val = M.val ∧ FiniteTypeArtin k E.total} :=
  vector_bundle k X hX r M

private def check_vector_bundle_finite_type (k : Type) [Field k]
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (E : VectorBundle X) :
    ProofWanted (FiniteTypeArtin k E.total) := vector_bundle_finite_type k X hX E

private def check_projectivization (k : Type) [Field k]
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (M : FPModule X) :
    DefWanted {P : ProjectiveBundle M // FiniteTypeArtin k P.total} := projectivization k X hX M

private def check_zero_section (k : Type) [Field k]
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (E : VectorBundle X) :
    DefWanted (ZeroSection E) := zero_section k X hX E

private def check_quotient_stack (k : Type) [Field k]
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (E F : VectorBundle X) (d : BundleMap E F) :
    DefWanted {Q : QuotientStackModel d // FiniteTypeArtin k Q.total} := quotient_stack k X hX E F d

private def check_bundle_stack_pullback (k : Type) [Field k]
    (T X : Stack (Spec (.of k))) (hT : FiniteTypeArtin k T) (hX : FiniteTypeArtin k X)
    (p : StackHom T X) (E : VectorBundleStack X) : DefWanted (BundleStackPullback p E) :=
  bundle_stack_pullback k T X hT hX p E

private def check_bundle_stack_from_quotient (k : Type) [Field k]
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X)
    (E F : VectorBundle X) (d : BundleMap E F) :
    DefWanted {B : VectorBundleStack X // IsQuotientOf B d ∧ B.virtualRank = (F.rank : ℤ) - E.rank} :=
  bundle_stack_from_quotient k X hX E F d

private def check_bundle_stack_finite_type (k : Type) [Field k]
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (E : VectorBundleStack X) :
    ProofWanted (FiniteTypeArtin k E.total) := bundle_stack_finite_type k X hX E

private def check_bundle_projection_pullback (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (E : VectorBundle X)
    (hE : FiniteTypeArtin k E.total) : DefWanted (FlatChowPullData D K hE hX E.projection E.rank) :=
  bundle_projection_pullback k D K X hX E hE

private def check_bundle_homotopy (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (E : VectorBundle X)
    (hE : FiniteTypeArtin k E.total) (P : FlatChowPullData D K hE hX E.projection E.rank) :
    DefWanted (BundleHomotopyData D K hX E hE P) := bundle_homotopy k D K X hX E hE P

private def check_bundle_stack_projection_pullback (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (E : VectorBundleStack X)
    (hE : FiniteTypeArtin k E.total) :
    DefWanted (FlatChowPullData D K hE hX E.projection E.virtualRank) :=
  bundle_stack_projection_pullback k D K X hX E hE

private def check_bundle_stack_homotopy (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (strata : QuotientStratification X)
    (E : VectorBundleStack X) (hE : FiniteTypeArtin k E.total)
    (P : FlatChowPullData D K hE hX E.projection E.virtualRank) :
    DefWanted (BundleStackHomotopyData D K hX E hE P) := bundle_stack_homotopy k D K X hX strata E hE P

private def check_DM_quotient_stratification (k : Type) [Field k]
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (DM : X.IsDeligneMumfordStack) :
    DefWanted (QuotientStratification X) := DM_quotient_stratification k X hX DM

private def check_intrinsic_cone (k : Type) [Field k]
    (F G : Stack (Spec (.of k))) (hF : FiniteTypeArtin k F) (hG : FiniteTypeArtin k G)
    (f : StackHom F G) (DM : IsDMType f) :
    DefWanted {C : IntrinsicConeModel f // FiniteTypeArtin k C.total} := intrinsic_cone k F G hF hG f DM

private def check_cone_base_change (k : Type) [Field k]
    (F G T : Stack (Spec (.of k))) (hF : FiniteTypeArtin k F) (hG : FiniteTypeArtin k G)
    (hT : FiniteTypeArtin k T) (f : StackHom F G) (g : StackHom T G) (DM : IsDMType f)
    (P : TwoCartesianSquare f g) (hP : FiniteTypeArtin k P.apex) (C : IntrinsicConeModel f)
    (hC : FiniteTypeArtin k C.total) : DefWanted
    (Σ C' : {C' : IntrinsicConeModel P.snd // FiniteTypeArtin k C'.total},
      ConeBaseChangeData P.snd f P.fst g C'.val C) :=
  cone_base_change k F G T hF hG hT f g DM P hP C hC

end WantedExt.AlgebraicGeometry.StackBundleConesWanted
