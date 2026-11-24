/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.StackChowGroups

/-!
# Integral finite-type Artin-stack Chow construction requests

All constructors are over a fixed field. The carrier is the actual
vector-bundle/projective presentation in `StackChowGroups`; none of the
requested functoriality or comparison laws is an input to that carrier.

Source: Kresch arXiv:math/9810166v1, Convention 2.1.1,
Definitions 2.1.2--2.1.11, Theorem 2.1.12 and Remarks 2.1.5--2.1.10.
Ordinary scheme cycle operations and principal divisors are completed
source integration from AxiomMath/Stacks revision
c496df0d9beea9deaeabcea8492605f9a0a2313b (Apache 2.0), not requests
for new ordinary-scheme Chow theory.
-/

@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.StackChowGroupsWanted

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.GeneralStackGeometry _root_.AlgebraicGeometry.StackCycleGeometry
open _root_.AlgebraicGeometry.StackCycleRelations _root_.AlgebraicGeometry.StackChowGroups
open _root_.AlgebraicGeometry.StackVectorBundles _root_.AlgebraicGeometry.StackProjectiveModels

public def_wanted cycle_construction (k : Type) [Field k] :
    CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)

public def_wanted kresch_presentation (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) : KreschPresentation D

public def_wanted cycle_classes (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) : CycleClassData D K X hX

public def_wanted projective_pushforward (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (X Y : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (hY : FiniteTypeArtin k Y)
    (f : StackHom X Y) (projective : ProjectiveMorphism f) : ProjectiveChowPushData D K hX hY f

public def_wanted flat_pullback (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (X Y : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (hY : FiniteTypeArtin k Y)
    (f : StackHom X Y) (shift : ℤ) (flat : FlatMorphism f shift) :
    FlatChowPullData D K hX hY f shift

public def_wanted scheme_comparison (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (U : IntegerSchemeChow.FieldScheme k) (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X)
    (C : SchemeCycleDictionary U X) (classes : CycleClassData D K X hX) :
    SchemeComparisonData D K U X hX C classes

public theorem_wanted scheme_comparison_isomorphism (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (U : IntegerSchemeChow.FieldScheme k) (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X)
    (C : SchemeCycleDictionary U X) (classes : CycleClassData D K X hX)
    (comparison : SchemeComparisonData D K U X hX C classes) (d : ℤ) :
    Function.Bijective (comparison.map d)

public theorem_wanted bundle_surjections_same (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (B : BundleTransitions D)
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X)
    (E F : BundleStage (scope := FiniteTypeArtin k) X) (q r : BundleArrow E F) (d : ℤ) :
    bundleTransition D B hX d q = bundleTransition D B hX d r

public theorem_wanted projective_pushforward_composition (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (X Y Z : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (hY : FiniteTypeArtin k Y)
    (hZ : FiniteTypeArtin k Z) (f : StackHom X Y) (g : StackHom Y Z)
    (F : ProjectiveChowPushData D K hX hY f) (G : ProjectiveChowPushData D K hY hZ g)
    (H : ProjectiveChowPushData D K hX hZ (Pseudofunctor.StrongTrans.vcomp f g)) (d : ℤ) :
    H.map d = (G.map d).comp (F.map d)

public theorem_wanted excision (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (Z : ClosedSubstack X)
    (hZ : FiniteTypeArtin k Z.source) (U : OpenSubstack X) (hU : FiniteTypeArtin k U.source)
    (complement : OpenClosedComplement Z U)
    (push : ProjectiveChowPushData D K hZ hX Z.inclusion)
    (restrict : FlatChowPullData D K hU hX U.inclusion 0) (d : ℤ) :
    (push.map d).range = (restrict.map d).ker ∧ Function.Surjective (restrict.map d)

public theorem_wanted above_dimension (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (a : CycleAtlas X)
    (n : ℕ) (dimension : topologicalKrullDim a.atlas.U.left = (n : ℕ))
    (d : ℤ) (above : (n : ℤ) - a.relativeRank < d) : Subsingleton (ChowGroup D K X hX d)

public def_wanted rational_DM_pushforward (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (X Y : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (hY : FiniteTypeArtin k Y)
    (f : StackHom X Y) (M : DMProperModel D K hX hY f) : RationalPushData D K hX hY f M

private def check_cycle_construction (k : Type) [Field k] :
    DefWanted (CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) := cycle_construction k

private def check_kresch_presentation (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) : DefWanted (KreschPresentation D) :=
  kresch_presentation k D

private def check_cycle_classes (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) : DefWanted (CycleClassData D K X hX) :=
  cycle_classes k D K X hX

private def check_projective_pushforward (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (X Y : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (hY : FiniteTypeArtin k Y)
    (f : StackHom X Y) (projective : ProjectiveMorphism f) :
    DefWanted (ProjectiveChowPushData D K hX hY f) :=
  projective_pushforward k D K X Y hX hY f projective

private def check_flat_pullback (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (X Y : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (hY : FiniteTypeArtin k Y)
    (f : StackHom X Y) (shift : ℤ) (flat : FlatMorphism f shift) :
    DefWanted (FlatChowPullData D K hX hY f shift) := flat_pullback k D K X Y hX hY f shift flat

private def check_scheme_comparison (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (U : IntegerSchemeChow.FieldScheme k) (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X)
    (C : SchemeCycleDictionary U X) (classes : CycleClassData D K X hX) :
    DefWanted (SchemeComparisonData D K U X hX C classes) := scheme_comparison k D K U X hX C classes

private def check_scheme_comparison_isomorphism (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (U : IntegerSchemeChow.FieldScheme k) (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X)
    (C : SchemeCycleDictionary U X) (classes : CycleClassData D K X hX)
    (comparison : SchemeComparisonData D K U X hX C classes) (d : ℤ) :
    ProofWanted (Function.Bijective (comparison.map d)) :=
  scheme_comparison_isomorphism k D K U X hX C classes comparison d

private def check_bundle_surjections_same (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (B : BundleTransitions D)
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X)
    (E F : BundleStage (scope := FiniteTypeArtin k) X) (q r : BundleArrow E F) (d : ℤ) :
    ProofWanted (bundleTransition D B hX d q = bundleTransition D B hX d r) :=
  bundle_surjections_same k D B X hX E F q r d

private def check_projective_pushforward_composition (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (X Y Z : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (hY : FiniteTypeArtin k Y)
    (hZ : FiniteTypeArtin k Z) (f : StackHom X Y) (g : StackHom Y Z)
    (F : ProjectiveChowPushData D K hX hY f) (G : ProjectiveChowPushData D K hY hZ g)
    (H : ProjectiveChowPushData D K hX hZ (Pseudofunctor.StrongTrans.vcomp f g)) (d : ℤ) :
    ProofWanted (H.map d = (G.map d).comp (F.map d)) :=
  projective_pushforward_composition k D K X Y Z hX hY hZ f g F G H d

private def check_excision (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (Z : ClosedSubstack X)
    (hZ : FiniteTypeArtin k Z.source) (U : OpenSubstack X) (hU : FiniteTypeArtin k U.source)
    (complement : OpenClosedComplement Z U)
    (push : ProjectiveChowPushData D K hZ hX Z.inclusion)
    (restrict : FlatChowPullData D K hU hX U.inclusion 0) (d : ℤ) :
    ProofWanted ((push.map d).range = (restrict.map d).ker ∧ Function.Surjective (restrict.map d)) :=
  excision k D K X hX Z hZ U hU complement push restrict d

private def check_above_dimension (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (a : CycleAtlas X)
    (n : ℕ) (dimension : topologicalKrullDim a.atlas.U.left = (n : ℕ))
    (d : ℤ) (above : (n : ℤ) - a.relativeRank < d) :
    ProofWanted (Subsingleton (ChowGroup D K X hX d)) :=
  above_dimension k D K X hX a n dimension d above

private def check_rational_DM_pushforward (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (X Y : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) (hY : FiniteTypeArtin k Y)
    (f : StackHom X Y) (M : DMProperModel D K hX hY f) :
    DefWanted (RationalPushData D K hX hY f M) := rational_DM_pushforward k D K X Y hX hY f M

end WantedExt.AlgebraicGeometry.StackChowGroupsWanted
