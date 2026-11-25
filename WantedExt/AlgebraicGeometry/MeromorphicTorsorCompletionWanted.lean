/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.MeromorphicCompletionRefinements
public import MathlibExt.AlgebraicGeometry.ReductiveGroupSchemeModels
public import MathlibExt.AlgebraicGeometry.AnalyticProObjectSites

/-!
# Source constructions for actual meromorphic torsor completion

These outputs construct original all-test algebraized frames and the
punctured comparison on the computed completed torsors. Strong
noetherianity is imposed on the actual whole pole chart; reductivity
retains native affine, finite-presentation, smooth and geometric
connectedness hypotheses. Refinement uses actual source maps, every
finite quotient and native fpqc pullback.

No desired Hecke equivalence, v-stack assertion or classification is
requested or assumed here. Source: Fargues--Scholze,
arXiv:2102.13459v4, Sections III.3 and VI.1; Beauville--Laszlo descent.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MeromorphicTorsorCompletion

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open AnalyticGroupTorsorSites AnalyticBundlePrestackModels AnalyticBundleModifications
open AnalyticMeromorphicCoordinates MeromorphicHeckeModels AffinoidTorsorAlgebraizationModels
open CompletedTorsorSourceFrames MeromorphicCompletionRefinements AnalyticProObjectSites
open MeromorphicCoefficientCompletion

/-- Algebraize every original frame through the all-test source comparison. -/
public def_wanted algebraizedIntegralFrame (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] (G : Over (Spec (.of E))) [GrpObj G]
    [ReductiveGroupSchemeModels.IsReductive (Spec (.of E)) G]
    (H : ∀ V : ESpace p E, GroupDescent p E G V)
    (P : PullbackPreservation p E G H)
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q : PoleChart p E d U)
    (hQ : IsStronglyNoetherian p (wholePoleChart p E d U Q).pair)
    (A : Algebraization p E G H Q.space)
    (N : Bundles p E G H X) (f : IntegralFrame p E G H d U Q N) :
    AlgebraizedFrame p E G H P d U Q A N f

/-- Construct the all-test punctured comparison on the actual computed torsor legs. -/
public def_wanted completedMeromorphicComparison (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] (G : Over (Spec (.of E))) [GrpObj G]
    [ReductiveGroupSchemeModels.IsReductive (Spec (.of E)) G]
    (H : ∀ V : ESpace p E, GroupDescent p E G V)
    (P : PullbackPreservation p E G H)
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q : PoleChart p E d U)
    (hQ : IsStronglyNoetherian p (wholePoleChart p E d U Q).pair)
    (A : Algebraization p E G H Q.space)
    (B : FpqcPreservesTorsors E G (completionBaseMap p E d U Q))
    (F : MathlibExt.AlgebraicGeometry.MeromorphicTorsorCompletion.SourceFrames
      p E G H P d U Q A)
    (h : IsUnit (sectionMap p E Q.puncture.map Q.parameter))
    (hi : Function.Injective (puncturedMap p E d U Q h)) :
    MathlibExt.AlgebraicGeometry.MeromorphicTorsorCompletion.CompletionComparison
      p E G H P d U Q A B F h

/-- Prove compatibility of the fixed finite quotient maps and actual localized parameter. -/
public def_wanted sourceRefinementCoefficients (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] {X D : ESpace p E}
    (d : D ⟶ X) (U : Puncture p E d) (Q Q' : PoleChart p E d U)
    (r : PoleRefinement p E d U Q Q') : CoefficientRefinement p E d U Q Q' r

/-- Refine each original integral frame, fixing all actual test points. -/
public def_wanted refineIntegralFrame (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] (G : Over (Spec (.of E))) [GrpObj G]
    (H : ∀ V : ESpace p E, GroupDescent p E G V)
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q Q' : PoleChart p E d U) (r : PoleRefinement p E d U Q Q')
    (N : Bundles p E G H X) (f : IntegralFrame p E G H d U Q N) :
    RefinedFrame p E d U Q Q' r G H N f

/-- Equip the original native sheaf composition square with its actual equivariant action. -/
public def_wanted nativeRestrictionSquare (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] {X D : ESpace p E}
    (d : D ⟶ X) (U : Puncture p E d) (Q Q' : PoleChart p E d U)
    (r : PoleRefinement p E d U Q Q') (R : CoefficientRefinement p E d U Q Q' r)
    (G : Over (Spec (.of E))) [GrpObj G]
    (V : FpqcPreservesTorsors E G (positiveSchemeMap p E d U Q Q' r R)) :
    RestrictionSquare p E d U Q Q' r R G V

/-- Construct unframed base change on the original completed torsors and all source frames. -/
public def_wanted completionRefinement (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] (G : Over (Spec (.of E))) [GrpObj G]
    [ReductiveGroupSchemeModels.IsReductive (Spec (.of E)) G]
    (H : ∀ V : ESpace p E, GroupDescent p E G V)
    (P : PullbackPreservation p E G H)
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q Q' : PoleChart p E d U)
    (hQ : IsStronglyNoetherian p (wholePoleChart p E d U Q).pair)
    (hQ' : IsStronglyNoetherian p (wholePoleChart p E d U Q').pair)
    (r : PoleRefinement p E d U Q Q') (R : CoefficientRefinement p E d U Q Q' r)
    (V : FpqcPreservesTorsors E G (positiveSchemeMap p E d U Q Q' r R))
    (A : Algebraization p E G H Q.space)
    (B : FpqcPreservesTorsors E G (completionBaseMap p E d U Q))
    (A' : Algebraization p E G H Q'.space)
    (B' : FpqcPreservesTorsors E G (completionBaseMap p E d U Q'))
    (F : MathlibExt.AlgebraicGeometry.MeromorphicTorsorCompletion.SourceFrames
      p E G H P d U Q A)
    (F' : MathlibExt.AlgebraicGeometry.MeromorphicTorsorCompletion.SourceFrames
      p E G H P d U Q' A') :
    CompletionRefinement p E d U Q Q' r R G H P V A B A' B' F F'

/-- Compare actual Hecke refinements, fixing both native unframed torsor maps. -/
public def_wanted meromorphicHeckeRefinement (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] (G : Over (Spec (.of E))) [GrpObj G]
    [ReductiveGroupSchemeModels.IsReductive (Spec (.of E)) G]
    (H : ∀ V : ESpace p E, GroupDescent p E G V)
    (P : PullbackPreservation p E G H)
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q Q' : PoleChart p E d U)
    (hQ : IsStronglyNoetherian p (wholePoleChart p E d U Q).pair)
    (hQ' : IsStronglyNoetherian p (wholePoleChart p E d U Q').pair)
    (r : PoleRefinement p E d U Q Q') (R : CoefficientRefinement p E d U Q Q' r)
    (V : FpqcPreservesTorsors E G (positiveSchemeMap p E d U Q Q' r R))
    (S : RestrictionSquare p E d U Q Q' r R G V)
    (A : Algebraization p E G H Q.space)
    (B : FpqcPreservesTorsors E G (completionBaseMap p E d U Q))
    (A' : Algebraization p E G H Q'.space)
    (B' : FpqcPreservesTorsors E G (completionBaseMap p E d U Q'))
    (F : MathlibExt.AlgebraicGeometry.MeromorphicTorsorCompletion.SourceFrames
      p E G H P d U Q A)
    (F' : MathlibExt.AlgebraicGeometry.MeromorphicTorsorCompletion.SourceFrames
      p E G H P d U Q' A')
    (T : CompletionRefinement p E d U Q Q' r R G H P V A B A' B' F F')
    (h : IsUnit (sectionMap p E Q.puncture.map Q.parameter))
    (h' : IsUnit (sectionMap p E Q'.puncture.map Q'.parameter))
    (hi : Function.Injective (puncturedMap p E d U Q h))
    (hi' : Function.Injective (puncturedMap p E d U Q' h'))
    (C : MathlibExt.AlgebraicGeometry.MeromorphicTorsorCompletion.CompletionComparison
      p E G H P d U Q A B F h)
    (C' : MathlibExt.AlgebraicGeometry.MeromorphicTorsorCompletion.CompletionComparison
      p E G H P d U Q' A' B' F' h') :
    HeckeRefinement p E d U Q Q' r R G H P V S A B A' B' F F' T h h' C C'

/-- The identity source coefficient map gives the identity completed map at every stage. -/
public theorem_wanted positiveRefinement_identity (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] {X D : ESpace p E}
    (d : D ⟶ X) (U : Puncture p E d) (Q : PoleChart p E d U)
    (r : PoleRefinement p E d U Q Q) (hr : r.map = 𝟙 Q.space)
    (R : CoefficientRefinement p E d U Q Q r) :
    positiveMap p E d U Q Q r R.powers R.finite = RingHom.id _

/-- Composition uses exactly the original two analytic coefficient maps at every stage. -/
public theorem_wanted positiveRefinement_comp (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] {X D : ESpace p E}
    (d : D ⟶ X) (U : Puncture p E d) (Q Q' Q'' : PoleChart p E d U)
    (r : PoleRefinement p E d U Q Q') (s : PoleRefinement p E d U Q' Q'')
    (t : PoleRefinement p E d U Q Q'') (ht : t.map = s.map ≫ r.map)
    (R : CoefficientRefinement p E d U Q Q' r)
    (S : CoefficientRefinement p E d U Q' Q'' s)
    (T : CoefficientRefinement p E d U Q Q'' t) :
    positiveMap p E d U Q Q'' t T.powers T.finite =
      (positiveMap p E d U Q' Q'' s S.powers S.finite).comp
        (positiveMap p E d U Q Q' r R.powers R.finite)

/-- Generic units use the same actual original identity coefficient map. -/
public theorem_wanted genericRefinement_identity (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] {X D : ESpace p E}
    (d : D ⟶ X) (U : Puncture p E d) (Q : PoleChart p E d U)
    (r : PoleRefinement p E d U Q Q) (hr : r.map = 𝟙 Q.space)
    (R : CoefficientRefinement p E d U Q Q r) :
    genericMap p E d U Q Q r R = RingHom.id _

/-- Generic composition is the localization of the actual completed source composition. -/
public theorem_wanted genericRefinement_comp (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] {X D : ESpace p E}
    (d : D ⟶ X) (U : Puncture p E d) (Q Q' Q'' : PoleChart p E d U)
    (r : PoleRefinement p E d U Q Q') (s : PoleRefinement p E d U Q' Q'')
    (t : PoleRefinement p E d U Q Q'') (ht : t.map = s.map ≫ r.map)
    (R : CoefficientRefinement p E d U Q Q' r)
    (S : CoefficientRefinement p E d U Q' Q'' s)
    (T : CoefficientRefinement p E d U Q Q'' t) :
    genericMap p E d U Q Q'' t T =
      (genericMap p E d U Q' Q'' s S).comp (genericMap p E d U Q Q' r R)

end WantedExt.AlgebraicGeometry.MeromorphicTorsorCompletion
