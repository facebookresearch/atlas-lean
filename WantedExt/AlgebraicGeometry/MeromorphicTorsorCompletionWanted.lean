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
public import MathlibExt.AlgebraicGeometry.MeromorphicTorsorCompletionGenericRefinementComp
public import MathlibExt.AlgebraicGeometry.MeromorphicTorsorCompletionGenericRefinementIdentity

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

/-- Algebraization of an integral frame: for a prime $p$, a reductive group scheme $G$ over a field
$E$ with torsor descent `H` and pullback preservation `P` on $E$-spaces, a map $d : D \to X$ of
$E$-spaces with a puncture `U`, a pole chart `Q` at `U` whose whole chart is strongly Noetherian, an
algebraization `A` of $G$-bundles on `Q`, a $G$-bundle $N$ on $X$ and an integral frame `f` of $N$
over `Q`: an isomorphism from the algebraized torsor of $N$ restricted to `Q` (over the spectrum of
the chart's coefficient ring) to the trivial torsor, which on every analytic test of `Q` agrees with
`f` through the comparison of `A`. -/
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

/-- The completed meromorphic comparison: for a prime $p$, a reductive group scheme $G$ over a field
$E$ with torsor descent `H` and pullback preservation `P` on $E$-spaces, a map $d : D \to X$ of
$E$-spaces with a puncture `U`, a pole chart `Q` at `U` whose whole chart is strongly Noetherian, an
algebraization `A` on `Q`, the fpqc torsor condition `B` along its completion, source frames `F`,
the condition `h` that the chart parameter is a unit on the puncture, and injectivity of the map
from the meromorphic ring of `Q` to sections on the puncture: a completion comparison
(`CompletionComparison`), that is, an identification of the finite-pole torsors of the two legs of
every meromorphic Hecke modification, agreeing with the original punctured isomorphism on every test
and point, whose completion acts on framed sections by multiplication by the completed $G$-point of
the modification. -/
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

/-- Coefficient maps of a pole-chart refinement: for a prime $p$, a field $E$, a map $d : D \to X$
of $E$-spaces with a puncture `U` and a refinement $r$ of a pole chart `Q` by a pole chart `Q'` at
`U`, the coefficient map of $r$ sends each power of the divisor ideal of `Q` into the same power of
that of `Q'`, the induced maps of finite quotients are compatible, and the image of the formal
parameter of `Q` in the localized completed ring of `Q'` is a unit (`CoefficientRefinement`). -/
public def_wanted sourceRefinementCoefficients (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] {X D : ESpace p E}
    (d : D ⟶ X) (U : Puncture p E d) (Q Q' : PoleChart p E d U)
    (r : PoleRefinement p E d U Q Q') : CoefficientRefinement p E d U Q Q' r

/-- Refinement of an integral frame: for a prime $p$, a group scheme $G$ over a field $E$ with
torsor descent `H`, a map $d : D \to X$ of $E$-spaces with a puncture `U`, a refinement $r$ of a
pole chart `Q` by a pole chart `Q'` at `U`, a $G$-bundle $N$ on $X$ and an integral frame `f` of $N$
over `Q`: an integral frame of $N$ over `Q'` whose value on every test of `Q'` is the value of `f`
on the same test regarded over `Q` through $r$. -/
public def_wanted refineIntegralFrame (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] (G : Over (Spec (.of E))) [GrpObj G]
    (H : ∀ V : ESpace p E, GroupDescent p E G V)
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q Q' : PoleChart p E d U) (r : PoleRefinement p E d U Q Q')
    (N : Bundles p E G H X) (f : IntegralFrame p E G H d U Q N) :
    RefinedFrame p E d U Q Q' r G H N f

/-- Restriction square for formal torsors: for a prime $p$, a field $E$, a map $d : D \to X$ of
$E$-spaces with a puncture `U` and a refinement $r$ of a pole chart `Q` by `Q'` with coefficient
refinement `R`, and a group scheme $G$ over $E$ whose torsors are preserved by fpqc pullback along
the completed coefficient map of $r$: a natural isomorphism between restricting a formal $G$-torsor
of `Q` to its generic part and then pulling back to the generic part of `Q'`, and reindexing it to
`Q'` and then restricting, whose underlying sheaf maps are the canonical pullback-composition
isomorphisms (`restrictionSheafSquare`). -/
public def_wanted nativeRestrictionSquare (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] {X D : ESpace p E}
    (d : D ⟶ X) (U : Puncture p E d) (Q Q' : PoleChart p E d U)
    (r : PoleRefinement p E d U Q Q') (R : CoefficientRefinement p E d U Q Q' r)
    (G : Over (Spec (.of E))) [GrpObj G]
    (V : FpqcPreservesTorsors E G (positiveSchemeMap p E d U Q Q' r R)) :
    RestrictionSquare p E d U Q Q' r R G V

/-- Refinement of completed torsors: for a prime $p$, a reductive group scheme $G$ over a field $E$
with torsor descent `H` and pullback preservation `P` on $E$-spaces, a map $d : D \to X$ of
$E$-spaces with a puncture `U`, a refinement $r$ of a pole chart `Q` by `Q'` (both with strongly
Noetherian whole charts) with coefficient refinement `R` and the fpqc torsor condition `V` along its
completed coefficient map, algebraizations `A`, `A'`, fpqc torsor conditions `B`, `B'` along the
completions and source frames `F`, `F'` on `Q` and `Q'`: an isomorphism between the completed
torsors of `Q` reindexed to `Q'` and the completed torsors of `Q'`, compatible with the refinement
of the algebraizations and with the completion squares, that carries the pulled-back formal frames
given by `F` to the formal frames given by `F'` of the refined integral frames. -/
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

/-- Refinement of local Hecke data: for a prime $p$, a reductive group scheme $G$ over a field $E$
with torsor descent `H` and pullback preservation `P` on $E$-spaces, a map $d : D \to X$ of
$E$-spaces with a puncture `U`, a refinement $r$ of a pole chart `Q` by `Q'` (both with strongly
Noetherian whole charts) with coefficient refinement `R`, fpqc torsor condition `V` and restriction
square `S`, algebraizations, fpqc torsor conditions and source frames on both charts, a completion
refinement `T`, the conditions `h`, `h'` that the chart parameters are units on the punctures,
injectivity of both punctured maps, and completion comparisons `C`, `C'`: an isomorphism between the
local Hecke datum of each meromorphic modification computed on `Q` and reindexed to `Q'` and the one
computed on `Q'`, whose left and right legs are the comparison maps of `T`. -/
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

/-- The identity refinement induces the identity of completed rings: for a prime $p$, a field $E$, a
map $d : D \to X$ of $E$-spaces with a puncture `U` and a pole chart `Q` at `U`, a refinement $r$ of
`Q` by itself whose map of chart spaces is the identity, and a coefficient refinement `R` for $r$,
the induced map of the completion of the chart's coefficient ring along the divisor (`positiveMap`)
is the identity. -/
public theorem_wanted positiveRefinement_identity (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] {X D : ESpace p E}
    (d : D ⟶ X) (U : Puncture p E d) (Q : PoleChart p E d U)
    (r : PoleRefinement p E d U Q Q) (hr : r.map = 𝟙 Q.space)
    (R : CoefficientRefinement p E d U Q Q r) :
    positiveMap p E d U Q Q r R.powers R.finite = RingHom.id _

/-- Refinement maps of completed rings compose: for a prime $p$, a field $E$, a map $d : D \to X$ of
$E$-spaces with a puncture `U` and refinements $r$ of a pole chart `Q` by `Q'`, $s$ of `Q'` by `Q''`
and $t$ of `Q` by `Q''` whose maps of chart spaces satisfy $t = r \circ s$, and coefficient
refinements `R`, `S`, `T` for them, the induced map of completed chart rings (`positiveMap`) for $t$
is the one for $r$ followed by the one for $s$. -/
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

end WantedExt.AlgebraicGeometry.MeromorphicTorsorCompletion
