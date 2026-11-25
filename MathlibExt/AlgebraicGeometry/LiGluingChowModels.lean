/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LiGluingGeometryModels

/-!
# Sourced Chow operations on Li's actual matching correspondence

The external product is normalized on every projective/vector-bundle
Kresch representative using its actual product stages and product cut.
The refined Gysin operator uses the intrinsic cone and pulled normal
bundle of the diagonal in the very same matching square. The push is the
native proper DM push attached to that exact Phi, normalized on its Chow
cover. None of these operators or any virtual class is a final input.

`weightedTerm` is the literal m(eta)/|Eq(eta)| times the Phi push of this
diagonal Gysin applied to this external product. The final degeneration
identity uses source-produced virtual classes, in a separate Wanted file.

Source: Jun Li arXiv:math/0110113v1, diagram(3.14), Lemma3.14 and
Theorem3.15, pp39--40. Chow carriers and representative specialization:
Kresch arXiv:math/9810166v1; Manolache arXiv:0805.2065v2, Construction3.6.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LiGluingChowModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open GeneralStackGeometry StackCycleGeometry StackCycleRelations StackFibreModels
open StackVectorBundles StackProjectiveModels StackChowGroups StackBundleCones StackVirtualPullbacks
open LiGluingGeometryModels LiGluingRelativeTypes
open scoped TensorProduct

variable {k : Type} [Field k]
  (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)

section Exterior

variable {L R : Stack (Spec (.of k))} (P : ProductStackModel L R)
  (hL : FiniteTypeArtin k L) (hR : FiniteTypeArtin k R) (hP : FiniteTypeArtin k P.stack)

/-- Literal products of projective stages, bundle stages, and integral cuts. -/
structure ExteriorRepresentative (d e : ℤ)
    (A : ProjectiveStage (scope := FiniteTypeArtin k) L)
    (B : ProjectiveStage (scope := FiniteTypeArtin k) R)
    (E : BundleStage (scope := FiniteTypeArtin k) A.source)
    (F : BundleStage (scope := FiniteTypeArtin k) B.source)
    (Z : IntegralClosedSubstack E.bundle.total (d + E.bundle.rank))
    (Z' : IntegralClosedSubstack F.bundle.total (e + F.bundle.rank)) where
  stage : ProjectiveStage (scope := FiniteTypeArtin k) P.stack
  stageProduct : ProductStackModel A.source B.source
  stageIso : StackEquivalence stage.source stageProduct.stack
  stageLeft : StackVectorBundles.TwoIso
    (Pseudofunctor.StrongTrans.vcomp stageIso.hom
      (Pseudofunctor.StrongTrans.vcomp stageProduct.left A.map))
    (Pseudofunctor.StrongTrans.vcomp stage.map P.left)
  stageRight : StackVectorBundles.TwoIso
    (Pseudofunctor.StrongTrans.vcomp stageIso.hom
      (Pseudofunctor.StrongTrans.vcomp stageProduct.right B.map))
    (Pseudofunctor.StrongTrans.vcomp stage.map P.right)
  bundle : BundleStage (scope := FiniteTypeArtin k) stage.source
  bundleProduct : ProductStackModel E.bundle.total F.bundle.total
  bundleIso : StackEquivalence bundle.bundle.total bundleProduct.stack
  bundleLeft : StackVectorBundles.TwoIso
    (Pseudofunctor.StrongTrans.vcomp bundleIso.hom
      (Pseudofunctor.StrongTrans.vcomp bundleProduct.left E.bundle.projection))
    (Pseudofunctor.StrongTrans.vcomp bundle.bundle.projection
      (Pseudofunctor.StrongTrans.vcomp stageIso.hom stageProduct.left))
  bundleRight : StackVectorBundles.TwoIso
    (Pseudofunctor.StrongTrans.vcomp bundleIso.hom
      (Pseudofunctor.StrongTrans.vcomp bundleProduct.right F.bundle.projection))
    (Pseudofunctor.StrongTrans.vcomp bundle.bundle.projection
      (Pseudofunctor.StrongTrans.vcomp stageIso.hom stageProduct.right))
  rank : bundle.bundle.rank = E.bundle.rank + F.bundle.rank
  cycle : IntegralClosedSubstack bundle.bundle.total ((d + e) + bundle.bundle.rank)
  productCut : ∀ (T : Over (Spec (.of k))) (x : bundle.bundle.total.Fibre T),
    cycle.val.predicate T x ↔
      Z.val.predicate T ((component bundleProduct.left T).obj ((component bundleIso.hom T).obj x)) ∧
      Z'.val.predicate T ((component bundleProduct.right T).obj ((component bundleIso.hom T).obj x))

def ExteriorRepresentative.value {d e : ℤ}
    {A : ProjectiveStage (scope := FiniteTypeArtin k) L}
    {B : ProjectiveStage (scope := FiniteTypeArtin k) R}
    {E : BundleStage (scope := FiniteTypeArtin k) A.source}
    {F : BundleStage (scope := FiniteTypeArtin k) B.source}
    {Z : IntegralClosedSubstack E.bundle.total (d + E.bundle.rank)}
    {Z' : IntegralClosedSubstack F.bundle.total (e + F.bundle.rank)}
    (J : ExteriorRepresentative P d e A B E F Z Z') :
    RationalChowGroup D K P.stack hP (d + e) :=
  (1 : ℚ) ⊗ₜ[ℤ] representative D K P.stack hP (d + e) J.stage J.bundle (cycleClass J.cycle)

structure ExteriorData where
  stage : ∀ (d e : ℤ)
    (A : ProjectiveStage (scope := FiniteTypeArtin k) L)
    (B : ProjectiveStage (scope := FiniteTypeArtin k) R)
    (E : BundleStage (scope := FiniteTypeArtin k) A.source)
    (F : BundleStage (scope := FiniteTypeArtin k) B.source)
    (Z : IntegralClosedSubstack E.bundle.total (d + E.bundle.rank))
    (Z' : IntegralClosedSubstack F.bundle.total (e + F.bundle.rank)),
      ExteriorRepresentative P d e A B E F Z Z'
  product : ∀ d e : ℤ, RationalChowGroup D K L hL d →ₗ[ℚ]
    (RationalChowGroup D K R hR e →ₗ[ℚ] RationalChowGroup D K P.stack hP (d + e))
  normalized : ∀ (d e : ℤ)
    (A : ProjectiveStage (scope := FiniteTypeArtin k) L)
    (B : ProjectiveStage (scope := FiniteTypeArtin k) R)
    (E : BundleStage (scope := FiniteTypeArtin k) A.source)
    (F : BundleStage (scope := FiniteTypeArtin k) B.source)
    (Z : IntegralClosedSubstack E.bundle.total (d + E.bundle.rank))
    (Z' : IntegralClosedSubstack F.bundle.total (e + F.bundle.rank)),
    product d e ((1 : ℚ) ⊗ₜ[ℤ] representative D K L hL d A E (cycleClass Z))
      ((1 : ℚ) ⊗ₜ[ℤ] representative D K R hR e B F (cycleClass Z')) =
      (stage d e A B E F Z Z').value D K P hP

end Exterior

section Correspondence

open ExpandedTargetChainGeometry RelativeProjectiveLineModels ExpandedTargetGluingModels

variable {n n' r g : ℕ} (G : FullType n r) (H : FullType n' r)
  (P Q : RelativePair (k := k)) (W0 : SingularTarget P Q)
  [LocallyOfFiniteType P.target.hom] [LocallyOfFiniteType Q.target.hom]
  [LocallyOfFiniteType W0.scheme.hom]
  [IsNoetherian P.target.left] [IsNoetherian Q.target.left] [IsNoetherian W0.scheme.left]
  (R : ProjectiveLine P.divisor.left (normalLineModule P))
  (R' : ProjectiveLine Q.divisor.left (normalLineModule Q))
  (S : StandardRelativeExpansionModels.StandardSystem P R)
  (S' : StandardRelativeExpansionModels.StandardSystem Q R')
  (beta : Fin G.vertices → StableMapNumericalClasses.NumericalClass P.target.left)
  (gamma : Fin H.vertices → StableMapNumericalClasses.NumericalClass Q.target.left)
  (ML : LiGluingRelativeTypes.ModuliModel P R S G beta)
  (MR : LiGluingRelativeTypes.ModuliModel Q R' S' H gamma)
  (M : MatchingModel G H P Q W0 R R' S S' beta gamma ML MR)
  (hProduct : FiniteTypeArtin k M.product.stack) (hMatching : FiniteTypeArtin k M.square.apex)

structure DiagonalGysinData where
  dimension : ℕ
  pureDimension : PureSchemeRelativeDimension (boundaryPower (r := r) P).hom dimension
  emptyDimension : r = 0 → dimension = 0
  normal : RegularNormalModel M.diagonal dimension
  bundle : VectorBundleStack M.boundary.stack
  rank : bundle.virtualRank = dimension
  normalIso : StackEquivalence bundle.total normal.bundle.total
  overBoundary : StackVectorBundles.TwoIso
    (Pseudofunctor.StrongTrans.vcomp normalIso.hom normal.bundle.projection) bundle.projection
  embedding : ConeEmbedding normal.cone bundle
  targetNormalization : StackVectorBundles.TwoIso
    (Pseudofunctor.StrongTrans.vcomp embedding.map normalIso.hom) normal.comparison.hom
  pulled : BundleStackPullback M.square.snd bundle
  bundleScope : FiniteTypeArtin k pulled.bundle.total
  cone : IntrinsicConeModel M.square.fst
  coneScope : FiniteTypeArtin k cone.total
  baseChange : ConeBaseChangeData M.square.fst M.diagonal M.square.snd M.pairEvaluation cone normal.cone
  sourceEmbedding : ConeEmbedding cone pulled.bundle
  sourceNormalization : StackVectorBundles.TwoIso
    (Pseudofunctor.StrongTrans.vcomp sourceEmbedding.map pulled.map)
    (Pseudofunctor.StrongTrans.vcomp baseChange.map embedding.map)
  recipe : VirtualPullbackRecipe D K hMatching hProduct pulled.bundle bundleScope cone coneScope sourceEmbedding

def DiagonalGysinData.map
    (N : DiagonalGysinData D K G H P Q W0 R R' S S' beta gamma ML MR M hProduct hMatching) (d : ℤ) :
    RationalChowGroup D K M.product.stack hProduct d →ₗ[ℚ]
      RationalChowGroup D K M.square.apex hMatching (d - N.dimension) :=
  (rationalMap (chowRegrade D K M.square.apex hMatching
    (by rw [N.pulled.rank_eq, N.rank]))).comp (virtualPullback N.recipe d)

variable (W : LiExpandedDegenerationModels.OneParameter P Q W0)
  (WS : LiExpandedDegenerationModels.StandardSystem W)
  (total : StableMapNumericalClasses.NumericalClass W0.scheme.left)
  (eta : AdmissibleTriple (g := g) G H P Q W0 beta gamma total)
  (MC : LiExpandedCentralModels.ModuliModel W WS (n + n') g total)
  (Phi : GluingModel G H P Q W0 R R' S S' beta gamma ML MR W WS total eta MC M)

structure ChowOperations where
  productScope : FiniteTypeArtin k M.product.stack
  matchingScope : FiniteTypeArtin k M.square.apex
  exterior : ExteriorData D K M.product ML.finiteType MR.finiteType productScope
  diagonal : DiagonalGysinData D K G H P Q W0 R R' S S' beta gamma ML MR M productScope matchingScope
  proper : DMProperModel D K matchingScope MC.finiteType Phi.phi
  push : RationalPushData D K matchingScope MC.finiteType Phi.phi proper

def weightedTerm
    (V : ChowOperations D K G H P Q W0 R R' S S' beta gamma ML MR M W WS total eta MC Phi)
    (d e : ℤ) (a : RationalChowGroup D K ML.stack ML.finiteType d)
    (b : RationalChowGroup D K MR.stack MR.finiteType e) :
    RationalChowGroup D K MC.stack MC.finiteType (d + e - V.diagonal.dimension) :=
  coefficient G beta H gamma • V.push.map (d + e - V.diagonal.dimension)
    (V.diagonal.map D K G H P Q W0 R R' S S' beta gamma ML MR M V.productScope V.matchingScope (d + e)
      (V.exterior.product d e a b))

end Correspondence

end MathlibExt.AlgebraicGeometry.LiGluingChowModels
