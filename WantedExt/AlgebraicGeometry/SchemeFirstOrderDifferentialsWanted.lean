/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SchemeFirstOrderDifferentials
public import Batteries.Util.ProofWanted

/-!
# Source normalized first-order cotangent-class construction requests

Each point class is computed from the actual dual-number coefficient,
the polynomial-resolution cotangent projection, and native H0 counits.
The chain rule compares actual composed point maps with cotangent
precomposition. No pointed-set equivalence replaces this class map.
References: Behrend–Fantechi alg-geom/9601010v1, §4;
Graber–Harris–Starr math/0109220v1, §2; Stacks, Tags 08S3/08UX.
-/

@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.SchemeFirstOrderDifferentials

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.BirationalDualityReferences
open MathlibExt.AlgebraicGeometry.GlobalPerfectObstructionTheory
open MathlibExt.AlgebraicGeometry.MarkedMapDeformationCones
open MathlibExt.AlgebraicGeometry.MarkedFirstOrderFamilies
open MathlibExt.AlgebraicGeometry.ModuleDerivedSquares
attribute [local instance] HasDerivedCategory.standard

variable [HasDerivedPullbacks.{0}] [HasDerivedPushforwards.{0}] [HasDerivedTensors.{0}]

/-- **A cotangent complex with a projection to Kähler one-forms.** Assume that derived pullbacks,
pushforwards and tensor products exist (`HasDerivedPullbacks`, `HasDerivedPushforwards`,
`HasDerivedTensors`). For a commutative ring $k$ and a $k$-scheme $U$: a cotangent normalization $P$
of $U \to \operatorname{Spec} k$ (a complex of $\mathcal{O}_U$-modules with, on every affine chart,
a polynomial resolution and a quasi-isomorphism from its cotangent complex to the sections of $P$,
compatible with refinements of charts), together with a map from $P$ to $\Omega^1_{U/k}$ placed in
degree $0$ that sends, on every affine chart, the degree-zero cotangent differential of each element
$x$ of the resolution to the Kähler differential of the image of $x$. Such a projection need not
exist for an arbitrary representative of the cotangent complex: on $\operatorname{Spec} k[t]$ the
quasi-isomorphic model $[k[t] \to k[t]/(t)]$ (degrees $0$ and $1$, receiving $dt \mapsto t$) has no
$k[t]$-linear map back sending $t$ to $dt$. -/
def_wanted normalizedCotangentFormsProjection (k : Type) [CommRing k]
    (U : Over (Spec (.of k))) :
    (P : CotangentNormalization U.hom) × CotangentFormsProjection U P

def_wanted normalizedPullbackH0 {X Y : Scheme.{0}} (f : X ⟶ Y) (M : Y.Modules) : PullbackH0 f M

def_wanted normalizedH0Projection {X : Scheme.{0}} (K : D X) [K.IsLE 0] : H0Projection K

def_wanted normalizedPointCotangentH0 (k : Type) [CommRing k]
    (U : Over (Spec (.of k))) (P : CotangentNormalization U.hom)
    (F : CotangentFormsProjection U P) (Ω : Type) [Field Ω] (p : Spec (.of Ω) ⟶ U.left) :
    PointCotangentH0 U P p F

def_wanted actualPointDifferential (k : Type) [CommRing k]
    (U : Over (Spec (.of k))) (Ω : Type) [Field Ω] (p : Spec (.of Ω) ⟶ U.left)
    (b : Spec (.of Ω) ⟶ Spec (.of k)) (hp : p ≫ U.hom = b) (D : PointDeformation p hp) :
    PointDifferential U p hp D

theorem_wanted actualPointClassChainRule (k : Type) [CommRing k]
    (U V : Over (Spec (.of k))) (f : U ⟶ V)
    (P : CotangentNormalization U.hom) (Q : CotangentNormalization V.hom)
    (F : CotangentFormsProjection U P) (G : CotangentFormsProjection V Q)
    (D : RelativeDifferential f.left (Over.w f) P Q)
    (Ω : Type) [Field Ω] (p : Spec (.of Ω) ⟶ U.left)
    (b : Spec (.of Ω) ⟶ Spec (.of k)) (hp : p ≫ U.hom = b)
    (A : PullbackPasting p f.left)
    (H : PointCotangentH0 U P p F) (K : PointCotangentH0 V Q (p ≫ f.left) G)
    (HP : H0Projection (pointCotangent U P p)) (HQ : H0Projection (pointCotangent V Q (p ≫ f.left)))
    (δ : PointDeformation p hp) (E : PointDifferential U p hp δ)
    (E' : PointDifferential V (p ≫ f.left) _ (composePoint U p f δ)) :
    pointClass V Q (p ≫ f.left) K HQ E' =
      mapPointClass U P p f Q D A (pointClass U P p H HP E)

end MathlibExt.AlgebraicGeometry.SchemeFirstOrderDifferentials
