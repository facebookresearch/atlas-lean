/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeWittIndRealizations
public import MathlibExt.AlgebraicGeometry.RelativeWittLoopCorrespondences
public import MathlibExt.AlgebraicGeometry.ReductiveGroupSchemeModels
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Native ind-perfect geometry of the original reductive Witt quotient

Finite stages are actual etale-presented algebraic spaces, with genuine
ordinary proper models and universal perfect realizations. Every
transition is an actual structural-compatible sheaf map and is a closed
immersion on every scheme pullback. The point diagram is computed from
these native maps. The realization target is the original fpqc `LG/L+G`.

Convolution uses the original twofold twisted quotient and its native
group-product map. All finite-stage maps and their transition squares
are retained, and the colimit insertions fix the original multiplication.
The finite-stage maps go between perfect spaces, which are not of finite
type, so they are not required to be proper: each is the perfection of a
proper map of the ordinary models, checked on actual representing scheme
fibres (Zhu, Appendix A, Definition A.18 and Lemma A.19: perfect
properness is properness of a deperfection).

Source: Zhu, arXiv:1407.8519v3, Theorem 1.4, p. 9, and
Section 1.4, pp. 18--20. Constructing this general reductive geometry is
a separate Wanted endpoint; no Satake equivalence is assumed here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeWittGroupIndModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.EtaleSpacePresentations
open RelativeWittLoopTests RelativeWittSpaceStages RelativeWittIndRealizations

variable (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k]

/-- One actual perfect space with its separate ordinary proper deperfection. -/
structure SpaceStage where
  ordinary : Space k
  proper : ProperModel k ordinary
  perfection : Perfection p k ordinary

/-- Actual increasing closed maps between the original perfect space stages. -/
structure IncreasingStages where
  stage : ℕ → SpaceStage p k
  transition : ∀ {N M : ℕ}, N ≤ M →
    SpaceMap k (stage N).perfection.space (stage M).perfection.space
  identity : ∀ N, transition (le_refl N) = 𝟙 _
  composition : ∀ {N M L : ℕ} (h : N ≤ M) (j : M ≤ L),
    transition (h.trans j) = transition h ≫ transition j
  closed : ∀ {N M : ℕ} (h : N ≤ M), IsClosedSpaceMap k (transition h)

variable {p k}

/-- Point maps are induced by the actual etale-quotient stage transitions. -/
def IncreasingStages.pointsDiagram (S : IncreasingStages p k) :
    ℕ ⥤ (PerfectAlgebra p k ⥤ Type 1) where
  obj N := spacePoints p k (S.stage N).perfection.space
  map f := spacePointMap p k (S.transition (leOfHom f))
  map_id N := by
    rw [S.identity]
    apply NatTrans.ext
    funext R
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    rfl
  map_comp f g := by
    have h := S.composition (leOfHom f) (leOfHom g)
    rw [h]
    apply NatTrans.ext
    funext R
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    rfl

/-- The sheaf diagram is the actual fpqc sheafification of those original points. -/
def IncreasingStages.sheafDiagram (S : IncreasingStages p k) :=
  S.pointsDiagram ⋙ sheafification p k

variable (p k)

/-- An actual native sheaf is represented by the original increasing space diagram. -/
structure QuotientRealization (F : Sheaf (fpqcTopology p k) (Type 1)) where
  stages : IncreasingStages p k
  comparison : colimit stages.sheafDiagram ≅ F

variable (B : Type) [CommRing B] [Algebra (WittVector p k) B] (pi : B)
  (G : Over (Spec (.of B))) [GrpObj G]

/-- The target is literally the original relative Witt positive-loop quotient. -/
abbrev GrassmannianGeometry := QuotientRealization p k
  (RelativeWittLoopCorrespondences.grassmannian p k B pi G)

/-- The twofold geometry targets precisely the original twisted quotient. -/
abbrev TwistedProductGeometry := QuotientRealization p k
  (RelativeWittLoopCorrespondences.convolution p k B pi G)

/-- Properness is on every actual representing scheme fibre of a space map. This is ordinary
properness, so it is meant for maps of the ordinary (finite-type) models. -/
def IsProperSpaceMap {A C : Space k} (f : SpaceMap k A C) : Prop :=
  ∀ (V : Scheme) (y : represented.obj V ⟶ C.sheaf),
    ∃ F : SchemeFibre k f V y, IsProper F.scheme.hom

/-- Native finite-stage convolution, pinned to the original group-product map. Each map of
perfect stages is the perfection of a proper map of the ordinary models: it lies over that
ordinary map along the two perfection projections. -/
structure ConvolutionGeometry (M : GrassmannianGeometry p k B pi G) where
  geometry : TwistedProductGeometry p k B pi G
  targetStage : ℕ →o ℕ
  maps : ∀ N : ℕ, SpaceMap k (geometry.stages.stage N).perfection.space
    (M.stages.stage (targetStage N)).perfection.space
  ordinaryMaps : ∀ N : ℕ, SpaceMap k (geometry.stages.stage N).ordinary
    (M.stages.stage (targetStage N)).ordinary
  ordinary_proper : ∀ N, IsProperSpaceMap k (ordinaryMaps N)
  perfection_square : ∀ N, maps N ≫ (M.stages.stage (targetStage N)).perfection.projection =
    (geometry.stages.stage N).perfection.projection ≫ ordinaryMaps N
  naturality : ∀ {N L : ℕ} (h : N ≤ L),
    geometry.stages.transition h ≫ maps L =
      maps N ≫ M.stages.transition (targetStage.monotone h)
  normalized : ∀ N : ℕ,
    colimit.ι geometry.stages.sheafDiagram N ≫ geometry.comparison.hom ≫
      RelativeWittLoopCorrespondences.convolutionMap p k B pi G =
        (sheafification p k).map (spacePointMap p k (maps N)) ≫
          colimit.ι M.stages.sheafDiagram (targetStage N) ≫ M.comparison.hom

end MathlibExt.AlgebraicGeometry.RelativeWittGroupIndModels
