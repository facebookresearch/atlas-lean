/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NumericalCompactifiedJacobians
public import MathlibExt.AlgebraicGeometry.SheafTensorSections
public import Mathlib.CategoryTheory.Monoidal.Mod

/-!
# Actual reduced-curve Picard tensor action

Tensoring uses the actual universal torsion-free sheaf and the actual
Picard-zero universal line. The action map is the unique parameter map
of this tensor family into the fine compactified Jacobian. Family
comparisons over every test scheme are computed from one global family
isomorphism by native pullback composition and tensor comparisons.

No O_C point of the compactified Jacobian is required, and the connected
Picard-zero group is kept separate from the whole line-bundle locus.
Source: MRV arXiv:1207.7233v5, Introduction and Section 5, pp2 and18--19.
The imported source/sheaf/curve and native tensor/pullback notices retain
their Mathlib/Stacks revision, original authorship and Apache attribution.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ReducedPicardTensorActions

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open CoherentCurveLinearSeries AlgebraicLineBundleFamilies PointedPicardFamilies
open NumericalCompactifiedJacobians SheafTensorSections NativeTensorComparisons

variable {k : Type} [Field k] [IsAlgClosed k]

/-- Local planar singularities are genuine local embeddings in smooth surfaces. -/
structure PlanarNeighborhood (C : Over (Spec (.of k))) (c : C.left) where
  openSet : C.left.Opens
  contains : c ∈ openSet
  surface : Over (Spec (.of k))
  smooth : SmoothOfRelativeDimension 2 surface.hom
  embedding : openSet.toScheme ⟶ surface.left
  closed : IsClosedImmersion embedding
  over : embedding ≫ surface.hom = openSet.ι ≫ C.hom

def IsLocallyPlanar (C : Over (Spec (.of k))) : Prop :=
  ∀ c : C.left, Nonempty (PlanarNeighborhood C c)

variable (C : Over (Spec (.of k))) [IsProperCurve C.hom] [TorsionFreeRestrictions C.left]
  (q : Polarization C.left) (s : SmoothMarking C)
  (M : FineCompactifiedJacobian C q s) (J : PicardZeroModel C s.p)

abbrev actionBase := J.J ⊗ M.J

def tensorFamily (T : Over (Spec (.of k))) (f : T ⟶ M.J) (g : T ⟶ J.J) :
    (prod C T).left.Modules :=
  moduleTensor (prod C T).left (familyPullback C M.J T M.F f) (familyPullback C J.J T J.P g)

def universalTensorFamily : (prod C (actionBase C q s M J)).left.Modules :=
  tensorFamily C q s M J (actionBase C q s M J) (CartesianMonoidalCategory.snd J.J M.J)
    (CartesianMonoidalCategory.fst J.J M.J)

/-- Preservation and finite-presentation data for this exact tensor family. -/
structure TensorAdmissibility : Prop where
  [finiteType : LocallyOfFiniteType (actionBase C q s M J).hom]
  [quasiCompact : QuasiCompact (actionBase C q s M J).hom]
  stable : IsStableFamily C (actionBase C q s M J) q (universalTensorFamily C q s M J)
  normalized : IsNormalized C (actionBase C q s M J) s.p (universalTensorFamily C q s M J)

def tensorAction (A : TensorAdmissibility C q s M J) : actionBase C q s M J ⟶ M.J :=
  (@M.universal (actionBase C q s M J) A.finiteType A.quasiCompact
    (universalTensorFamily C q s M J) A.stable A.normalized).choose

def universalTensorIso (A : TensorAdmissibility C q s M J) :
    familyPullback C M.J (actionBase C q s M J) M.F (tensorAction C q s M J A) ≅
      universalTensorFamily C q s M J :=
  Classical.choice (@M.universal (actionBase C q s M J) A.finiteType A.quasiCompact
    (universalTensorFamily C q s M J) A.stable A.normalized).choose_spec.1

def familyCompositionIso (Y T U : Over (Spec (.of k))) (F : (prod C Y).left.Modules)
    (f : T ⟶ U) (g : U ⟶ Y) :
    (Scheme.Modules.pullback (prod.map (𝟙 C) f).left).obj (familyPullback C Y U F g) ≅
      familyPullback C Y T F (f ≫ g) :=
  (Scheme.Modules.pullbackComp (prod.map (𝟙 C) f).left
    (prod.map (𝟙 C) g).left).app F ≪≫
      (Scheme.Modules.pullbackCongr (by
        change (prod.map (𝟙 C) f).left ≫ (prod.map (𝟙 C) g).left =
          (prod.map (𝟙 C) (f ≫ g)).left
        rw [← Over.comp_left]
        congr 1
        ext <;> simp)).app F

/-- The group law is attached to the unique actual tensor parameter map. -/
structure PicardTensorAction where
  admissible : TensorAdmissibility C q s M J
  action : letI := J.group; ModObj J.J M.J
  action_eq : letI := J.group; letI := action;
    γ[J.J,M.J] = tensorAction C q s M J admissible
  tensorPullback : ∀ (T : Over (Spec (.of k))) (f : T ⟶ actionBase C q s M J),
    TensorPullbackComparison (prod.map (𝟙 C) f).left

/-- All-scheme comparisons are the pullbacks of the same universal tensor iso. -/
def pointFamilyIso (A : PicardTensorAction C q s M J) (T : Over (Spec (.of k)))
    (f : T ⟶ M.J) (g : T ⟶ J.J) :
    familyPullback C M.J T M.F
      (CartesianMonoidalCategory.lift g f ≫ tensorAction C q s M J A.admissible) ≅
        tensorFamily C q s M J T f g := by
  let h : T ⟶ actionBase C q s M J := CartesianMonoidalCategory.lift g f
  exact (familyCompositionIso C M.J T (actionBase C q s M J) M.F h
      (tensorAction C q s M J A.admissible)).symm ≪≫
    (Scheme.Modules.pullback (prod.map (𝟙 C) h).left).mapIso
      (universalTensorIso C q s M J A.admissible) ≪≫
    (A.tensorPullback T h).iso
      (familyPullback C M.J (actionBase C q s M J) M.F (CartesianMonoidalCategory.snd J.J M.J))
      (familyPullback C J.J (actionBase C q s M J) J.P (CartesianMonoidalCategory.fst J.J M.J)) ≪≫
    NativeTensorComparisons.tensorIso
      (familyCompositionIso C M.J T (actionBase C q s M J) M.F h
          (CartesianMonoidalCategory.snd J.J M.J) ≪≫
        eqToIso (by simp [h]))
      (familyCompositionIso C J.J T (actionBase C q s M J) J.P h
          (CartesianMonoidalCategory.fst J.J M.J) ≪≫
        eqToIso (by simp [h]))

end MathlibExt.AlgebraicGeometry.ReducedPicardTensorActions
