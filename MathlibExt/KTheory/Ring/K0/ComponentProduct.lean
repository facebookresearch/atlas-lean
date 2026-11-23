/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSComponentProduct
public import MathlibExt.KTheory.Ring.K0.ProjectiveUniverseEquivalence
public import MathlibExt.KTheory.Exact.Quillen.SplitExactGroupCompletion

/-!
# The full based K₀ component product for finite projectives

For every associative unital ring, with independently sized projective
modules, this uses the entire fixed RingK0 group and the actual native
classifying space of the original additive S⁻¹S category. Its zero factor is
the original categorical zero-component realization. The existing canonical
component dictionary reindexes every class, with the positive-first formula
on every original pair. Both actual inverse homotopies remain relative to
the original zero pair and (0,zero-pair) product point.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Algebra
open CategoryTheory.SInverseS CategoryTheory.SInverseS.ComponentTranslation

universe u v w

public section

namespace AlgebraicKTheory.RingK0

variable (R : Type u) [Ring R]

/-- The fixed RingK0 factor uses its specified discrete topology. -/
local instance ringK0Topology : TopologicalSpace (RingK0 R) := ⊥
local instance ringK0Discrete : DiscreteTopology (RingK0 R) := ⟨rfl⟩

/-- Projective class labels use the existing Grothendieck discrete topology. -/
local instance projectiveGrothendieckTopology :
    TopologicalSpace (GrothendieckAddGroup (Skeleton (FGProjectiveCat.{max u v} R))) :=
  (grothendieckDiscreteSpace (C := FGProjectiveCat.{max u v} R)).str

local instance projectiveGrothendieckDiscrete :
    DiscreteTopology (GrothendieckAddGroup (Skeleton (FGProjectiveCat.{max u v} R))) :=
  grothendieckDiscreteSpace_discrete (C := FGProjectiveCat.{max u v} R)

/-- The fixed ring-universe K₀ group, with its actual discrete topology. -/
abbrev discreteSpace : TopCat.{u + 1} := TopCat.of (RingK0 R)

/-- The existing Grothendieck-to-fixed-RingK0 dictionary on the entire original large category. -/
def projectiveGrothendieckEquiv :
    GrothendieckAddGroup (Skeleton (FGProjectiveCat.{max u v} R)) ≃+ RingK0 R :=
  (K0.splitIso (FGProjectiveCat.{max u v} R)).addCommGroupIsoToAddEquiv.trans
    (projectiveUniverseEquiv.{u, v} R)

private theorem projectiveGrothendieckEquiv_difference_computation
    (X : Pair (FGProjectiveCat.{max u v} R)) :
    projectiveGrothendieckEquiv.{u, v} R X.difference =
      sInverseSComponentsUniverseEquiv.{u, v} R (CategoryTheory.ConnectedComponents.mk X) := rfl

/-- On every actual pair, this is the already proved original component dictionary. -/
theorem projectiveGrothendieckEquiv_difference
    (X : Pair (FGProjectiveCat.{max u v} R)) :
    projectiveGrothendieckEquiv.{u, v} R X.difference =
      sInverseSComponentsUniverseEquiv.{u, v} R (CategoryTheory.ConnectedComponents.mk X) :=
          projectiveGrothendieckEquiv_difference_computation.{u, v} R X

/-- Every original pair has its full positive-first fixed RingK0 difference. -/
theorem projectiveGrothendieckEquiv_mk
    (X : Pair (FGProjectiveCat.{max u v} R)) :
    projectiveGrothendieckEquiv.{u, v} R X.difference =
      K0.mk (FGProjectiveCat.UniverseEquivalence.shrinkObject.{u, v} R X.fst) -
        K0.mk (FGProjectiveCat.UniverseEquivalence.shrinkObject.{u, v} R X.snd) :=
  (projectiveGrothendieckEquiv_difference.{u, v} R X).trans
      (sInverseSComponentsUniverseEquiv_mk R X)

/-- The entire canonical group dictionary is a homeomorphism of the specified discrete spaces. -/
def projectiveGrothendieckHomeomorph :
    grothendieckDiscreteSpace (C := FGProjectiveCat.{max u v} R) ≃ₜ discreteSpace R where
  toEquiv := (projectiveGrothendieckEquiv.{u, v} R).toEquiv
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

/-- The actual native original S⁻¹S space, with independent projective carrier universe. -/
abbrev projectiveOriginalSpace :=
  nativeOriginalSpace.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R)

/-- The same actual native zero-component space of the original large projective category. -/
abbrev projectiveZeroSpace :=
  nativeZeroSpace.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R)

/-- The whole fixed K₀-discrete product, retaining its actual original zero factor. -/
abbrev projectiveProductSpace : TopCat.{max u v + 1} :=
  TopCat.of (RingK0 R × projectiveZeroSpace.{u, v, w} R)

/-- The literal original zero pair in the large projective native classifying space. -/
def projectiveOriginalPoint : projectiveOriginalSpace.{u, v, w} R :=
  nativeOriginalPoint.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R)

/-- The literal zero-component native point represented by that same pair. -/
def projectiveZeroPoint : projectiveZeroSpace.{u, v, w} R :=
  nativeZeroPoint.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R)

/-- The specified (0,zero-pair) point of the entire fixed RingK0 product. -/
def projectiveProductPoint : projectiveProductSpace.{u, v, w} R :=
    ⟨0, projectiveZeroPoint.{u, v, w} R⟩

private theorem projectiveOriginalPoint_eq_native_computation :
    projectiveOriginalPoint.{u, v, w} R =
      nativeOriginalPoint.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R) := by
  unfold projectiveOriginalPoint
  rfl

/-- The original Ring-space marked point is the literal native zero Pair point. -/
theorem projectiveOriginalPoint_eq_native :
    projectiveOriginalPoint.{u, v, w} R =
      nativeOriginalPoint.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R) :=
  projectiveOriginalPoint_eq_native_computation.{u, v, w} R

private theorem projectiveZeroPoint_eq_native_computation :
    projectiveZeroPoint.{u, v, w} R =
      nativeZeroPoint.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R) := by
  unfold projectiveZeroPoint
  rfl

/-- The original Ring zero point is the literal native categorical zero point. -/
theorem projectiveZeroPoint_eq_native :
    projectiveZeroPoint.{u, v, w} R =
      nativeZeroPoint.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R) :=
  projectiveZeroPoint_eq_native_computation.{u, v, w} R

private theorem projectiveProductPoint_eq_pair_computation :
    projectiveProductPoint.{u, v, w} R = (0, projectiveZeroPoint.{u, v, w} R) := by
  unfold projectiveProductPoint
  rfl

/-- The original whole Ring product point is the literal pair of zero class and zero point. -/
theorem projectiveProductPoint_eq_pair :
    projectiveProductPoint.{u, v, w} R = (0, projectiveZeroPoint.{u, v, w} R) :=
  projectiveProductPoint_eq_pair_computation.{u, v, w} R

private theorem projectiveNativeProductPoint_eq_pair :
    nativeProductPoint.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R) =
      ((0 : GrothendieckAddGroup (Skeleton (FGProjectiveCat.{max u v} R))),
        nativeZeroPoint.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R)) := by
  let e := nativeProductRealizationHomeomorph.{max u v + 1, max u v, w}
    (C := FGProjectiveCat.{max u v} R)
  have hPoint := nativeProductRealizationHomeomorph_point.{max u v + 1, max u v, w}
    (C := FGProjectiveCat.{max u v} R)
  have hPair := componentProductPoint_eq_zeroPair (C := FGProjectiveCat.{max u v} R)
  exact hPoint.symm.trans
    ((congrArg e hPair).trans
      ((nativeProductRealizationHomeomorph_apply.{max u v + 1, max u v, w}
        (C := FGProjectiveCat.{max u v} R) 0
            (zeroSpacePoint (C := FGProjectiveCat.{max u v} R))).trans
        (congrArg (fun z : projectiveZeroSpace.{u, v, w} R =>
          ((0 : GrothendieckAddGroup (Skeleton (FGProjectiveCat.{max u v} R))), z))
          (nativeZeroRealizationIso_inv_point.{max u v + 1, max u v, w}
            (C := FGProjectiveCat.{max u v} R)))))

/-- Reindex the whole product by the existing fixed RingK0 dictionary, changing no zero-space
map. -/
def projectiveProductReindexHomeomorph :
    nativeProductSpace.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R) ≃ₜ
        projectiveProductSpace.{u, v, w} R :=
  (projectiveGrothendieckHomeomorph.{u, v} R).prodCongr
    (Homeomorph.refl (projectiveZeroSpace.{u, v, w} R))

private theorem projectiveProductReindexHomeomorph_apply_computation
    (g : GrothendieckAddGroup (Skeleton (FGProjectiveCat.{max u v} R)))
    (z : projectiveZeroSpace.{u, v, w} R) :
    projectiveProductReindexHomeomorph.{u, v, w} R (g, z) =
      (projectiveGrothendieckEquiv.{u, v} R g, z) := rfl

private theorem projectiveProductReindexHomeomorph_symm_apply_computation
    (a : RingK0 R) (z : projectiveZeroSpace.{u, v, w} R) :
    (projectiveProductReindexHomeomorph.{u, v, w} R).symm (a, z) =
      ((projectiveGrothendieckEquiv.{u, v} R).symm a, z) := rfl

/-- Every original class and actual zero-space point has its literal reindexed coordinates. -/
theorem projectiveProductReindexHomeomorph_apply
    (g : GrothendieckAddGroup (Skeleton (FGProjectiveCat.{max u v} R)))
    (z : projectiveZeroSpace.{u, v, w} R) :
    projectiveProductReindexHomeomorph.{u, v, w} R (g, z) =
        (projectiveGrothendieckEquiv.{u, v} R g, z) :=
        projectiveProductReindexHomeomorph_apply_computation.{u, v, w} R g z

/-- The entire group reindexing preserves the specified original product unit. -/
theorem projectiveProductReindexHomeomorph_point :
    projectiveProductReindexHomeomorph.{u, v, w} R
        (nativeProductPoint.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R)) =
      projectiveProductPoint.{u, v, w} R := by
  rw [projectiveNativeProductPoint_eq_pair.{u, v, w} R,
    projectiveProductReindexHomeomorph_apply.{u, v, w} R]
  rw [projectiveProductPoint_eq_pair.{u, v, w} R, projectiveZeroPoint_eq_native.{u, v, w} R,
    map_zero]

/-- The inverse reindexing returns that same original product unit. -/
theorem projectiveProductReindexHomeomorph_inv_point :
    (projectiveProductReindexHomeomorph.{u, v, w} R).symm (projectiveProductPoint.{u, v, w} R) =
      nativeProductPoint.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R) := by
  let e := projectiveProductReindexHomeomorph.{u, v, w} R
  exact (congrArg e.symm (projectiveProductReindexHomeomorph_point.{u, v, w} R)).symm.trans
    (e.symm_apply_apply
      (nativeProductPoint.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R)))

/-- The full canonical RingK0 product map is the actual native component map with that same
dictionary. -/
def projectiveProductForward :
    C(projectiveOriginalSpace.{u, v, w} R, projectiveProductSpace.{u, v, w} R) :=
        (⟨projectiveProductReindexHomeomorph.{u, v, w} R,
    (projectiveProductReindexHomeomorph.{u, v, w} R).continuous⟩ :
    C(nativeProductSpace.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R),
      projectiveProductSpace.{u, v, w} R)).comp
    (nativeProductForward.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R))

/-- The full inverse uses the computed inverse dictionary and the same native inverse map. -/
def projectiveProductInverse :
    C(projectiveProductSpace.{u, v, w} R, projectiveOriginalSpace.{u, v, w} R) :=
        (nativeProductInverse.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R)).comp
    (⟨(projectiveProductReindexHomeomorph.{u, v, w} R).symm,
      (projectiveProductReindexHomeomorph.{u, v, w} R).symm.continuous⟩ :
      C(projectiveProductSpace.{u, v, w} R,
        nativeProductSpace.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R)))

private theorem projectiveProductForward_apply_computation
    (x : projectiveOriginalSpace.{u, v, w} R) :
    projectiveProductForward.{u, v, w} R x = projectiveProductReindexHomeomorph.{u, v, w} R
      (nativeProductForward.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R) x) := rfl

private theorem projectiveProductInverse_apply_computation
    (y : projectiveProductSpace.{u, v, w} R) :
    projectiveProductInverse.{u, v, w} R y =
      nativeProductInverse.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R)
        ((projectiveProductReindexHomeomorph.{u, v, w} R).symm y) := rfl

/-- The canonical full forward map is strictly based at the original zero pair. -/
theorem projectiveProductForward_point :
    projectiveProductForward.{u, v, w} R (projectiveOriginalPoint.{u, v, w} R) =
        projectiveProductPoint.{u, v, w} R := by
  rw [projectiveProductForward_apply_computation.{u, v, w} R,
    projectiveOriginalPoint_eq_native.{u, v, w} R,
    nativeProductForward_point.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R),
    projectiveProductReindexHomeomorph_point.{u, v, w} R]

/-- The canonical full inverse returns the same literal original zero pair. -/
theorem projectiveProductInverse_point :
    projectiveProductInverse.{u, v, w} R (projectiveProductPoint.{u, v, w} R) =
        projectiveOriginalPoint.{u, v, w} R := by
  rw [projectiveProductInverse_apply_computation.{u, v, w} R,
    projectiveProductReindexHomeomorph_inv_point.{u, v, w} R,
    nativeProductInverse_point.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R)]
  exact (projectiveOriginalPoint_eq_native.{u, v, w} R).symm

/-- The first actual full inverse family remains relative to the original zero pair in every
universe. -/
def projectiveProductLeftHomotopyRel :
    ContinuousMap.HomotopyRel ((projectiveProductInverse.{u, v, w} R).comp
        (projectiveProductForward.{u, v, w} R))
      (ContinuousMap.id (projectiveOriginalSpace.{u, v, w} R))
          {projectiveOriginalPoint.{u, v, w} R} := by
  let e := projectiveProductReindexHomeomorph.{u, v, w} R
  have h₀ : (nativeProductInverse.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R)).comp
      (nativeProductForward.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R)) =
        (projectiveProductInverse.{u, v, w} R).comp (projectiveProductForward.{u, v, w} R) := by
    apply ContinuousMap.ext
    intro x
    change nativeProductInverse.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R)
      (nativeProductForward.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R) x) =
        projectiveProductInverse.{u, v, w} R (projectiveProductForward.{u, v, w} R x)
    rw [projectiveProductInverse_apply_computation.{u, v, w} R,
      projectiveProductForward_apply_computation.{u, v, w} R]
    exact (congrArg (nativeProductInverse.{max u v + 1, max u v, w}
      (C := FGProjectiveCat.{max u v} R))
      (e.symm_apply_apply (nativeProductForward.{max u v + 1, max u v, w}
        (C := FGProjectiveCat.{max u v} R) x))).symm
  have hPoint : projectiveOriginalPoint.{u, v, w} R =
      nativeOriginalPoint.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R) :=
    projectiveOriginalPoint_eq_native.{u, v, w} R
  simpa only [← hPoint] using
    (nativeProductLeftHomotopyRel.{max u v + 1, max u v, w}
      (C := FGProjectiveCat.{max u v} R)).cast h₀ rfl

private def projectiveProductRightHomotopy :
    ContinuousMap.Homotopy ((projectiveProductForward.{u, v, w} R).comp
        (projectiveProductInverse.{u, v, w} R))
      (ContinuousMap.id (projectiveProductSpace.{u, v, w} R)) := by
  let e := projectiveProductReindexHomeomorph.{u, v, w} R
  let E : C(nativeProductSpace.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R),
      projectiveProductSpace.{u, v, w} R) := ⟨e, e.continuous⟩
  let Ei : C(projectiveProductSpace.{u, v, w} R,
      nativeProductSpace.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R)) :=
    ⟨e.symm, e.symm.continuous⟩
  let H := nativeProductRightHomotopyRel.{max u v + 1, max u v, w}
    (C := FGProjectiveCat.{max u v} R)
  let h := (ContinuousMap.Homotopy.refl E).comp (H.toHomotopy.compContinuousMap Ei)
  refine h.cast ?_ ?_
  · apply ContinuousMap.ext
    intro y
    rfl
  · apply ContinuousMap.ext
    intro y
    exact e.apply_symm_apply y

private theorem projectiveProductRightHomotopy_apply_computation
    (t : unitInterval) (y : projectiveProductSpace.{u, v, w} R) :
    projectiveProductRightHomotopy.{u, v, w} R (t, y) =
      projectiveProductReindexHomeomorph.{u, v, w} R
        (nativeProductRightHomotopyRel.{max u v + 1, max u v, w}
          (C := FGProjectiveCat.{max u v} R)
          (t, (projectiveProductReindexHomeomorph.{u, v, w} R).symm y)) := rfl

/-- The other actual full inverse family is relative to the original (0,zero-pair) product point. -/
def projectiveProductRightHomotopyRel :
    ContinuousMap.HomotopyRel ((projectiveProductForward.{u, v, w} R).comp
        (projectiveProductInverse.{u, v, w} R))
      (ContinuousMap.id (projectiveProductSpace.{u, v, w} R))
          {projectiveProductPoint.{u, v, w} R} where
  toHomotopy := projectiveProductRightHomotopy.{u, v, w} R
  prop' t y hy := by
    obtain rfl := Set.mem_singleton_iff.mp hy
    change projectiveProductRightHomotopy.{u, v, w} R
      (t, projectiveProductPoint.{u, v, w} R) =
        projectiveProductForward.{u, v, w} R
          (projectiveProductInverse.{u, v, w} R (projectiveProductPoint.{u, v, w} R))
    rw [projectiveProductRightHomotopy_apply_computation.{u, v, w} R,
      projectiveProductReindexHomeomorph_inv_point.{u, v, w} R,
      projectiveProductInverse_point.{u, v, w} R, projectiveProductForward_point.{u, v, w} R]
    exact (congrArg (projectiveProductReindexHomeomorph.{u, v, w} R)
      ((nativeProductRightHomotopyRel.{max u v + 1, max u v, w}
        (C := FGProjectiveCat.{max u v} R)).eq_snd t (by simp))).trans
      (projectiveProductReindexHomeomorph_point.{u, v, w} R)

/-- The full objectwise based component product, over every associative ring and independent module
universe. -/
def projectiveProductHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (projectiveOriginalSpace.{u, v, w} R)
      (projectiveProductSpace.{u, v, w} R) where
  toFun := projectiveProductForward.{u, v, w} R
  invFun := projectiveProductInverse.{u, v, w} R
  left_inv := ⟨(projectiveProductLeftHomotopyRel.{u, v, w} R).toHomotopy⟩
  right_inv := ⟨(projectiveProductRightHomotopyRel.{u, v, w} R).toHomotopy⟩

/-- The whole class formula retains the full actual zero-space coordinate, for every group label. -/
theorem projectiveProductForward_class
    (g : GrothendieckAddGroup (Skeleton (FGProjectiveCat.{max u v} R)))
    (z : componentSpace g) :
    projectiveProductForward.{u, v, w} R
        ((nativeOriginalRealizationIso.{max u v + 1, max u v, w}
          (C := FGProjectiveCat.{max u v} R)).inv
      (SSet.toTop.map (CategoryTheory.nerveMap (componentProperty g).ι) z)) =
        (projectiveGrothendieckEquiv.{u, v} R g,
            (nativeZeroRealizationIso.{max u v + 1, max u v, w}
              (C := FGProjectiveCat.{max u v} R)).inv (componentForward g z)) := by
  rw [projectiveProductForward_apply_computation.{u, v, w} R,
    nativeProductForward_class.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R),
    projectiveProductReindexHomeomorph_apply.{u, v, w} R]

/-- The inverse returns every fixed K₀ label through the same actual class inclusion and inverse
translation. -/
theorem projectiveProductInverse_class (a : RingK0 R) (z : projectiveZeroSpace.{u, v, w} R) :
    projectiveProductInverse.{u, v, w} R (a, z) =
        (nativeOriginalRealizationIso.{max u v + 1, max u v, w}
          (C := FGProjectiveCat.{max u v} R)).inv
      (SSet.toTop.map (CategoryTheory.nerveMap
        (componentProperty ((projectiveGrothendieckEquiv.{u, v} R).symm a)).ι)
          (componentInverse ((projectiveGrothendieckEquiv.{u, v} R).symm a)
            ((nativeZeroRealizationIso.{max u v + 1, max u v, w}
                (C := FGProjectiveCat.{max u v} R)).hom z))) := by
  rw [projectiveProductInverse_apply_computation.{u, v, w} R,
    projectiveProductReindexHomeomorph_symm_apply_computation.{u, v, w} R]
  exact nativeProductInverse_class.{max u v + 1, max u v, w}
    (C := FGProjectiveCat.{max u v} R) _ z

/-- Every fixed RingK0 class appears as the first coordinate of the actual full forward map. -/
theorem projectiveProductForward_every_class (a : RingK0 R)
    (z : componentSpace
      ((projectiveGrothendieckEquiv.{u, v} R).symm a)) :
    (projectiveProductForward.{u, v, w} R
      ((nativeOriginalRealizationIso.{max u v + 1, max u v, w}
          (C := FGProjectiveCat.{max u v} R)).inv
        (SSet.toTop.map (CategoryTheory.nerveMap
          (componentProperty ((projectiveGrothendieckEquiv.{u, v} R).symm a)).ι) z))).1 = a := by
  have h := congrArg (fun y : projectiveProductSpace.{u, v, w} R => y.1)
    (projectiveProductForward_class.{u, v, w} R
      ((projectiveGrothendieckEquiv.{u, v} R).symm a) z)
  exact h.trans ((projectiveGrothendieckEquiv.{u, v} R).apply_symm_apply a)

/-- On every original pair class, the full forward map has the existing positive-first fixed-K0
value. -/
theorem projectiveProductForward_pair_class
    (X : Pair (FGProjectiveCat.{max u v} R)) (z : componentSpace X.difference) :
    (projectiveProductForward.{u, v, w} R
      ((nativeOriginalRealizationIso.{max u v + 1, max u v, w}
          (C := FGProjectiveCat.{max u v} R)).inv
        (SSet.toTop.map (CategoryTheory.nerveMap (componentProperty X.difference).ι) z))).1 =
      K0.mk (FGProjectiveCat.UniverseEquivalence.shrinkObject.{u, v} R X.fst) -
        K0.mk (FGProjectiveCat.UniverseEquivalence.shrinkObject.{u, v} R X.snd) := by
  have h := congrArg (fun y : projectiveProductSpace.{u, v, w} R => y.1)
    (projectiveProductForward_class.{u, v, w} R X.difference z)
  exact h.trans (projectiveGrothendieckEquiv_mk.{u, v} R X)

/-- The literal fixed-K₀ product with the actual path component of the original zero pair. -/
abbrev projectivePathProductSpace : TopCat.{max u v + 1} :=
  TopCat.of (RingK0 R × pathComponent (projectiveOriginalPoint.{u, v, w} R))

/-- The original unit in that literal path-component product. -/
def projectivePathProductPoint : projectivePathProductSpace.{u, v, w} R :=
  ⟨0, projectiveOriginalPoint.{u, v, w} R,
      mem_pathComponent_self (projectiveOriginalPoint.{u, v, w} R)⟩

/-- Replace only the canonical zero factor by its computed actual ambient path component. -/
def projectivePathProductHomeomorph :
    projectiveProductSpace.{u, v, w} R ≃ₜ projectivePathProductSpace.{u, v, w} R :=
  (Homeomorph.refl (RingK0 R)).prodCongr
    (nativeZeroPathComponentHomeomorph.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R))

private theorem projectivePathProductHomeomorph_apply_computation
    (a : RingK0 R) (z : projectiveZeroSpace.{u, v, w} R) :
    projectivePathProductHomeomorph.{u, v, w} R (a, z) =
      (a, nativeZeroPathComponentHomeomorph.{max u v + 1, max u v, w}
        (C := FGProjectiveCat.{max u v} R) z) := rfl

private theorem projectivePathProductHomeomorph_point_computation :
    projectivePathProductHomeomorph.{u, v, w} R (projectiveProductPoint.{u, v, w} R) =
      projectivePathProductPoint.{u, v, w} R := by
  change ((0 : RingK0 R), nativeZeroPathComponentHomeomorph.{max u v + 1, max u v, w}
      (C := FGProjectiveCat.{max u v} R)
      (nativeZeroPoint.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R))) =
    (0, ⟨nativeOriginalPoint.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R),
      mem_pathComponent_self _⟩)
  rw [nativeZeroPathComponentHomeomorph_point.{max u v + 1, max u v, w}
    (C := FGProjectiveCat.{max u v} R)]

/-- The actual zero-component homeomorphism preserves the specified original product unit. -/
theorem projectivePathProductHomeomorph_point :
    projectivePathProductHomeomorph.{u, v, w} R (projectiveProductPoint.{u, v, w} R) =
      projectivePathProductPoint.{u, v, w} R :=
          projectivePathProductHomeomorph_point_computation.{u, v, w} R

/-- The full map to fixed K₀ times the literal original path component. -/
def projectivePathProductForward :
    C(projectiveOriginalSpace.{u, v, w} R, projectivePathProductSpace.{u, v, w} R) :=
        (⟨projectivePathProductHomeomorph.{u, v, w} R,
    (projectivePathProductHomeomorph.{u, v, w} R).continuous⟩ :
    C(projectiveProductSpace.{u, v, w} R, projectivePathProductSpace.{u, v, w} R)).comp
      (projectiveProductForward.{u, v, w} R)

/-- Its actual full inverse returns through the same zero inclusion and original inverse
translations. -/
def projectivePathProductInverse :
    C(projectivePathProductSpace.{u, v, w} R, projectiveOriginalSpace.{u, v, w} R) :=
        (projectiveProductInverse.{u, v, w} R).comp
    (⟨(projectivePathProductHomeomorph.{u, v, w} R).symm,
      (projectivePathProductHomeomorph.{u, v, w} R).symm.continuous⟩ :
      C(projectivePathProductSpace.{u, v, w} R, projectiveProductSpace.{u, v, w} R))

private theorem projectivePathProductForward_apply_computation
    (x : projectiveOriginalSpace.{u, v, w} R) :
    projectivePathProductForward.{u, v, w} R x =
      projectivePathProductHomeomorph.{u, v, w} R (projectiveProductForward.{u, v, w} R x) := rfl

private theorem projectivePathProductInverse_apply_computation
    (y : projectivePathProductSpace.{u, v, w} R) :
    projectivePathProductInverse.{u, v, w} R y =
      projectiveProductInverse.{u, v, w} R
          ((projectivePathProductHomeomorph.{u, v, w} R).symm y) := rfl

private theorem projectivePathProductHomeomorph_inv_point :
    (projectivePathProductHomeomorph.{u, v, w} R).symm (projectivePathProductPoint.{u, v, w} R) =
      projectiveProductPoint.{u, v, w} R := by
  let e := projectivePathProductHomeomorph.{u, v, w} R
  exact (congrArg e.symm (projectivePathProductHomeomorph_point.{u, v, w} R)).symm.trans
    (e.symm_apply_apply (projectiveProductPoint.{u, v, w} R))

/-- The literal original path-component product map is strictly based. -/
theorem projectivePathProductForward_point :
    projectivePathProductForward.{u, v, w} R (projectiveOriginalPoint.{u, v, w} R) =
      projectivePathProductPoint.{u, v, w} R := by
  rw [projectivePathProductForward_apply_computation.{u, v, w} R,
    projectiveProductForward_point.{u, v, w} R, projectivePathProductHomeomorph_point.{u, v, w} R]

/-- Its inverse returns the same literal original zero pair. -/
theorem projectivePathProductInverse_point :
    projectivePathProductInverse.{u, v, w} R (projectivePathProductPoint.{u, v, w} R) =
      projectiveOriginalPoint.{u, v, w} R := by
  rw [projectivePathProductInverse_apply_computation.{u, v, w} R,
    projectivePathProductHomeomorph_inv_point.{u, v, w} R,
        projectiveProductInverse_point.{u, v, w} R]

/-- The first full inverse family is relative to the original zero pair for this literal product. -/
def projectivePathProductLeftHomotopyRel :
    ContinuousMap.HomotopyRel ((projectivePathProductInverse.{u, v, w} R).comp
        (projectivePathProductForward.{u, v, w} R))
      (ContinuousMap.id (projectiveOriginalSpace.{u, v, w} R))
          {projectiveOriginalPoint.{u, v, w} R} := by
  let e := projectivePathProductHomeomorph.{u, v, w} R
  have h : (projectiveProductInverse.{u, v, w} R).comp (projectiveProductForward.{u, v, w} R) =
      (projectivePathProductInverse.{u, v, w} R).comp
          (projectivePathProductForward.{u, v, w} R) := by
    apply ContinuousMap.ext
    intro x
    change projectiveProductInverse.{u, v, w} R (projectiveProductForward.{u, v, w} R x) =
      projectivePathProductInverse.{u, v, w} R (projectivePathProductForward.{u, v, w} R x)
    rw [projectivePathProductInverse_apply_computation.{u, v, w} R,
      projectivePathProductForward_apply_computation.{u, v, w} R]
    exact (congrArg (projectiveProductInverse.{u, v, w} R)
      (e.symm_apply_apply (projectiveProductForward.{u, v, w} R x))).symm
  exact (projectiveProductLeftHomotopyRel.{u, v, w} R).cast h rfl

private def projectivePathProductRightHomotopy :
    ContinuousMap.Homotopy ((projectivePathProductForward.{u, v, w} R).comp
        (projectivePathProductInverse.{u, v, w} R))
      (ContinuousMap.id (projectivePathProductSpace.{u, v, w} R)) := by
  let e := projectivePathProductHomeomorph.{u, v, w} R
  let E : C(projectiveProductSpace.{u, v, w} R, projectivePathProductSpace.{u, v, w} R) :=
    ⟨e, e.continuous⟩
  let Ei : C(projectivePathProductSpace.{u, v, w} R, projectiveProductSpace.{u, v, w} R) :=
    ⟨e.symm, e.symm.continuous⟩
  let h := (ContinuousMap.Homotopy.refl E).comp
    ((projectiveProductRightHomotopyRel.{u, v, w} R).toHomotopy.compContinuousMap Ei)
  refine h.cast ?_ ?_
  · apply ContinuousMap.ext
    intro y
    rfl
  · apply ContinuousMap.ext
    intro y
    exact e.apply_symm_apply y

private theorem projectivePathProductRightHomotopy_apply_computation
    (t : unitInterval) (y : projectivePathProductSpace.{u, v, w} R) :
    projectivePathProductRightHomotopy.{u, v, w} R (t, y) =
      projectivePathProductHomeomorph.{u, v, w} R
        (projectiveProductRightHomotopyRel.{u, v, w} R
          (t, (projectivePathProductHomeomorph.{u, v, w} R).symm y)) := rfl

/-- The other full inverse family is relative to the literal (0,original-zero-pair) path-component
point. -/
def projectivePathProductRightHomotopyRel :
    ContinuousMap.HomotopyRel ((projectivePathProductForward.{u, v, w} R).comp
        (projectivePathProductInverse.{u, v, w} R))
      (ContinuousMap.id (projectivePathProductSpace.{u, v, w} R))
          {projectivePathProductPoint.{u, v, w} R} where
  toHomotopy := projectivePathProductRightHomotopy.{u, v, w} R
  prop' t y hy := by
    obtain rfl := Set.mem_singleton_iff.mp hy
    change projectivePathProductRightHomotopy.{u, v, w} R
      (t, projectivePathProductPoint.{u, v, w} R) =
        projectivePathProductForward.{u, v, w} R
          (projectivePathProductInverse.{u, v, w} R (projectivePathProductPoint.{u, v, w} R))
    rw [projectivePathProductRightHomotopy_apply_computation.{u, v, w} R,
      projectivePathProductHomeomorph_inv_point.{u, v, w} R,
      projectivePathProductInverse_point.{u, v, w} R,
          projectivePathProductForward_point.{u, v, w} R]
    exact (congrArg (projectivePathProductHomeomorph.{u, v, w} R)
      ((projectiveProductRightHomotopyRel.{u, v, w} R).eq_snd t (by simp))).trans
      (projectivePathProductHomeomorph_point.{u, v, w} R)

/-- The full objectwise based product with the literal original zero path component, in every
universe. -/
def projectivePathProductHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (projectiveOriginalSpace.{u, v, w} R)
      (projectivePathProductSpace.{u, v, w} R) where
  toFun := projectivePathProductForward.{u, v, w} R
  invFun := projectivePathProductInverse.{u, v, w} R
  left_inv := ⟨(projectivePathProductLeftHomotopyRel.{u, v, w} R).toHomotopy⟩
  right_inv := ⟨(projectivePathProductRightHomotopyRel.{u, v, w} R).toHomotopy⟩

/-- Every fixed RingK0 class is retained by the full map to the literal path-component product. -/
theorem projectivePathProductForward_every_class (a : RingK0 R)
    (z : componentSpace ((projectiveGrothendieckEquiv.{u, v} R).symm a)) :
    (projectivePathProductForward.{u, v, w} R
        ((nativeOriginalRealizationIso.{max u v + 1, max u v, w}
          (C := FGProjectiveCat.{max u v} R)).inv
      (SSet.toTop.map (CategoryTheory.nerveMap
        (componentProperty ((projectiveGrothendieckEquiv.{u, v} R).symm a)).ι) z))).1 = a := by
  let x := (nativeOriginalRealizationIso.{max u v + 1, max u v, w}
    (C := FGProjectiveCat.{max u v} R)).inv
      (SSet.toTop.map (CategoryTheory.nerveMap
        (componentProperty ((projectiveGrothendieckEquiv.{u, v} R).symm a)).ι) z)
  have h : (projectivePathProductForward.{u, v, w} R x).1 =
      (projectiveProductForward.{u, v, w} R x).1 := by
    rw [projectivePathProductForward_apply_computation.{u, v, w} R]
    exact congrArg (fun y : projectivePathProductSpace.{u, v, w} R => y.1)
      (projectivePathProductHomeomorph_apply_computation.{u, v, w} R
        (projectiveProductForward.{u, v, w} R x).1 (projectiveProductForward.{u, v, w} R x).2)
  exact h.trans (projectiveProductForward_every_class.{u, v, w} R a z)

/-- The forward field of the whole Ring component equivalence is the
SAME original full component-product map. -/
theorem projectiveProductHomotopyEquiv_toFun :
    (projectiveProductHomotopyEquiv.{u, v, w} R).toFun =
      projectiveProductForward.{u, v, w} R := by
  unfold projectiveProductHomotopyEquiv
  rfl

/-- Its inverse field is the SAME original full component-product inverse. -/
theorem projectiveProductHomotopyEquiv_invFun :
    (projectiveProductHomotopyEquiv.{u, v, w} R).invFun =
      projectiveProductInverse.{u, v, w} R := by
  unfold projectiveProductHomotopyEquiv
  rfl

end AlgebraicKTheory.RingK0
