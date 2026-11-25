/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Lie.ProjectiveFreeCover
public import MathlibExt.Algebra.Lie.UniversalEnveloping.PBW.IntrinsicComparison

/-!
# PBW for projective Lie carriers

For a Lie algebra whose underlying module over a commutative ring is projective, the canonical
map from the symmetric algebra to the associated graded enveloping algebra is an algebra
isomorphism.

A split Lie cover with free underlying module transfers PBW through the retract. Its inverse
is the composite of the graded inclusion, the inverse free-carrier PBW map, and the symmetric
projection.
-/

@[expose] public section

noncomputable section

universe u v

namespace UniversalEnvelopingAlgebra

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L] [Module.Projective R L]

/-- A classical order on the free-cover basis index. -/
def coverIndexOrder (X : Type*) : LinearOrder X := by
  classical
  exact linearOrderOfSTO WellOrderingRel
attribute [local instance] coverIndexOrder

/-- The symmetric map of the projective Lie inclusion. -/
abbrev coverSymmetricInclusion :
    SymmetricAlgebra R L →ₐ[R] SymmetricAlgebra R (LieAlgebra.ProjectiveFreeCover R L) :=
  SymmetricAlgebra.lift
    ((SymmetricAlgebra.ι R (LieAlgebra.ProjectiveFreeCover R L)).comp
      (LieAlgebra.projectiveCoverInclusion R L).toLinearMap)

/-- The symmetric map of the free Lie cover projection. -/
abbrev coverSymmetricProjection :
    SymmetricAlgebra R (LieAlgebra.ProjectiveFreeCover R L) →ₐ[R] SymmetricAlgebra R L :=
  SymmetricAlgebra.lift
    ((SymmetricAlgebra.ι R L).comp (LieAlgebra.projectiveCoverProjection R L).toLinearMap)

/-- The constructive free PBW equivalence on the Lie cover. -/
abbrev coverPBWEquiv :
    SymmetricAlgebra R (LieAlgebra.ProjectiveFreeCover R L) ≃ₐ[R]
      AssociatedGraded R (LieAlgebra.ProjectiveFreeCover R L) :=
  symmetricPBWEquivOfBasis (LieAlgebra.projectiveFreeCoverBasis R L)

theorem coverPBWEquiv_toAlgHom :
    (coverPBWEquiv R L).toAlgHom =
      symmetricComparison R (LieAlgebra.ProjectiveFreeCover R L) :=
  symmetricPBWEquivOfBasis_toAlgHom (LieAlgebra.projectiveFreeCoverBasis R L)

theorem coverSymmetricProjection_inclusion_apply (x : SymmetricAlgebra R L) :
    coverSymmetricProjection R L (coverSymmetricInclusion R L x) = x := by
  have h : (coverSymmetricProjection R L).comp (coverSymmetricInclusion R L) =
      AlgHom.id R (SymmetricAlgebra R L) := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro a
    change SymmetricAlgebra.lift
        ((SymmetricAlgebra.ι R L).comp (LieAlgebra.projectiveCoverProjection R L).toLinearMap)
        (SymmetricAlgebra.lift
          ((SymmetricAlgebra.ι R (LieAlgebra.ProjectiveFreeCover R L)).comp
            (LieAlgebra.projectiveCoverInclusion R L).toLinearMap)
          (SymmetricAlgebra.ι R L a)) = SymmetricAlgebra.ι R L a
    rw [SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply,
      SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply]
    exact congrArg (SymmetricAlgebra.ι R L)
      (LieAlgebra.projectiveCoverLinearProjection_inclusion_apply R L a)
  exact congrArg (fun f : SymmetricAlgebra R L →ₐ[R] SymmetricAlgebra R L => f x) h

/-- The enveloping algebra maps induced by the projective Lie cover are a split retraction of the
enveloping algebra. -/
theorem map_projectiveCoverProjection_comp_inclusion :
    (map R (LieAlgebra.projectiveCoverProjection R L)).comp
        (map R (LieAlgebra.projectiveCoverInclusion R L)) =
      AlgHom.id R (UniversalEnvelopingAlgebra R L) := by
  rw [← map_comp, LieAlgebra.projectiveCoverProjection_comp_inclusion, map_id]

/-- The quotient/direct-sum algebra maps are a split retraction. -/
theorem associatedGradedMap_projectiveCoverProjection_comp_inclusion :
    (associatedGradedMap R (LieAlgebra.projectiveCoverProjection R L)).comp
        (associatedGradedMap R (LieAlgebra.projectiveCoverInclusion R L)) =
      AlgHom.id R (AssociatedGraded R L) := by
  rw [← associatedGradedMap_comp, LieAlgebra.projectiveCoverProjection_comp_inclusion,
    associatedGradedMap_id]

/-- The PBW inverse obtained by composing the graded inclusion, the inverse free-cover PBW
equivalence, and the symmetric projection. -/
def projectivePBWInverse : AssociatedGraded R L →ₐ[R] SymmetricAlgebra R L :=
  (coverSymmetricProjection R L).comp
    ((coverPBWEquiv R L).symm.toAlgHom.comp
      (associatedGradedMap R (LieAlgebra.projectiveCoverInclusion R L)))

/-- The characteristic inverse formula is the split-retract composite. -/
theorem projectivePBWInverse_apply (x : AssociatedGraded R L) :
    projectivePBWInverse R L x =
      SymmetricAlgebra.lift
        ((SymmetricAlgebra.ι R L).comp (LieAlgebra.projectiveCoverProjection R L).toLinearMap)
        ((symmetricPBWEquivOfBasis (LieAlgebra.projectiveFreeCoverBasis R L)).symm
          (associatedGradedMap R (LieAlgebra.projectiveCoverInclusion R L) x)) := rfl

theorem projectivePBWInverse_leftInverse (x : SymmetricAlgebra R L) :
    projectivePBWInverse R L (symmetricComparison R L x) = x := by
  have hi := congrArg
    (fun f : SymmetricAlgebra R L →ₐ[R]
        AssociatedGraded R (LieAlgebra.ProjectiveFreeCover R L) => f x)
    (symmetricComparison_naturality R (LieAlgebra.projectiveCoverInclusion R L))
  change associatedGradedMap R (LieAlgebra.projectiveCoverInclusion R L)
      (symmetricComparison R L x) =
    symmetricComparison R (LieAlgebra.ProjectiveFreeCover R L) (coverSymmetricInclusion R L x)
    at hi
  change coverSymmetricProjection R L
      ((coverPBWEquiv R L).symm
        (associatedGradedMap R (LieAlgebra.projectiveCoverInclusion R L)
          (symmetricComparison R L x))) = x
  rw [hi, ← coverPBWEquiv_toAlgHom]
  change coverSymmetricProjection R L
      ((coverPBWEquiv R L).symm ((coverPBWEquiv R L) (coverSymmetricInclusion R L x))) = x
  rw [AlgEquiv.symm_apply_apply]
  exact coverSymmetricProjection_inclusion_apply R L x

theorem projectivePBWInverse_rightInverse (x : AssociatedGraded R L) :
    symmetricComparison R L (projectivePBWInverse R L x) = x := by
  let y := (coverPBWEquiv R L).symm
    (associatedGradedMap R (LieAlgebra.projectiveCoverInclusion R L) x)
  have hp := congrArg
    (fun f : SymmetricAlgebra R (LieAlgebra.ProjectiveFreeCover R L) →ₐ[R]
        AssociatedGraded R L => f y)
    (symmetricComparison_naturality R (LieAlgebra.projectiveCoverProjection R L))
  change associatedGradedMap R (LieAlgebra.projectiveCoverProjection R L)
      (symmetricComparison R (LieAlgebra.ProjectiveFreeCover R L) y) =
    symmetricComparison R L (coverSymmetricProjection R L y) at hp
  change symmetricComparison R L (coverSymmetricProjection R L y) = x
  rw [← hp, ← coverPBWEquiv_toAlgHom]
  change associatedGradedMap R (LieAlgebra.projectiveCoverProjection R L)
      ((coverPBWEquiv R L) ((coverPBWEquiv R L).symm
        (associatedGradedMap R (LieAlgebra.projectiveCoverInclusion R L) x))) = x
  rw [AlgEquiv.apply_symm_apply]
  exact congrArg (fun f : AssociatedGraded R L →ₐ[R] AssociatedGraded R L => f x)
    (associatedGradedMap_projectiveCoverProjection_comp_inclusion R L)

/-- PBW for an arbitrary projective underlying Lie module over an arbitrary commutative ring, on
the intrinsic associated graded enveloping algebra. -/
def symmetricPBWEquivOfProjective : SymmetricAlgebra R L ≃ₐ[R] AssociatedGraded R L where
  __ := symmetricComparison R L
  invFun := projectivePBWInverse R L
  left_inv := projectivePBWInverse_leftInverse R L
  right_inv := projectivePBWInverse_rightInverse R L

@[simp]
theorem symmetricPBWEquivOfProjective_toAlgHom :
    (symmetricPBWEquivOfProjective R L).toAlgHom = symmetricComparison R L := rfl

@[simp]
theorem symmetricPBWEquivOfProjective_symm_apply (x : AssociatedGraded R L) :
    (symmetricPBWEquivOfProjective R L).symm x = projectivePBWInverse R L x := rfl

@[simp]
theorem symmetricPBWEquivOfProjective_ι (x : L) :
    symmetricPBWEquivOfProjective R L (SymmetricAlgebra.ι R L x) =
      associatedGradedGeneratorSymbol R L x := symmetricComparison_ι R L x

/-- The canonical symmetric comparison is bijective under projectivity. -/
theorem symmetricComparison_bijective_of_projective :
    Function.Bijective (symmetricComparison R L) :=
  (symmetricPBWEquivOfProjective R L).bijective

/-- The projective PBW forward map agrees with every free-basis construction whenever the
underlying module also has a basis. -/
theorem symmetricPBWEquivOfProjective_eq_of_basis {I : Type*} [LinearOrder I]
    (b : Module.Basis I R L) :
    symmetricPBWEquivOfProjective R L = symmetricPBWEquivOfBasis b := by
  apply AlgEquiv.ext
  intro x
  change symmetricComparison R L x = (symmetricPBWEquivOfBasis b).toAlgHom x
  rw [symmetricPBWEquivOfBasis_toAlgHom]

/-- Injectivity of the Lie map into the enveloping algebra under projectivity is reflected through
its free Lie retract. -/
theorem ι_injective_of_projective : Function.Injective (ι R (L := L)) := by
  intro x y hxy
  have hi : ι R (LieAlgebra.projectiveCoverInclusion R L x) =
      ι R (LieAlgebra.projectiveCoverInclusion R L y) := by
    simpa only [map_ι] using
      congrArg (map R (LieAlgebra.projectiveCoverInclusion R L)) hxy
  have hixy := (PBW.ι_injective_of_free
    (R := R) (L := LieAlgebra.ProjectiveFreeCover R L)) hi
  simpa only [LieAlgebra.projectiveCoverProjection_inclusion_apply] using
    congrArg (LieAlgebra.projectiveCoverProjection R L) hixy

end UniversalEnvelopingAlgebra
