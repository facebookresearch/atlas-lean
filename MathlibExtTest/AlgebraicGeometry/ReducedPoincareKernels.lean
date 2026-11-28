/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.MixedReducedPoincareKernels

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.ReducedPoincareKernelsTest

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open CoherentCurveLinearSeries AlgebraicLineBundleFamilies PointedPicardFamilies
open NumericalCompactifiedJacobians ReducedPicardTensorActions ReducedPoincareFamilies
open MixedReducedPoincareKernels FourierMukai PositiveCurveDeterminants
open AffineDerivedCoefficientModules SchemeModulesTensor CurveCohomologyDeterminantModels

variable {k : Type} [Field k] [IsAlgClosed k]
  (C : Over (Spec (.of k))) [IsProperCurve C.hom] [TorsionFreeRestrictions C.left]
  (q q' : Polarization C.left) (s : SmoothMarking C)
  (M : FineCompactifiedJacobian C q s) (N : FineCompactifiedJacobian C q' s)
  (J : PicardZeroModel C s.p)

-- The Picard tensor action is parametrized by `Pic⁰ ⊗ J̄`, and its tensor family is the tensor
-- product of the two pulled-back universal families.
example : actionBase C q s M J = J.J ⊗ M.J := rfl

example (T : Over (Spec (.of k))) (f : T ⟶ M.J) (g : T ⟶ J.J) :
    tensorFamily C q s M J T f g =
      moduleTensor (prod C T).left (familyPullback C M.J T M.F f)
        (familyPullback C J.J T J.P g) := rfl

-- The bounded coherent objects used by the mixed equivalence are main's.
example (X : Scheme.{0}) :
    BoundedCoh X = (BoundedCoherent.boundedCoherent X).FullSubcategory := rfl

variable [HasDerivedPullbacks.{0}] [HasDerivedScalarExtensions.{0}] [HasDerivedPushforwards.{0}]
  [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]

-- The Poincaré family lives over `J̄ × Pic⁰`; its universal sheaf and line are the pullbacks of
-- the universal families along the two projections, and its tensor is their tensor product.
example : parameterBase C q s M J = prod M.J J.J := rfl

example : universalSheaf C q s M J = familyPullback C M.J (prod M.J J.J) M.F prod.fst := rfl

example : universalLine C q s M J = familyPullback C J.J (prod M.J J.J) J.P prod.snd := rfl

example : universalTensor C q s M J =
    moduleTensor (prod C (prod M.J J.J)).left (universalSheaf C q s M J)
      (universalLine C q s M J) := rfl

-- The mixed kernel lives on `J̄_q × J̄_{q'}`.
noncomputable example (S : AffineSources) (A : DeterminantSystem S) (L : LineLocus C q s M)
    (L' : LineLocus C q' s N) (D : OpenCohomologyData C q q' s M N L L') :
    (prod M.J N.J).left.Modules := mixedKernelModule S A C q q' s M N L L' D

end MathlibExt.AlgebraicGeometry.ReducedPoincareKernelsTest
