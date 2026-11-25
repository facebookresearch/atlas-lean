/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.MixedReducedPoincareKernels
public import MathlibExt.AlgebraicGeometry.ProjectiveLineSystems

/-!
# Reduced-curve Poincare and mixed Fourier--Mukai targets

All maps, modules and kernels are computed from actual universal sheaves,
native curve cohomology, inverse-shift determinants and canonical sheaf
duals. Autoduality and the mixed equivalence remain direct targets; no
such conclusion is encoded in their standing input data.

Sources read: MRV arXiv:1207.7233v5, Section 5/Theorem C; MRV
arXiv:1308.0564v2, Equation (4.1), Remark 4.2, Theorem 4.6/Theorem A.
The Cohen–Macaulay and flatness request and the mixed equivalence retain
MRV II's hypothesis char(k)=0 or char(k)>p_a(C) (Theorem 4.6, Theorem A), where
the arithmetic genus p_a(C) is h¹(C, 𝒪_C) (H⁰(C, 𝒪_C) = k for a reduced
connected proper curve over an algebraically closed field); Picard-zero
autoduality (MRV I, Theorem C) has no such restriction. The mixed equivalence
is requested for the kernel of the chosen universal sheaves; their
independence in degree zero (MRV II, Remark 4.2) is not requested. Scalar bases for
D(O_C) and an O_C compactification point are not requested.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.ReducedPoincareModelsWanted

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open _root_.MathlibExt.AlgebraicGeometry
open CoherentCurveLinearSeries NumericalCompactifiedJacobians PointedPicardFamilies
open FourierMukai SchemeDeterminantPresentations AffineDerivedCoefficientModules
open PositiveCurveDeterminants CurveCohomologyDeterminantModels
open ReducedPicardTensorActions ReducedPoincareFamilies MixedReducedPoincareKernels

def_wanted curveDeterminantSystem
    [HasDerivedPullbacks.{0}] [HasDerivedScalarExtensions.{0}] [HasDerivedPushforwards.{0}]
    [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
    (S : AffineSources) : DeterminantSystem S

def_wanted generalizedJacobianTensorAction
    (k : Type) [Field k] [IsAlgClosed k]
    (C : Over (Spec (.of k))) [TorsionFreeRestrictions C.left]
    [IsProperCurve C.hom] [IsReduced C.left] [ConnectedSpace C.left]
    (projective : ProjectiveSpace.IsProjective C)
    (q : Polarization C.left) (general : IsNondegenerate C q) (s : SmoothMarking C)
    (M : FineCompactifiedJacobian C q s) (J : PicardZeroModel C s.p) : PicardTensorAction C q s M J

def_wanted reducedPoincareCohomology
    [HasDerivedPullbacks.{0}] [HasDerivedScalarExtensions.{0}] [HasDerivedPushforwards.{0}]
    [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
    (k : Type) [Field k] [IsAlgClosed k]
    (C : Over (Spec (.of k))) [TorsionFreeRestrictions C.left]
    [IsProperCurve C.hom] [IsReduced C.left] [ConnectedSpace C.left]
    (projective : ProjectiveSpace.IsProjective C)
    (q : Polarization C.left) (general : IsNondegenerate C q) (s : SmoothMarking C)
    (M : FineCompactifiedJacobian C q s) (J : PicardZeroModel C s.p) :
    PoincareCohomologyData C q s M J

def_wanted reducedPoincareFamily
    [HasDerivedPullbacks.{0}] [HasDerivedScalarExtensions.{0}] [HasDerivedPushforwards.{0}]
    [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
    (k : Type) [Field k] [IsAlgClosed k]
    (C : Over (Spec (.of k))) [TorsionFreeRestrictions C.left]
    [IsProperCurve C.hom] [IsReduced C.left] [ConnectedSpace C.left]
    (projective : ProjectiveSpace.IsProjective C)
    (q : Polarization C.left) (general : IsNondegenerate C q) (s : SmoothMarking C)
    (M : FineCompactifiedJacobian C q s) (J : PicardZeroModel C s.p)
    (S : AffineSources) (A : DeterminantSystem S) (D : PoincareCohomologyData C q s M J)
    (p0 : 𝟙_ (Over (Spec (.of k))) ⟶ M.J)
    (planar : IsLocallyPlanar C) : PoincareFamilyData S A C q s M J D p0

theorem_wanted reducedBetaGroupCompatibility
    [HasDerivedPullbacks.{0}] [HasDerivedScalarExtensions.{0}] [HasDerivedPushforwards.{0}]
    [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
    (k : Type) [Field k] [IsAlgClosed k]
    (C : Over (Spec (.of k))) [TorsionFreeRestrictions C.left]
    [IsProperCurve C.hom] [IsReduced C.left] [ConnectedSpace C.left]
    (projective : ProjectiveSpace.IsProjective C)
    (q : Polarization C.left) (general : IsNondegenerate C q) (s : SmoothMarking C)
    (M : FineCompactifiedJacobian C q s) (J : PicardZeroModel C s.p)
    (S : AffineSources) (A : DeterminantSystem S) (D : PoincareCohomologyData C q s M J)
    (p0 : 𝟙_ (Over (Spec (.of k))) ⟶ M.J)
    (planar : IsLocallyPlanar C) (F : PoincareFamilyData S A C q s M J D p0) :
    BetaGroupCompatibility S A C q s M J D F

theorem_wanted reducedCurveAutoduality
    [HasDerivedPullbacks.{0}] [HasDerivedScalarExtensions.{0}] [HasDerivedPushforwards.{0}]
    [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
    (k : Type) [Field k] [IsAlgClosed k]
    (C : Over (Spec (.of k))) [TorsionFreeRestrictions C.left]
    [IsProperCurve C.hom] [IsReduced C.left] [ConnectedSpace C.left]
    (projective : ProjectiveSpace.IsProjective C)
    (q : Polarization C.left) (general : IsNondegenerate C q) (s : SmoothMarking C)
    (M : FineCompactifiedJacobian C q s) (J : PicardZeroModel C s.p)
    (S : AffineSources) (A : DeterminantSystem S) (D : PoincareCohomologyData C q s M J)
    (p0 : 𝟙_ (Over (Spec (.of k))) ⟶ M.J)
    (planar : IsLocallyPlanar C) (F : PoincareFamilyData S A C q s M J D p0) :
    IsIso (beta S A C q s M J D F)

def_wanted compactifiedLineLocus
    (k : Type) [Field k] [IsAlgClosed k]
    (C : Over (Spec (.of k))) [TorsionFreeRestrictions C.left]
    [IsProperCurve C.hom] [IsReduced C.left] [ConnectedSpace C.left]
    (projective : ProjectiveSpace.IsProjective C)
    (q : Polarization C.left) (general : IsNondegenerate C q) (s : SmoothMarking C)
    (M : FineCompactifiedJacobian C q s) : LineLocus C q s M

def_wanted mixedOpenPoincareCohomology
    [HasDerivedPullbacks.{0}] [HasDerivedScalarExtensions.{0}] [HasDerivedPushforwards.{0}]
    [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
    (k : Type) [Field k] [IsAlgClosed k]
    (C : Over (Spec (.of k))) [TorsionFreeRestrictions C.left]
    [IsProperCurve C.hom] [IsReduced C.left] [ConnectedSpace C.left]
    (projective : ProjectiveSpace.IsProjective C)
    (q q' : Polarization C.left) (general : IsNondegenerate C q)
    (general' : IsNondegenerate C q') (s : SmoothMarking C)
    (M : FineCompactifiedJacobian C q s) (N : FineCompactifiedJacobian C q' s)
    (planar : IsLocallyPlanar C) (L : LineLocus C q s M) (L' : LineLocus C q' s N) :
    OpenCohomologyData C q q' s M N L L'

def_wanted mixedProductCoordinates
    [HasDerivedPullbacks.{0}] [HasDerivedScalarExtensions.{0}] [HasDerivedPushforwards.{0}]
    [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
    (k : Type) [Field k] [IsAlgClosed k]
    (C : Over (Spec (.of k))) [TorsionFreeRestrictions C.left]
    [IsProperCurve C.hom] [IsReduced C.left] [ConnectedSpace C.left]
    (projective : ProjectiveSpace.IsProjective C)
    (q q' : Polarization C.left) (general : IsNondegenerate C q)
    (general' : IsNondegenerate C q') (s : SmoothMarking C)
    (M : FineCompactifiedJacobian C q s) (N : FineCompactifiedJacobian C q' s) :
    ProductCoordinates C q q' s M N

theorem_wanted mixedPoincareCohenMacaulay
    [HasDerivedPullbacks.{0}] [HasDerivedScalarExtensions.{0}] [HasDerivedPushforwards.{0}]
    [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
    (k : Type) [Field k] [IsAlgClosed k]
    (C : Over (Spec (.of k))) [TorsionFreeRestrictions C.left]
    [IsProperCurve C.hom] [IsReduced C.left] [ConnectedSpace C.left]
    (projective : ProjectiveSpace.IsProjective C)
    (q q' : Polarization C.left) (general : IsNondegenerate C q)
    (general' : IsNondegenerate C q') (s : SmoothMarking C)
    (M : FineCompactifiedJacobian C q s) (N : FineCompactifiedJacobian C q' s)
    (S : AffineSources) (A : DeterminantSystem S)
    (L : LineLocus C q s M) (L' : LineLocus C q' s N)
    (D : OpenCohomologyData C q q' s M N L L')
    (P : ProductCoordinates C q q' s M N)
    (planar : IsLocallyPlanar C)
    (characteristic : CharZero k ∨ ∃ p : ℕ, CharP k p ∧
      Module.finrank k (cohomology C.hom (structureModule C.left) 1) < p) :
    CompactifiedPoincareKernels.IsClosedPointMCM (mixedKernelModule S A C q q' s M N L L' D) ∧
      IsFlatOver (prod.fst : prod M.J N.J ⟶ M.J).left (mixedKernelModule S A C q q' s M N L L' D) ∧
      IsFlatOver (prod.snd : prod M.J N.J ⟶ N.J).left (mixedKernelModule S A C q q' s M N L L' D)

/-- The mixed Fourier–Mukai equivalence given by the kernel of the chosen universal sheaves
(MRV II, Theorem A); the universal sheaves are part of the data. -/
def_wanted chosenMixedPoincareEquivalence
    [HasDerivedPullbacks.{0}] [HasDerivedScalarExtensions.{0}] [HasDerivedPushforwards.{0}]
    [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
    (k : Type) [Field k] [IsAlgClosed k]
    (C : Over (Spec (.of k))) [TorsionFreeRestrictions C.left]
    [IsProperCurve C.hom] [IsReduced C.left] [ConnectedSpace C.left]
    (projective : ProjectiveSpace.IsProjective C)
    (q q' : Polarization C.left) (general : IsNondegenerate C q)
    (general' : IsNondegenerate C q') (s : SmoothMarking C)
    (M : FineCompactifiedJacobian C q s) (N : FineCompactifiedJacobian C q' s)
    (S : AffineSources) (A : DeterminantSystem S)
    (L : LineLocus C q s M) (L' : LineLocus C q' s N)
    (D : OpenCohomologyData C q q' s M N L L')
    (P : ProductCoordinates C q q' s M N)
    [HasDerivedTensors.{0}] (planar : IsLocallyPlanar C)
    (characteristic : CharZero k ∨ ∃ p : ℕ, CharP k p ∧
      Module.finrank k (cohomology C.hom (structureModule C.left) 1) < p) :
    MixedFourierMukaiEquivalence S A C q q' s M N L L' D P

end WantedExt.AlgebraicGeometry.ReducedPoincareModelsWanted
