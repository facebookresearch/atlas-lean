/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ReducedPoincareFamilies
public import MathlibExt.AlgebraicGeometry.BoundedCoherent

/-!
# Actual mixed compactified-Jacobian Poincare kernels

The two compactified Jacobians and their universal sheaves are independent.
The open determinant formula is used only where at least one actual family
is a line bundle; the tensor family need not be flat on the whole product.
The full kernel is the actual j_* of that open line. Its inverse uses the
actual sheaf dual, transposed product and genus shift.

No inverse-kernel or equivalence theorem is an input field. The bounded
quasicoherent/coherent equivalence targets below retain the actual native
Fourier--Mukai functors on both directions. Canonical independence from
universal sheaves requires degree zero; other Euler characteristics retain
the supplied universal-family choice.
Source: MRV arXiv:1308.0564v2, Section 4, Equation (4.1), Remark 4.2,
Theorem 4.6 and Theorem A (pp2--3,14--15). The equivalence has the source
restriction char(k)=0 or char(k)>p_a(C).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MixedReducedPoincareKernels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open CoherentCurveLinearSeries AlgebraicLineBundleFamilies PointedPicardFamilies
open NumericalCompactifiedJacobians ReducedPicardTensorActions
open FourierMukai PositiveCurveDeterminants CurveCohomologyDeterminantModels
open SchemeDeterminantPresentations AffineDerivedCoefficientModules NativeLineDuals

attribute [local instance] HasDerivedCategory.standard

variable {k : Type} [Field k] [IsAlgClosed k]

structure LineLocus (C : Over (Spec (.of k))) [IsProperCurve C.hom] [TorsionFreeRestrictions C.left]
    (q : Polarization C.left) (s : SmoothMarking C) (M : FineCompactifiedJacobian C q s) where
  openSet : M.J.left.Opens
  allTests : ∀ (T : Over (Spec (.of k))) (f : T ⟶ M.J),
    (∃ a : T ⟶ Over.mk (openSet.ι ≫ M.J.hom), a ≫ Over.homMk openSet.ι = f) ↔
      IsLineBundle (familyPullback C M.J T M.F f)

variable
  [HasDerivedPullbacks.{0}] [HasDerivedScalarExtensions.{0}] [HasDerivedPushforwards.{0}]
  [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
  (S : AffineSources) (A : DeterminantSystem S)
  (C : Over (Spec (.of k))) [IsProperCurve C.hom] [TorsionFreeRestrictions C.left]
  (q q' : Polarization C.left) (s : SmoothMarking C)
  (M : FineCompactifiedJacobian C q s) (N : FineCompactifiedJacobian C q' s)
  (L : LineLocus C q s M) (L' : LineLocus C q' s N)

abbrev mixedBase := prod M.J N.J

def bigOpen : (mixedBase C q q' s M N).left.Opens :=
  (prod.fst : mixedBase C q q' s M N ⟶ M.J).left ⁻¹ᵁ L.openSet ⊔
    (prod.snd : mixedBase C q q' s M N ⟶ N.J).left ⁻¹ᵁ L'.openSet

def openBase : Over (Spec (.of k)) :=
  Over.mk ((bigOpen C q q' s M N L L').ι ≫ (mixedBase C q q' s M N).hom)

def openInclusion : openBase C q q' s M N L L' ⟶ mixedBase C q q' s M N :=
  Over.homMk (bigOpen C q q' s M N L L').ι rfl

def firstSheaf : (prod C (openBase C q q' s M N L L')).left.Modules :=
  familyPullback C M.J (openBase C q q' s M N L L') M.F
    (openInclusion C q q' s M N L L' ≫ prod.fst)

def secondSheaf : (prod C (openBase C q q' s M N L L')).left.Modules :=
  familyPullback C N.J (openBase C q q' s M N L L') N.F
    (openInclusion C q q' s M N L L' ≫ prod.snd)

def projection : (prod C (openBase C q q' s M N L L')).left ⟶
    (openBase C q q' s M N L L').left :=
  (prod.snd : prod C (openBase C q q' s M N L L') ⟶ openBase C q q' s M N L L').left

structure OpenCohomologyData where
  first : IsPerfectTwoTermOn
    ((cohomologyObject (projection C q q' s M N L L') (firstSheaf C q q' s M N L L'))⟦(1 : ℤ)⟧)
  second : IsPerfectTwoTermOn
    ((cohomologyObject (projection C q q' s M N L L') (secondSheaf C q q' s M N L L'))⟦(1 : ℤ)⟧)
  tensor : IsPerfectTwoTermOn
    ((cohomologyObject (projection C q q' s M N L L')
      (moduleTensor (prod C (openBase C q q' s M N L L')).left
        (firstSheaf C q q' s M N L L') (secondSheaf C q q' s M N L L')))⟦(1 : ℤ)⟧)

variable (D : OpenCohomologyData C q q' s M N L L')

def openPoincare : (openBase C q q' s M N L L').left.Modules :=
  moduleTensor (openBase C q q' s M N L L').left
    (dualModule (openBase C q q' s M N L L').left
      (determinantOfCohomology A (projection C q q' s M N L L')
        (moduleTensor (prod C (openBase C q q' s M N L L')).left
          (firstSheaf C q q' s M N L L') (secondSheaf C q q' s M N L L')) D.tensor).line)
    (moduleTensor (openBase C q q' s M N L L').left
      (determinantOfCohomology A (projection C q q' s M N L L')
        (firstSheaf C q q' s M N L L') D.first).line
      (determinantOfCohomology A (projection C q q' s M N L L')
        (secondSheaf C q q' s M N L L') D.second).line)

def mixedKernelModule : (mixedBase C q q' s M N).left.Modules :=
  (Scheme.Modules.pushforward (bigOpen C q q' s M N L L').ι).obj
    (openPoincare S A C q q' s M N L L' D)

def transposedDual : (prod N.J M.J).left.Modules :=
  (Scheme.Modules.pullback (prod.lift (prod.snd : prod N.J M.J ⟶ M.J)
    (prod.fst : prod N.J M.J ⟶ N.J)).left).obj
      (dualModule (mixedBase C q q' s M N).left (mixedKernelModule S A C q q' s M N L L' D))

/-- Only the canonical product/fibre-product coordinate identifications;
equivalence and inverse identities are separate theorem/construction targets. -/
structure ProductCoordinates where
  forward : (prod M.J N.J).left ≅ pullback M.J.hom N.J.hom
  forward_fst : forward.hom ≫ pullback.fst M.J.hom N.J.hom =
    (prod.fst : prod M.J N.J ⟶ M.J).left
  forward_snd : forward.hom ≫ pullback.snd M.J.hom N.J.hom =
    (prod.snd : prod M.J N.J ⟶ N.J).left
  reverse : (prod N.J M.J).left ≅ pullback N.J.hom M.J.hom
  reverse_fst : reverse.hom ≫ pullback.fst N.J.hom M.J.hom =
    (prod.fst : prod N.J M.J ⟶ N.J).left
  reverse_snd : reverse.hom ≫ pullback.snd N.J.hom M.J.hom =
    (prod.snd : prod N.J M.J ⟶ M.J).left

variable (P : ProductCoordinates C q q' s M N)

def forwardKernel : FourierMukai.D (pullback M.J.hom N.J.hom) :=
  singleModule ((Scheme.Modules.pullback P.forward.inv).obj
    (mixedKernelModule S A C q q' s M N L L' D))

/-- The reverse kernel: the transposed dual, shifted by `h¹(C, 𝒪_C)`, which is the dimension of
the compactified Jacobian (its `dimension` field), the shift of the inverse Fourier–Mukai kernel.
For a reduced connected proper curve over an algebraically closed field, where
`H⁰(C, 𝒪_C) = k`, this is the arithmetic genus `p_a(C) = h¹ - h⁰ + 1`. -/
def reverseKernel : FourierMukai.D (pullback N.J.hom M.J.hom) :=
  (singleModule ((Scheme.Modules.pullback P.reverse.inv).obj
    (transposedDual S A C q q' s M N L L' D)))⟦(Module.finrank k
      (cohomology C.hom (structureModule C.left) 1) : ℤ)⟧

def bounded (X : Scheme.{0}) (K : FourierMukai.D X) : Prop :=
  ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj K)

def boundedQuasicoherent (X : Scheme.{0}) : ObjectProperty (FourierMukai.D X) :=
  fun K => quasicoherent X K ∧ bounded X K

abbrev BoundedQCoh (X : Scheme.{0}) := (boundedQuasicoherent X).FullSubcategory
/-- Bounded complexes with coherent cohomology (`BoundedCoherent.boundedCoherent`). -/
abbrev BoundedCoh (X : Scheme.{0}) := (BoundedCoherent.boundedCoherent X).FullSubcategory

variable [HasDerivedTensors.{0}]

/-- The actual forward/inverse Fourier--Mukai restrictions, as a target. -/
structure MixedFourierMukaiEquivalence where
  quasicoherent : BoundedQCoh M.J.left ≌ BoundedQCoh N.J.left
  quasicoherent_forward : quasicoherent.functor ⋙ (boundedQuasicoherent N.J.left).ι ≅
    (boundedQuasicoherent M.J.left).ι ⋙
      fourierMukai M.J.hom N.J.hom (forwardKernel S A C q q' s M N L L' D P)
  quasicoherent_reverse : quasicoherent.inverse ⋙ (boundedQuasicoherent M.J.left).ι ≅
    (boundedQuasicoherent N.J.left).ι ⋙
      fourierMukai N.J.hom M.J.hom (reverseKernel S A C q q' s M N L L' D P)
  coherent : BoundedCoh M.J.left ≌ BoundedCoh N.J.left
  coherent_forward : coherent.functor ⋙ (BoundedCoherent.boundedCoherent N.J.left).ι ≅
    (BoundedCoherent.boundedCoherent M.J.left).ι ⋙
      fourierMukai M.J.hom N.J.hom (forwardKernel S A C q q' s M N L L' D P)
  coherent_reverse : coherent.inverse ⋙ (BoundedCoherent.boundedCoherent M.J.left).ι ≅
    (BoundedCoherent.boundedCoherent N.J.left).ι ⋙
      fourierMukai N.J.hom M.J.hom (reverseKernel S A C q q' s M N L L' D P)

end MathlibExt.AlgebraicGeometry.MixedReducedPoincareKernels
