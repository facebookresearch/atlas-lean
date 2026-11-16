/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import MathlibExt.AlgebraicGeometry.CompactifiedPoincareKernels

@[expose] public section

/-!
# Compactified Poincaré extension and inverse kernels

This integral planar-curve packet requests the normalized open Picard
comparison, its Cohen--Macaulay factor-flat extension, and the two actual
inverse-kernel identities. The requested proofs occur in the constructor's
output; they are not assumed as background. Canonical derived operators
are explicit inputs fixed by their cochain universal properties.

Source: D. Arinkin, *Autoduality of compactified Jacobians for curves with
plane singularities*, Theorems A--C. https://arxiv.org/abs/1001.3868
For the reduced-curve extension see MRV II, Theorem A and §§4--6:
https://arxiv.org/abs/1308.0564
-/

namespace WantedExt.AlgebraicGeometry.CompactifiedPoincareKernel

open CategoryTheory _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open _root_.MathlibExt.AlgebraicGeometry.NumericalCompactifiedJacobians
open _root_.MathlibExt.AlgebraicGeometry.CompactifiedPoincareKernels

universe u

variable [MathlibExt.AlgebraicGeometry.FourierMukai.HasDerivedPullbacks.{u}]
  [MathlibExt.AlgebraicGeometry.FourierMukai.HasDerivedPushforwards.{u}]
  [MathlibExt.AlgebraicGeometry.FourierMukai.HasDerivedTensors.{u}]

/-- Arinkin's normalized compactified Poincaré kernel, with its open
universal-family comparison, factor flatness, depth and inverse identities. -/
public def_wanted compactifiedPoincareKernel
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (C : Over (Spec (.of k))) [IsProper C.hom] [IsIntegral C.left]
    (hdim : topologicalKrullDim C.left = 1)
    (planar : ∀ x : C.left, IsClosed ({x} : Set C.left) →
      Module.finrank (IsLocalRing.ResidueField (C.left.presheaf.stalk x))
        (IsLocalRing.CotangentSpace (C.left.presheaf.stalk x)) ≤ 2)
    [TorsionFreeRestrictions C.left]
    (q : Polarization C.left) (hq : totalWeight q = ((1 - (genus C.hom : ℤ) : ℤ) : ℚ))
    (s : SmoothMarking C) (M : FineCompactifiedJacobian C q s) :
    PoincareKernelModel C q s M

end WantedExt.AlgebraicGeometry.CompactifiedPoincareKernel
