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
# Compactified Poincaré sheaf, its properties and autoduality

For an integral proper curve with planar singularities over an algebraically closed field of
characteristic zero, with a fine compactified Jacobian `J̄`, this request asks for an autodual
Poincaré-type sheaf on `J̄ × J̄`, which Arinkin's normalized Poincaré sheaf provides: a
Poincaré-kernel candidate (`PoincareKernelCandidate`: a sheaf with its line-bundle locus, open
Picard-zero family, symmetry and extension from the big open) that has Arinkin's geometric
properties (`PoincareKernelCandidate.Properties`: density of the line-bundle locus, identification
with `Pic⁰(J̄)` (Theorem B), maximal Cohen--Macaulay, flat over both factors (Theorem A)) and is a
Fourier--Mukai autoduality kernel (`PoincareKernelCandidate.IsAutodual`, Theorem C). Neither the
candidate data nor these properties single out Arinkin's sheaf (a constant classifying map with the
trivial sheaf is a candidate; and the data do not record Arinkin's determinant formula on the
line-bundle locus, so for a smooth elliptic curve the normalized Poincaré bundle and its pullback by
inversion both qualify), so the request is the existence of a candidate with both properties, a
consequence of Arinkin's Theorems A--C; it is not vacuous, since the trivial candidate fails
`Properties.betaIso`. Canonical derived operators are explicit inputs fixed by their cochain
universal properties.

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

/-- An autodual Poincaré-type sheaf on `J̄ × J̄`: a Poincaré-kernel candidate with Arinkin's
geometric properties (Theorems A and B) that is an autoduality kernel (Theorem C). Arinkin's
normalized compactified Poincaré sheaf is one. -/
public def_wanted compactifiedPoincareKernel
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (C : Over (Spec (.of k))) [IsIntegral C.left] [IsProperCurve C.hom]
    (planar : ∀ x : C.left, IsClosed ({x} : Set C.left) →
      Module.finrank (IsLocalRing.ResidueField (C.left.presheaf.stalk x))
        (IsLocalRing.CotangentSpace (C.left.presheaf.stalk x)) ≤ 2)
    [TorsionFreeRestrictions C.left]
    (q : Polarization C.left) (hq : totalWeight q = ((1 - (genus C.hom : ℤ) : ℤ) : ℚ))
    (s : SmoothMarking C) (M : FineCompactifiedJacobian C q s) :
    {K : PoincareKernelCandidate C q s M // K.Properties ∧ K.IsAutodual}

end WantedExt.AlgebraicGeometry.CompactifiedPoincareKernel
