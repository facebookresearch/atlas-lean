/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import MathlibExt.AlgebraicGeometry.NumericalCompactifiedJacobians

@[expose] public section

/-!
# Fine compactified Jacobians of reduced planar curves

Numerical stability is the actual Euler-characteristic subcurve inequality.
The torsion-free quotient system is separately requested and characterized
by its universal property. The compactification is a fine moduli object
with its normalized universal sheaf, not an unconstrained named carrier.

Sources: Esteves, *Compactifying the relative Jacobian over families of
reduced curves*; Melo--Rapagnetta--Viviani, *Fine compactified Jacobians
of reduced curves*, Theorem A and §§2,5.
https://arxiv.org/abs/1406.2299
-/

namespace WantedExt.AlgebraicGeometry.FineCompactifiedJacobians

open CategoryTheory _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry.NumericalCompactifiedJacobians
open _root_.MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

universe u

/-- Construct the canonical maximal torsion-free restrictions. -/
public instance_wanted torsionFreeRestrictions
    (k : Type u) [Field k] [IsAlgClosed k]
    (C : Over (Spec (.of k))) [IsProper C.hom] [IsReduced C.left]
    (hdim : topologicalKrullDim C.left = 1) : TorsionFreeRestrictions C.left

/-- A general polarization of a connected reduced planar curve has a fine
projective compactified Jacobian with its normalized universal sheaf. -/
public def_wanted fineCompactifiedJacobian
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (C : Over (Spec (.of k))) [IsProper C.hom] [IsReduced C.left]
    [ConnectedSpace C.left] (hdim : topologicalKrullDim C.left = 1)
    [TorsionFreeRestrictions C.left]
    (planar : ∀ x : C.left, IsClosed ({x} : Set C.left) →
      Module.finrank (IsLocalRing.ResidueField (C.left.presheaf.stalk x))
        (IsLocalRing.CotangentSpace (C.left.presheaf.stalk x)) ≤ 2)
    (d : ℤ) (q : Polarization C.left)
    (hqDegree : totalWeight q = ((d + 1 - (genus C.hom : ℤ) : ℤ) : ℚ))
    (s : SmoothMarking C)
    (hq : IsNondegenerate C q) : FineCompactifiedJacobian C q s

end WantedExt.AlgebraicGeometry.FineCompactifiedJacobians
