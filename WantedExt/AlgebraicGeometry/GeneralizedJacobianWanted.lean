/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.Topology.KrullDimension
public import MathlibExt.AlgebraicGeometry.PointedPicardFamilies

@[expose] public section

/-!
# Generalized Jacobians of pointed reduced curves

The request extends the pointed smooth-curve Picard interface to reduced
connected proper curves. The group need not be proper. Its dimension is
the actual coherent arithmetic genus, and its normalized universal family
represents Picard zero on arbitrary parameter schemes.

Source: Bosch--Lütkebohmert--Raynaud, *Néron Models*, Chapter 9,
generalized Jacobians and the relative Picard functor. See also SGA 6,
Exposé XII, and Stacks Project, Tag 0D25.
https://stacks.math.columbia.edu/tag/0D25
-/

namespace WantedExt.AlgebraicGeometry.GeneralizedJacobian

open CategoryTheory CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry.PointedPicardFamilies

universe u

/-- Picard zero of a reduced proper connected curve, with its normalized
universal bundle and all-test-scheme representing property. -/
public def_wanted generalizedJacobian
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (C : Over (Spec (.of k))) [IsProper C.hom]
    [GeometricallyReduced C.hom] [GeometricallyConnected C.hom]
    (hdim : topologicalKrullDim C.left = 1)
    (p : 𝟙_ (Over (Spec (.of k))) ⟶ C) : PicardZeroModel C p

end WantedExt.AlgebraicGeometry.GeneralizedJacobian
