/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies

@[expose] public section

/-!
# Dual abelian varieties and their normalized Poincaré family

The request is for the Picard-zero representative of an arbitrary abelian
variety, with its actual line-bundle family and universal parameter maps.
The construction records families over test schemes, including nonreduced
schemes, rather than only a correspondence on rational points.

Source: J. S. Milne, *Abelian Varieties*, §9, duality and the Poincaré
sheaf. https://www.jmilne.org/math/CourseNotes/AV.pdf
See also Bosch--Lütkebohmert--Raynaud, *Néron Models*, Chapter 8.
-/

namespace WantedExt.AlgebraicGeometry.DualAbelianVariety

open CategoryTheory _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies

universe u

/-- The dual abelian variety represents normalized algebraically trivial
line-bundle families, with the displayed Poincaré universal property. -/
public def_wanted dualAbelianVariety
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom] :
    DualAbelianVarietyModel A

end WantedExt.AlgebraicGeometry.DualAbelianVariety
