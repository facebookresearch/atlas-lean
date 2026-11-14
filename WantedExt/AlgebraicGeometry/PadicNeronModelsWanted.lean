/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import MathlibExt.AlgebraicGeometry.PadicNeronModels

/-!
# Néron models of actual p-adic abelian varieties

The generic object is a proper smooth geometrically connected commutative
group scheme over `ℚ_p`, expressed with actual internal group operations in
the scheme slice. The requested integral model lives over `Spec ℤ_p` and
satisfies the universal extension property for every smooth test scheme.
Its generic fibre, special fibre and reduction maps are concrete pullbacks.

Reference: Bosch–Lütkebohmert–Raynaud, *Néron Models*, Chapter 1.
https://doi.org/10.1007/978-3-642-51438-8
Public statement: Conrad, *Néron models, Tamagawa factors, and
Tate–Shafarevich groups*, Theorem 1.1 and Remark 1.3.
https://math.stanford.edu/~conrad/BSDseminar/Notes/L3.pdf
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.PadicNeronModels

open CategoryTheory CategoryTheory.MonObj
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PadicNeronModels

/-- Construct the actual Néron model of the given p-adic abelian variety. -/
public def_wanted abelianVarietyNeronModel
    (p : ℕ) [Fact p.Prime] (A : Over (genericBase p))
    [GrpObj A] [IsCommMonObj A] [IsProper A.hom] [Smooth A.hom]
    [GeometricallyConnected A.hom] : NeronModel p A

end WantedExt.AlgebraicGeometry.PadicNeronModels
