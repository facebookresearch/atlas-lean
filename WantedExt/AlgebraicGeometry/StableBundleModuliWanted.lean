/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.Data.Int.GCD
public import MathlibExt.AlgebraicGeometry.StableBundleModuli

@[expose] public section

/-!
# Coprime stable-bundle moduli on curves

For rank and degree coprime, stability equals semistability and the proper
moduli has a global universal bundle. The universal property retains base
line-bundle twists. No HN existence theorem is duplicated here.

Source: Huybrechts--Lehn, The Geometry of Moduli Spaces of Sheaves,
Chapters 4 and 6. https://doi.org/10.1017/CBO9780511711985
-/

namespace WantedExt.AlgebraicGeometry.StableBundleModuli

open CategoryTheory _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open _root_.MathlibExt.AlgebraicGeometry.StableBundleModuli

universe u

/-- Proper smooth rank-r degree-d stable-bundle moduli with universal bundle
in the coprime case. -/
public def_wanted stableBundleModuli
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (hgenus : 2 ≤ genus C.hom) (r : ℕ) (hr : 0 < r) (d : ℤ)
    (coprime : Nat.gcd r d.natAbs = 1) : StableModuliModel C r d

end WantedExt.AlgebraicGeometry.StableBundleModuli
