/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
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

/-- **Moduli of stable bundles on a curve in the coprime case.** Let $k$ be an algebraically closed
field of characteristic zero, $C$ a smooth proper integral curve over $k$ of genus $g \geq 2$, and
$r > 0$ and $d$ integers with $\gcd(r, d) = 1$. Then there is a proper, smooth, geometrically
connected $k$-scheme $M$ of dimension $r^2(g - 1) + 1$ with a universal bundle on $C \times M$, a
family of stable bundles of rank $r$ and degree $d$, such that every such family over a $k$-scheme
$T$ of finite type is isomorphic to the pullback of the universal bundle along a unique map
$T \to M$, tensored with the pullback of some line bundle on $T$ (`StableModuliModel`). -/
public def_wanted stableBundleModuli
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (C : Over (Spec (.of k))) [IsIntegral C.left] [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom]
    (hgenus : 2 ≤ genus C.hom) (r : ℕ) (hr : 0 < r) (d : ℤ)
    (coprime : Nat.gcd r d.natAbs = 1) : StableModuliModel C r hr d

end WantedExt.AlgebraicGeometry.StableBundleModuli
