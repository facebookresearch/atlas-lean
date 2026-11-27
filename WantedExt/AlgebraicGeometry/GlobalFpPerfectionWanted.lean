/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.GlobalFpPerfectionModels

/-!
# Native global perfection from the affine Frobenius direct-colimit source

The whole affine objects/maps and zero-stage projection are already
fixed. The global source extends them on every actual open chart,
retaining zero rings, empty schemes and the literal perfect-source
universal map. No Perf descent theorem is an input.

Source: Bhatt--Mathew1807.04725v4, Theorem5.16; Stacks perfection.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicGeometry.GlobalFpPerfectionModels

open FrobeniusPerfectionModels

/-- **The perfection of $\mathbb{F}_p$-schemes.** For a prime $p$ and the Frobenius
$r \mapsto r^p$ of $\mathbb{F}_p$-algebras (`FrobeniusSource p`): an endofunctor
$X \mapsto X_{\mathrm{perf}}$ of $\mathbb{F}_p$-schemes with a natural projection
$X_{\mathrm{perf}} \to X$ such that, for every $\mathbb{F}_p$-algebra $A$,
$(\operatorname{Spec} A)_{\mathrm{perf}}$ is identified, naturally in $A$ and compatibly with the
projection, with $\operatorname{Spec}$ of the direct colimit $A_{\mathrm{perf}}$ of
$A \to A \to \cdots$ along Frobenius; every $X_{\mathrm{perf}}$ is perfect (Frobenius is bijective
on the coordinate ring of every affine open); the square formed by an open immersion $Y \to X$, its
perfection and the two projections is cartesian; and every morphism from a perfect
$\mathbb{F}_p$-scheme to $X$ factors uniquely through the projection
(`GlobalPerfectionSource F`). -/
def_wanted native_global_fp_perfection {p : ℕ} (F : FrobeniusSource p) : GlobalPerfectionSource F

end MathlibExt.AlgebraicGeometry.GlobalFpPerfectionModels
