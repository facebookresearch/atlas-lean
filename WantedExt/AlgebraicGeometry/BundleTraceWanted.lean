/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.BundleTrace

/-!
# The normalized geometric trace needed for trace-free deformation spaces

Reference: Huybrechts--Lehn, *The Geometry of Moduli Spaces of Sheaves*,
Section 4.5. The actual internal-Hom sheaf, scalar multiplication,
trace-free kernel and cohomology maps are completed support. This request
constructs a trace obeying the affine-frame matrix and scalar normalizations;
it assumes no trace map, fixed-determinant conclusion or obstruction class.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.BundleTraceWanted

open MathlibExt.AlgebraicGeometry.BundleTrace
open MathlibExt.AlgebraicGeometry.CurveVectorBundles
open _root_.AlgebraicGeometry

universe u

/-- **The trace map of a vector bundle.** For a scheme $X$ and a sheaf $E$ of
$\mathcal{O}_X$-modules that is locally free of rank $r$ (every point has an open neighbourhood on
which $E$ is isomorphic to $\mathcal{O}^r$): a trace for $E$ (`TraceData X E r`), that is, a
morphism of $\mathcal{O}_X$-modules $\operatorname{tr} : \mathcal{E}nd(E) \to \mathcal{O}_X$ from
the internal endomorphism sheaf which, on every affine open $U$ and for every basis of $E(U)$ over
$\mathcal{O}_X(U)$ indexed by $r$ elements, sends each local endomorphism to the trace of its
matrix in that basis, and whose composite with the scalar map
$\mathcal{O}_X \to \mathcal{E}nd(E)$ is multiplication by $r$. -/
public def_wanted bundle_trace (X : Scheme.{u}) (E : X.Modules) (r : ℕ)
    (hE : IsVectorBundle E r) : TraceData X E r

end WantedExt.AlgebraicGeometry.BundleTraceWanted
