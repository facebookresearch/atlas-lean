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

/-- A locally free bundle has the geometric, frame-normalized trace map. -/
public def_wanted bundle_trace (X : Scheme.{u}) (E : X.Modules) (r : ℕ)
    (hE : IsVectorBundle E r) : TraceData X E r

end WantedExt.AlgebraicGeometry.BundleTraceWanted
