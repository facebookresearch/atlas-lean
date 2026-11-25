/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RegularGrothendieckSteinberg

/-!
# Normalized regular type A1 eigenline/spectral realization

Construct the homeomorphism from the actual Grothendieck eigenline incidence
to the actual characteristic-root double cover. Its forward map is fixed by
the projection; its inverse projector is fixed by the literal Q Q*/tr(Q Q*)
formula. This includes the continuous family of eigenlines for arbitrary
non-normal regular-semisimple matrices.

The resulting Weyl involution is the completed spectral deck involution
transported through that normalized homeomorphism. The spectral Steinberg
convolution, reflection-square law and actual rational coefficient/direct-
image data are completed support. Generic characteristic-root/cardinality,
finite convolution and finite-group character-theory primitives are covered
and excluded as new requests. Full nilpotent Springer fibres, intermediate-
extension comparisons and Satake remain residual scope.

Reference: Chriss--Ginzburg, *Representation Theory and Complex Geometry*,
Chapter 3; Ginzburg, https://arxiv.org/abs/math/9802004v3,
§9, Proposition 9.3, printed pp.34--35. Hermitian spectral theorem primitives
apply to the projector;
the matrix parameter in this interface is an arbitrary regular-semisimple
complex matrix.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RegularGrothendieckSteinbergWanted

open MathlibExt.AlgebraicGeometry.RegularGrothendieckSteinberg

/-- The canonical family comparison fixes both the spectral projection and
the actual Hermitian eigenprojector inverse formula. -/
public def_wanted eigenlineSpectralRealization : EigenlineSpectralComparison

end WantedExt.AlgebraicGeometry.RegularGrothendieckSteinbergWanted
