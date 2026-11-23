/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.WittLatticeFamilies

/-!
# Bounded Witt-lattice projective representation request

Bhatt--Scholze, *Projectivity of the Witt vector affine Grassmannian*,
arXiv:1507.06490v3, Theorem1.1, p2. The displayed bounded points are
actual finite-projective W(R)-submodules of W(R)[1/p]^n lying between
p^N W(R)^n and p^(-N) W(R)^n. The geometric output is an actual perfect
F_p scheme. Its ordinary projective finite-presentation model is separate,
with a universal perfection map on all perfect scheme-valued tests.
Lattice points/naturality use the perfect output and prescribed Witt map.

Generic Grassmannian representability, polynomial Proj and native Witt
operations are source-covered prerequisites. The normalized base-change
producer (the coordinate span of a lattice is again a lattice, with its
bound) is requested separately as `wittLatticeBaseChange`, and the
representation request takes it as input; no representability conclusion
is assumed in it. General reductive groups, Satake and local-model
comparisons remain separate family interfaces.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.WittLatticeGrassmannian

open MathlibExt.AlgebraicGeometry.WittLatticeFamilies

/-- Scalar extension of Witt lattices along perfect algebra maps: the span of the coordinate
images of a lattice is again a finite projective lattice, and it keeps every bound. This is the
functoriality of the lattice description in Bhatt--Scholze, Theorem 1.1. -/
public def_wanted wittLatticeBaseChange (p : ℕ) [Fact p.Prime] (n : ℕ) : BaseChange p n

/-- The actual bounded mixed-characteristic lattice functor is projective. -/
public def_wanted boundedPerfectProjectiveRepresentation
    (p : ℕ) [Fact p.Prime] (n N : ℕ) [B : BaseChange p n] :
    Representation p n N

end WantedExt.AlgebraicGeometry.WittLatticeGrassmannian
