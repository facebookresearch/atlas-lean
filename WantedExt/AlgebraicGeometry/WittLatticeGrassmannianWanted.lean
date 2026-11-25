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

/-- Base change of Witt lattices (functoriality of the lattice description in Bhatt–Scholze,
Theorem 1.1): for a prime $p$ and $n ∈ ℕ$, an operation (`BaseChange`) that sends a map $f : R → S$
of perfect $𝔽_p$-algebras and a Witt lattice $L ⊆ W(R)[1/p]^n$ to a Witt lattice over $S$ whose
module is the $W(S)$-span of the coordinatewise images of $L$, compatibly with identities and
composition, and preserving every bound $p^N W^n ⊆ L ⊆ p^{-N} W^n$. -/
public def_wanted wittLatticeBaseChange (p : ℕ) [Fact p.Prime] (n : ℕ) : BaseChange p n

/-- Projectivity of the Witt vector affine Grassmannian (Bhatt–Scholze, Theorem 1.1): for a prime
$p$, $n, N ∈ ℕ$ and the given base change of Witt lattices (`BaseChange`): a projective
$𝔽_p$-scheme $X$ of finite presentation with a perfection $X^{perf}$ (`PerfectionModel`), together
with bijections, natural in the perfect $𝔽_p$-algebra $R$ for that base change, between the Witt
lattices $L ⊆ W(R)[1/p]^n$ with $p^N W(R)^n ⊆ L ⊆ p^{-N} W(R)^n$ and the morphisms
$\mathrm{Spec}\,R → X^{perf}$ over $𝔽_p$ (`Representation`). -/
public def_wanted boundedPerfectProjectiveRepresentation
    (p : ℕ) [Fact p.Prime] (n N : ℕ) [B : BaseChange p n] :
    Representation p n N

end WantedExt.AlgebraicGeometry.WittLatticeGrassmannian
