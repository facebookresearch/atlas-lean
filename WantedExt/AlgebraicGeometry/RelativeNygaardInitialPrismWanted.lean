/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.PrismaticNygaardModels
public import MathlibExt.AlgebraicGeometry.LargeQuasiSyntomicAlgebras

/-!
# Universal relative prismatic algebra on the large quasisyntomic basis

Bhatt--Scholze, arXiv:1905.08229v4, Theorem 15.2(1), p102:
for every large quasisyntomic residue algebra the relative prismatic
algebra is an actual initial delta-prism lift. Base-module completeness
uses the ordinary source scalar-restriction integration input.

The companion completed core defines the actual derived relative
Frobenius, its unit-normalized completion factor, and the defining
Nygaard preimage submodules. Associated graded, Breuil-Kisin twists,
syntomic fibers and qsyn descent remain separate comparisons; they are
not claimed by this universal-algebra component.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RelativeNygaardInitialPrism

open MathlibExt.RingTheory.BoundedPrisms
open MathlibExt.RingTheory.DerivedModuleScalarOperations
open MathlibExt.AlgebraicGeometry.PrismaticNygaardModels
open MathlibExt.AlgebraicGeometry.LargeQuasiSyntomicAlgebras

/-- **The initial prism of a large quasisyntomic algebra.** Let $p$ be a prime, $(A, I)$ a bounded
prism and $S$ a large quasisyntomic $A/I$-algebra (`LargeQuasiSyntomic`: $p$-complete,
$p$-completely flat, with cotangent complex of $p$-adic Tor amplitude in $[-1, 0]$, and a quotient
of the $p$-completed $A/I$-algebra of compatible $p$-power roots of a set of variables), with the
given derived tensor product on $S$-modules (`HasTensor`). Then the category of bounded prisms
$(B, J)$ over $(A, I)$ with an $A/I$-algebra map $S \to B/J$ has an initial object (`InitialLift`;
Bhatt–Scholze, Theorem 15.2(1)). -/
public def_wanted initialPrismLift
    (p : ℕ) [Fact p.Prime] (P : Prism.{0} p)
    (S : Type) [CommRing S] [Algebra P.Residue S] [HasTensor S]
    (h : LargeQuasiSyntomic p P.Residue S) : InitialLift p P S

end WantedExt.AlgebraicGeometry.RelativeNygaardInitialPrism
