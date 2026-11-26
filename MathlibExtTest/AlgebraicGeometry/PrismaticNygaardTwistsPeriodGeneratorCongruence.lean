/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PrismaticNygaardTwistsPeriodGeneratorCongruence

/-!
# Period generator quotient congruence

The period generator congruence gives equality with the prime in each finite
period quotient.

References: Bhatt--Morrow--Scholze, *Topological Hochschild homology and integral p-adic Hodge
theory*, arXiv:1802.03261v2, Theorem 1.12(3)--(5), Proposition 6.5, Remark 6.6 and Section 7.4;
Bhatt--Morrow--Scholze, *Integral p-adic Hodge theory*, arXiv:1602.03148v3, Example 4.24;
Bhatt--Scholze, *Prisms and prismatic cohomology*, arXiv:1905.08229v4, Theorems 1.12--1.14.
-/

@[expose] public noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.PrismaticNygaardTwistsPeriodGeneratorCongruence

open MathlibExt.RingTheory MathlibExt.RingTheory.BoundedPrisms
open MathlibExt.AlgebraicGeometry.PrismaticBreuilKisinSeeds
open MathlibExt.AlgebraicGeometry.PrismaticPeriodFrames

example (p : ℕ) [Fact p.Prime] (P : Prism.{0} p)
    (hPerfect : Function.Bijective (DeltaRing.frobenius p P.ring))
    (epsilon : P.ring) (hUnit : IsUnit epsilon)
    (hTeichmuller : DeltaRing.frobenius p P.ring epsilon = epsilon ^ p)
    (hTheta : Ideal.Quotient.mk P.ideal epsilon = 1)
    (hIdeal : P.ideal = Ideal.span {xi p P hPerfect epsilon}) (n : ℕ) :
    Ideal.Quotient.mk (periodIdeal p P n)
      (phiPower p P (n + 2) (xi p P hPerfect epsilon)) =
        (p : P.ring ⧸ periodIdeal p P n) := by
  apply sub_eq_zero.mp
  have h := WantedExt.AlgebraicGeometry.PrismaticNygaardTwists.periodGeneratorCongruence
    p P hPerfect epsilon hUnit hTeichmuller hTheta hIdeal n
  simpa only [map_sub, map_natCast] using Ideal.Quotient.eq_zero_iff_mem.mpr h

end MathlibExtTest.AlgebraicGeometry.PrismaticNygaardTwistsPeriodGeneratorCongruence
