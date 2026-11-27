/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FrobeniusTraceSections
public import Batteries.Util.ProofWanted

/-!
# Sheaf comparison for the actual indexed big-test ideal

Schwede arXiv0901.1154v4, Definition 2.12 and its localization theorem.
The input trace system is the fixed boundary Frobenius counit, indexed by
every actual admissible positive exponent. Local maps are computed from
genuine Cartier generators. The target ideal is pinned on every such
affine frame to the actual compatible-ideal infimum.

That infimum is nonzero on every nonempty affine frame where some trace of the
family is nonzero (`localTestInfimum_ne_bot`): it contains the big test ideal of
that trace, which is nonzero by Schwede, *F-adjunction*, Proposition 4.8 (i), for an
F-finite normal domain. With `localTestInfimum_isLeast` it is then the least nonzero
compatible ideal, so the comparison sheaf is the big test ideal.

Generic compatible quotients/splittings and ordinary tensor/projection
formula are completed source integration inputs, not requested again.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FrobeniusTraceSections

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.FrobeniusGeometry
open MathlibExt.AlgebraicGeometry.DualizingFrobeniusInterfaces
open MathlibExt.AlgebraicGeometry.BoundaryFrobeniusTraces
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

def_wanted bigTestIdealSheafComparison
    {k : Type} [Field k] {n : ℕ} (V : NormalVariety k n) (p : ℕ) [Fact p.Prime]
    [CharP k p]
    [∀ q : PrimePoint V, IsDiscreteValuationRing (LocalRing V q.val)]
    [HasDerivedPushforwards.{0}]
    (C : CanonicalWeilReference V) (D : RealWeil V)
    (hp : IsInCharacteristic V.X.left p)
    (S : TraceSystem V C D p hp (structureModule V.X.left))
    [∀ a : AdmissibleExponent V C D p, IsFinite (iterated V.X.left p hp a.val)]
    (A : TraceTrivializingCover V C D p hp S) :
    TestIdealComparison V C D p hp S A

/-- **Nonzero infimum of the nonzero ideals compatible with Frobenius traces.** Let $p$ be a prime,
$k$ a field of characteristic $p$ and $V$ a normal variety over $k$ of dimension $n$ whose local
rings at codimension-one points are discrete valuation rings, with a chosen canonical divisor
(`CanonicalWeilReference`), an $\mathbb{R}$-divisor $D$, and a trace system $S$ for the pair with
coefficients in $\mathcal{O}_V$: traces $\varphi_e$ for the admissible exponents $e$. Assume that
derived direct images of module sheaves exist (`HasDerivedPushforwards`) and that the $e$-th
iterated Frobenius of $V$ is finite for every admissible $e$. Let $U$ be a nonempty affine open
subset of $V$ with local trace frames on which some $\varphi_e$ is nonzero. Then the infimum of the
nonzero ideals of $\Gamma(U, \mathcal{O}_V)$ compatible with every $\varphi_e$ is nonzero
(Schwede, *F-adjunction*, Proposition 4.8 (i)). -/
theorem_wanted localTestInfimum_ne_bot
    {k : Type} [Field k] {n : ℕ} (V : NormalVariety k n) (p : ℕ) [Fact p.Prime]
    [CharP k p]
    [∀ q : PrimePoint V, IsDiscreteValuationRing (LocalRing V q.val)]
    [HasDerivedPushforwards.{0}]
    (C : CanonicalWeilReference V) (D : RealWeil V)
    (hp : IsInCharacteristic V.X.left p)
    (S : TraceSystem V C D p hp (structureModule V.X.left))
    [∀ a : AdmissibleExponent V C D p, IsFinite (iterated V.X.left p hp a.val)]
    (U : V.X.left.affineOpens) (hU : (U.val : Set V.X.left).Nonempty)
    (A : LocalFrames V C D p hp S U.val)
    (hnonzero : ∃ a : AdmissibleExponent V C D p,
      letI := S.adjoints a
      (affineTrace V C D p hp a.val (S.identification a) (boundaryData V C D p a)
        (A a)).toAddMonoidHom ≠ 0) :
    localTestInfimum V C D p hp S U.val A ≠ ⊥

end MathlibExt.AlgebraicGeometry.FrobeniusTraceSections
