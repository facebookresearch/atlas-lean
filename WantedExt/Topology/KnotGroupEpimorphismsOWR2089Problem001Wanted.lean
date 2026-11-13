/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Simon's conjecture on epimorphisms of knot groups (Oberwolfach Reports 43/2008)

Oberwolfach workshop Topologie (2008), Conjecture 1.1 (A. W. Reid, with M. Boileau, S. Boyer and S.
Wang; Simon's conjecture, Kirby Problem 1.12(D)): for a nontrivial knot `K ⊂ S³`, `π₁(S³ \ K)`
surjects onto only finitely many distinct knot groups.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import WantedExt.Topology.ConwayKnotShared

@[expose] public section

namespace MathlibExt.Topology.KnotGroupEpimorphismsOWR2089Problem001Wanted

/-!
Source: A. W. Reid (with M. Boileau, S. Boyer and S. Wang), in Topologie, Oberwolfach Reports 5
(2008), no. 43, p. 2427, Conjecture 1.1, DOI 10.4171/OWR/2008/43. UnsolvedMath record UM-30001045
(`OWR-2089-001`), dataset ulamai/UnsolvedMath v1.8.0.

Knots are the smooth knots `Knot` of `WantedExt.Topology.ConwayKnotShared` (smooth `2π`-periodic
immersions `ℝ → ℝ³` injective on a period); smooth knots are tame, and every tame knot type has one.
The knot group is `π₁(ℝ³ \ K)`, isomorphic to `π₁(S³ \ K)`; basepoints are arbitrary (the complement
is path-connected). 'Finitely many distinct knot groups' is up to isomorphism. The statement is made
for every knot, as Agol and Liu prove; for the unknot it is immediate.
-/

open MathlibExt.Topology.ConwayKnotShared.KnotTheory (Knot R3)

/-- The complement `ℝ³ \ K` of the knot `K`, with the subspace topology. -/
abbrev KnotComplement (K : Knot) : Type :=
  {x : R3 // x ∉ Set.range K.curve}

/-- The knot group `π₁(ℝ³ \ K, x₀)` (isomorphic to `π₁(S³ \ K)`). -/
abbrev KnotGroup (K : Knot) (x₀ : KnotComplement K) : Type :=
  FundamentalGroup (KnotComplement K) x₀

/-- Simon's conjecture (Oberwolfach Report 43/2008, p. 2427, Conjecture 1.1; Kirby Problem 1.12(D)):
a knot group surjects onto only finitely many knot groups up to isomorphism. For every knot `K`
there are finitely many knots `K₁, …, K_m` such that every knot group onto which `π₁(ℝ³ \ K)`
surjects is isomorphic to some `π₁(ℝ³ \ K_i)`. -/
def finitelyManyKnotGroupQuotients : Prop :=
  ∀ (K : Knot) (x₀ : KnotComplement K),
    ∃ (m : ℕ) (L : Fin m → Knot) (y : ∀ i, KnotComplement (L i)),
      ∀ (K' : Knot) (x₀' : KnotComplement K'),
        ∀ φ : KnotGroup K x₀ →* KnotGroup K' x₀', Function.Surjective φ →
          ∃ i, Nonempty (KnotGroup K' x₀' ≃* KnotGroup (L i) (y i))

/--
Resolved true: Agol and Liu proved that any knot group maps onto at most finitely many knot groups
(up to isomorphism), answering Simon's conjecture affirmatively; their theorem has no assumption on
the degree of the epimorphisms. Source: A. W. Reid (with M. Boileau, S. Boyer and S. Wang), in
Topologie, Oberwolfach Reports 5 (2008), no. 43, p. 2427, Conjecture 1.1, DOI 10.4171/OWR/2008/43;
resolution: I. Agol and Y. Liu, Presentation length and Simon's conjecture, J. Amer. Math. Soc. 25
(2012), arXiv:1006.5262, abstract and Corollary 1.2: any knot group maps onto at most finitely many
knot groups, which answers Simon's conjecture (Kirby Problem 1.12(D)) affirmatively,
https://arxiv.org/abs/1006.5262.
-/
public theorem_wanted finitelyManyKnotGroupQuotients_holds : finitelyManyKnotGroupQuotients

end MathlibExt.Topology.KnotGroupEpimorphismsOWR2089Problem001Wanted
