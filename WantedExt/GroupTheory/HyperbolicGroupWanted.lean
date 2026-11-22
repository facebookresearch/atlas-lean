/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FinitelyPresentedGroup
public import MathlibExt.GroupTheory.HyperbolicGroup
public import WantedExt.GroupTheory.WordProblemSolvableShared

/-!
# Basic theorems on word-hyperbolic groups

Statements from M. Gromov, *Hyperbolic groups*, in Essays in Group Theory (S. M. Gersten, ed.),
Math. Sci. Res. Inst. Publ. 8, Springer (1987), 75-263, §1.1.D, §1.4 and §2.1-2.3, for
`Group.IsHyperbolic` (some finite generating family has a hyperbolic word metric).
-/

@[expose] public section

namespace MathlibExt.GroupTheory.HyperbolicGroupWanted

open MathlibExt.GroupTheory.WordProblemSolvableShared

/-- **Hyperbolic groups are finitely presented** (Gromov, *Hyperbolic groups*, 1987,
Corollary 2.2.A of Rips's theorem 2.2). -/
theorem_wanted isFinitelyPresented_of_isHyperbolic {G : Type*} [Group G]
    (h : Group.IsHyperbolic G) : Group.IsFinitelyPresented G

/-- **Hyperbolicity does not depend on the finite generating set** (Gromov, *Hyperbolic groups*,
1987, Corollary 2.3.E). If `G` is word-hyperbolic, then the word metric of every finite generating
family of `G` is `δ`-hyperbolic for some `δ` (depending on the family). -/
theorem_wanted isDeltaHyperbolic_of_isHyperbolic {G ι : Type*} [Group G] [Finite ι]
    (h : Group.IsHyperbolic G) (P : Group.Generators G ι) :
    ∃ δ : ℝ, @Metric.IsDeltaHyperbolic G P.normedGroup.toPseudoMetricSpace δ

/-- **Hyperbolic groups have solvable word problem** (Gromov, *Hyperbolic groups*, 1987,
Corollary 2.3.B: a linear isoperimetric inequality holds for every finite presentation, "in
particular, the word problem is solvable"; the algorithm is Dehn's). If `G` is word-hyperbolic and
`P` is a generating family indexed by `Fin n`, it is decidable by an algorithm whether a word in the
generators and their inverses represents the identity of `G`. -/
theorem_wanted wordProblemSolvable_of_isHyperbolic {G : Type*} [Group G]
    (h : Group.IsHyperbolic G) {n : ℕ} (P : Group.Generators G (Fin n)) :
    WordProblemSolvable P.lift

/-- **Free groups are `0`-hyperbolic** (Gromov, *Hyperbolic groups*, 1987, §1.1.D and §1.4: the
Cayley graph of a free group on a free basis is a simplicial tree, and simplicial trees are
`0`-hyperbolic). The word metric of `FreeGroup ι` with respect to the free basis `FreeGroup.of` is
`0`-hyperbolic. -/
theorem_wanted freeGroup_isDeltaHyperbolic_zero (ι : Type*) :
    @Metric.IsDeltaHyperbolic (FreeGroup ι)
      (⟨FreeGroup.of, FreeGroup.closure_range_of ι⟩ :
        Group.Generators (FreeGroup ι) ι).normedGroup.toPseudoMetricSpace 0

end MathlibExt.GroupTheory.HyperbolicGroupWanted
