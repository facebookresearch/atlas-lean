/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.GameTheory.Matching.StableMechanism

/-! # Incentives of the man-optimal stable mechanism (wanted)

Roth's positive results complementing his impossibility theorem
(`MathlibExt.GameTheory.Matching.StableMechanism.not_exists_stable_strategyProof`), from A. E.
Roth, "The economics of matching: stability and incentives", *Mathematics of Operations Research*
7(4) (1982), 617–628:

* Theorem 5: in the mechanism that always yields the man-optimal stable matching, truthful
  revelation is a dominant strategy for every man. Roth's footnote 4 notes that related
  conclusions were developed independently by Dubins and Freedman (published as "Machiavelli and
  the Gale–Shapley algorithm", *Amer. Math. Monthly* 88 (1981); not consulted here).
* Theorem 6: no perfect matching, stable or not, is strictly preferred by every man to the
  man-optimal stable matching.

Roth's proofs run the men-proposing deferred-acceptance algorithm step by step; the repository's
executable algorithm is `Cslib.Algorithms.Lean.Matching.GaleShapley.gsMatching`, which is stable
and proposer-optimal, so it implements the mechanism of Theorem 5 on `Fin n`.
-/

@[expose] public section

namespace MathlibExt.GameTheory.Matching.StableMechanismIncentivesWanted

open MathlibExt.Combinatorics.Matching.GaleShapley
open MathlibExt.GameTheory.Matching.StableMechanism

/-- **Strategy-proofness of the man-optimal stable mechanism for the men** (Roth, *Math. Oper.
Res.* 7 (1982), Theorem 5; related conclusions of Dubins and Freedman are cited in its footnote
4). If a mechanism
`h` always returns the man-optimal stable matching of the stated profile, then truthful
revelation is a dominant strategy for every man. Roth states it for either side; this is the
men's side, the women's side being symmetric. Such mechanisms exist whenever the two sides have
the same size (`exists_isManOptimalStable`, and deferred acceptance on `Fin n`,
`Cslib.Algorithms.Lean.Matching.GaleShapley.exists_isManOptimalStable_mechanism`). -/
theorem_wanted isTruthfulDominantForMan_of_isManOptimalStable {M W : Type*} [Fintype M]
    [Fintype W] [DecidableEq M] (h : MatchingMechanism M W)
    (hh : ∀ mp wp, IsManOptimalStable mp wp (h mp wp)) (m : M) :
    IsTruthfulDominantForMan h m

/-- **Weak Pareto optimality of the man-optimal stable matching for the men** (Roth, *Math. Oper.
Res.* 7 (1982), Theorem 6). No perfect matching gives every man a partner he strictly prefers to
his partner in the man-optimal stable matching. The hypothesis `Nonempty M` excludes the empty
market, where "every man strictly prefers" holds vacuously. Roth's example after Corollary 5.1
shows that strong Pareto optimality fails. -/
theorem_wanted not_forall_lt_of_isManOptimalStable {M W : Type*} [Fintype M] [Fintype W]
    [Nonempty M] (mp : MPrefs M W) (wp : WPrefs M W) {μ : PerfectMatching M W}
    (hμ : IsManOptimalStable mp wp μ) (ν : PerfectMatching M W) :
    ¬ ∀ m, (mp m).lt (ν m) (μ m)

end MathlibExt.GameTheory.Matching.StableMechanismIncentivesWanted
