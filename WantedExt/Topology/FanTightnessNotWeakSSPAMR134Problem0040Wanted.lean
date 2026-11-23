/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Fan tightness of C_p(X) and the weak sequence selection property (Milestone Problem 15.3)

B. Tsaban, Selection principles in mathematics: A milestone of open problems, Problem 15.3
(Scheepers, A sequential property of `C_p(X)` and a covering property of Hurewicz, Problem 1): does
countable fan tightness of `C_p(X)` imply the weak sequence selection property?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.Topology.SelectionPrinciplesShared

@[expose] public section

namespace MathlibExt.Topology.FanTightnessNotWeakSSPAMR134Problem0040Wanted

/-!
Source: B. Tsaban, Selection principles in mathematics: A milestone of open problems, Note di
Matematica 22 (2003/2004), arXiv:math/0312182, Problem 15.3 (M. Scheepers, Proc. Amer. Math. Soc.
125 (1997), Problem 1). UnsolvedMath record UM-00800668 (`AMR-134-0040`), dataset
ulamai/UnsolvedMath v1.8.0.

Following the source's convention (Section 2.3), `X` ranges over sets of reals. `C_p(X)` is the set
of continuous real functions on `X` with the pointwise topology. Countable fan tightness is the
source's Section 15 definition (at every point). The sequence selection property asks, for every
sequence of sequences `(f^n_k)_k` in `C_p(X)` converging to `𝟎`, for indices `k_n` with `f^n_{k_n} →
𝟎`; the weak version only asks that `𝟎` be in the closure of `{f^n_{k_n} : n}`.
-/

open MathlibExt.Topology.SelectionPrinciplesShared

/-- Countable fan tightness (Arhangel'skiĭ): for every point `y` and sets `Aₙ` with `y` in the
closure of each `Aₙ`, there are finite `Fₙ ⊆ Aₙ` with `y` in the closure of `⋃ₙ Fₙ`. -/
def HasCountableFanTightness (Y : Type*) [TopologicalSpace Y] : Prop :=
  ∀ y : Y, ∀ A : ℕ → Set Y, (∀ n, y ∈ closure (A n)) →
    ∃ F : ℕ → Finset Y, (∀ n, (F n : Set Y) ⊆ A n) ∧ y ∈ closure (⋃ n, (F n : Set Y))

/-- Tsaban, Milestone Problem 15.3 (Scheepers): for every set of reals `X`, countable fan tightness
of `C_p(X)` implies the weak sequence selection property of `C_p(X)`. -/
def fanTightnessImpliesWeakSSP : Prop :=
  ∀ X : Set ℝ, HasCountableFanTightness (Cp X) → HasWeakSSP X

/--
Resolved false: Sakai proved that `C_p(X)` has the weak sequence selection property only when `X` is
zero-dimensional, so `C_p([0, 1])` lacks it, while `C_p([0, 1])` has countable fan tightness (all
finite powers of `[0, 1]` are compact; Arkhangel'skiĭ's theorem in the source's Section 15); the
problem list's Notes added in proof record the negative answer. Source: B. Tsaban, Selection
principles in mathematics: A milestone of open problems, Note di Matematica 22 (2003/2004),
arXiv:math/0312182, Problem 15.3 (M. Scheepers, Proc. Amer. Math. Soc. 125 (1997), Problem 1);
resolution: M. Sakai, The sequence selection properties of C_p(X), Topology Appl. 154 (2007),
552-560, doi:10.1016/j.topol.2006.07.008, zbMATH review Zbl 1109.54014 (T. Natkaniec): if C_p(X) has
the weak sequence selection property then X is zero-dimensional, so C_p([0,1]) does not have it,
which solves problems of Scheepers; the problem list's Notes added in proof: 'Sakai also settled
Problems 15.3 and 15.4 in the negative', https://doi.org/10.1016/j.topol.2006.07.008.
-/
public theorem_wanted fanTightnessImpliesWeakSSP_refuted : ¬ fanTightnessImpliesWeakSSP

end MathlibExt.Topology.FanTightnessNotWeakSSPAMR134Problem0040Wanted
