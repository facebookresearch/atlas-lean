/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Under CH, Menger-bounded groups need not be Scheepers-bounded (Tsaban, Problem 10.2(1))

B. Tsaban, Selection principles and special sets of reals, Problem 10.2 (Machura and Tsaban): is
`S₁(Ω_nbd, Ω) = S_fin(O_nbd, O)` for separable metrizable groups? Specifically: (1) does the
Continuum Hypothesis imply the existence of a separable metrizable group `G` satisfying
`S_fin(O_nbd, O)` but not `S₁(Ω_nbd, Ω)`? (2) Is it consistent that `S_fin(O_nbd, O) = S₁(Ω_nbd, Ω)`
for separable metrizable groups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.SetTheory.Cardinal.Continuum
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Metrizable.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.MengerBoundedNotScheepersBoundedAMR133Problem0039Wanted

/-!
Source: B. Tsaban, Selection principles and special sets of reals, in Open Problems in Topology II
(E. Pearl, ed.), Elsevier 2007, 91-108; revised version arXiv:math/0609601, Problem 10.2, part (1)
(M. Machura and B. Tsaban). UnsolvedMath record UM-00800613 (`AMR-133-0039`), dataset
ulamai/UnsolvedMath v1.8.0.

`S_fin(O_nbd, O)` is Menger-boundedness and `S₁(Ω_nbd, Ω)` Scheepers-boundedness, stated as in
Machura, Shelah and Tsaban, Definition 1 (Okunev, Kočinac): for every sequence of neighbourhoods
`Uₙ` of the unit there are finite `Fₙ ⊆ G` with `G = ⋃ₙ Fₙ Uₙ`, respectively with every finite
subset of `G` inside some `Fₙ Uₙ`. The source's `Ω_nbd` excludes neighbourhoods `U` with `F U = G`
for a finite `F`; such a `Uₙ` makes `Fₙ Uₙ = G` available in the Kočinac form, so the two forms
agree. CH is `𝔠 = ℵ₁`. Groups are types in `Type` with group, topology and topological-group
structure bound by the existential. `IsMengerBounded` has the same body as `IsMengerBounded` in the
OpenConjectures entry `AMR133Problem38` (WantedExt cannot import OpenConjectures).
-/

open scoped Pointwise Topology

/-- `G` is Menger-bounded (Okunev's `o`-boundedness, `S_fin(O_nbd, O)`): for every sequence of
neighbourhoods `Uₙ` of `1` there are finite sets `Fₙ ⊆ G` with `G = ⋃ₙ Fₙ Uₙ`. -/
def IsMengerBounded (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ U : ℕ → Set G, (∀ n, U n ∈ 𝓝 (1 : G)) →
    ∃ F : ℕ → Finset G, ⋃ n, (F n : Set G) * U n = Set.univ

/-- `G` is Scheepers-bounded (Kočinac, `S₁(Ω_nbd, Ω)`): for every sequence of neighbourhoods `Uₙ`
of `1` there are finite sets `Fₙ ⊆ G` such that every finite subset of `G` lies in some `Fₙ Uₙ`. -/
def IsScheepersBounded (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ U : ℕ → Set G, (∀ n, U n ∈ 𝓝 (1 : G)) →
    ∃ F : ℕ → Finset G, ∀ E : Finset G, ∃ n, (E : Set G) ⊆ (F n : Set G) * U n

/-- Tsaban, Problem 10.2(1) (Machura and Tsaban): the Continuum Hypothesis implies that some
separable metrizable group is Menger-bounded but not Scheepers-bounded. -/
def chMengerBoundedNotScheepersBounded : Prop :=
  (Cardinal.continuum : Cardinal.{0}) = Cardinal.aleph 1 →
    ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G) (_ : IsTopologicalGroup G),
      TopologicalSpace.SeparableSpace G ∧ TopologicalSpace.MetrizableSpace G ∧
        IsMengerBounded G ∧ ¬ IsScheepersBounded G

/--
Resolved true: under CH, Machura, Shelah and Tsaban constructed a Menger-bounded subgroup of the
Baer-Specker group `ℤ^ℕ` (a separable metrizable group) whose square is not Menger-bounded, so it is
not Scheepers-bounded; the problem list's update records 'Yes' for part (1). Source: B. Tsaban,
Selection principles and special sets of reals, in Open Problems in Topology II (E. Pearl, ed.),
Elsevier 2007, 91-108; revised version arXiv:math/0609601, Problem 10.2, part (1) (M. Machura and B.
Tsaban); resolution: M. Machura, S. Shelah and B. Tsaban, Squares of Menger-bounded groups, Trans.
Amer. Math. Soc. 362 (2010), 1751-1764, doi:10.1090/S0002-9947-09-05169-1, arXiv:math/0611353,
Abstract: 'Using the Continuum Hypothesis, we prove that there is a Menger-bounded (also called
o-bounded) subgroup of the Baer-Specker group Z^N, whose square is not Menger-bounded', which
'implies that Menger-bounded groups need not be Scheepers-bounded'; the problem list's update
records 'Yes' for (1), https://arxiv.org/abs/math/0611353.
-/
public theorem_wanted chMengerBoundedNotScheepersBounded_holds : chMengerBoundedNotScheepersBounded

end MathlibExt.GroupTheory.MengerBoundedNotScheepersBoundedAMR133Problem0039Wanted
