/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A non-indicable left-orderable group with vanishing second bounded cohomology (Navas, Question 8)

Navas, Question 8: does there exist a finitely generated, left-orderable group `G` with no
nontrivial homomorphism into `ℤ` and trivial bounded cohomology group `H²_b(G, ℝ)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.GroupTheory.Finiteness
public import WantedExt.GroupTheory.UniqueProductNotLeftOrderableKourovka15Problem49Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.LeftOrderableVanishingBoundedCohomologyAMR120Problem0008Wanted

/-!
Source: A. Navas, Group actions on 1-manifolds: a list of very concrete open questions, Proceedings
of the International Congress of Mathematicians 2018, Vol. 2, World Scientific (2018), 2029-2056,
arXiv:1712.06462, Question 8. UnsolvedMath record UM-00800294 (`AMR-120-0008`), dataset
ulamai/UnsolvedMath v1.8.0.

`H²_b(G; ℝ) = 0` is stated with inhomogeneous cochains and trivial coefficients: every bounded `c :
G → G → ℝ` with `c h k - c (g h) k + c g (h k) - c g h = 0` is `f h - f (g h) + f g` for a bounded
`f : G → ℝ`. Left-orderable is `IsLeftOrderable` from the Kourovka 15.49 module (a linear order
invariant under left multiplication). `G` is required to be nontrivial: the trivial group satisfies
every other condition.
-/

open MathlibExt.GroupTheory.UniqueProductNotLeftOrderableKourovka15Problem49Wanted

/-- A bounded real 2-cocycle of `G` with trivial coefficients, in inhomogeneous form: `c` is bounded
and `c h k - c (g h) k + c g (h k) - c g h = 0` for all `g h k`. -/
def IsBoundedTwoCocycle {G : Type*} [Group G] (c : G → G → ℝ) : Prop :=
  (∃ C : ℝ, ∀ g h, |c g h| ≤ C) ∧ ∀ g h k, c h k - c (g * h) k + c g (h * k) - c g h = 0

/-- The second bounded cohomology `H²_b(G; ℝ)` (trivial real coefficients) vanishes: every bounded
2-cocycle is the coboundary `g, h ↦ f h - f (g h) + f g` of a bounded function `f : G → ℝ`. -/
def BoundedCohomologyTwoVanishes (G : Type*) [Group G] : Prop :=
  ∀ c : G → G → ℝ, IsBoundedTwoCocycle c →
    ∃ f : G → ℝ, (∃ C : ℝ, ∀ g, |f g| ≤ C) ∧ ∀ g h, c g h = f h - f (g * h) + f g

/-- Navas, Question 8: there is a finitely generated, nontrivial, left-orderable group with no
nontrivial homomorphism into `ℤ` and with `H²_b(G; ℝ) = 0`. -/
def existsLeftOrderableNonIndicableBoundedAcyclic : Prop :=
  ∃ (G : Type) (_ : Group G), Group.FG G ∧ Nontrivial G ∧ IsLeftOrderable G ∧
    (∀ φ : G →* Multiplicative ℤ, φ = 1) ∧ BoundedCohomologyTwoVanishes G

/--
Resolved true: Fournier-Facio and Lodha prove that the finitely generated simple left-orderable
groups G_ρ of Hyde and Lodha have vanishing second bounded cohomology; being simple and infinite
they are nontrivial and admit no nontrivial homomorphism to ℤ. They present this as the answer to
Navas's Question 8. Source: A. Navas, Group actions on 1-manifolds: a list of very concrete open
questions, Proceedings of the International Congress of Mathematicians 2018, Vol. 2, World
Scientific (2018), 2029-2056, arXiv:1712.06462, Question 8; resolution: F. Fournier-Facio, Y. Lodha,
Second bounded cohomology of groups acting on 1-manifolds and applications to spectrum problems,
Adv. Math. 428 (2023), 109162, arXiv:2111.07931, Theorem 1.4 (H²_b(G_ρ; ℝ) = 0 for every
quasi-periodic labelling ρ, where G_ρ is the finitely generated simple left orderable group of Hyde
and Lodha), stated in §1 to answer Question 8 of Navas; also recorded in S. Nariman, M. Yazdi,
Problem list on foliations and diffeomorphism groups, arXiv:2503.18274, section 'Bounded
cohomology', https://arxiv.org/abs/2111.07931.
-/
public theorem_wanted existsLeftOrderableNonIndicableBoundedAcyclic_holds :
    existsLeftOrderableNonIndicableBoundedAcyclic

end MathlibExt.GroupTheory.LeftOrderableVanishingBoundedCohomologyAMR120Problem0008Wanted
