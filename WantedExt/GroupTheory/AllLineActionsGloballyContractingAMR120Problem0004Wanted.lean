/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Groups all of whose actions on the line are globally contracting (Navas, Question 4)

Navas, Question 4: does there exist an infinite, finitely generated group that acts on the real line
all of whose actions by orientation-preserving homeomorphisms of the line without global fixed
points are of type (iii)? Type (iii) (globally contracting): the action is semiconjugate to a
minimal one for which every bounded interval is sent, by well-chosen group elements, into a sequence
of intervals converging to a point.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.AllLineActionsGloballyContractingAMR120Problem0004Wanted

/-!
Source: A. Navas, Group actions on 1-manifolds: a list of very concrete open questions, Proceedings
of the International Congress of Mathematicians 2018, Vol. 2, World Scientific (2018), 2029-2056,
arXiv:1712.06462, Question 4. UnsolvedMath record UM-00800290 (`AMR-120-0004`), dataset
ulamai/UnsolvedMath v1.8.0.

Actions are homomorphisms `ρ : G →* (ℝ ≃ₜ ℝ)` with every `ρ g` monotone (orientation preserving); no
global fixed point means every `x` is moved by some `ρ g`. "Acts on the real line" is read as the
existence of one such action without global fixed points, which rules out groups (finite or torsion
ones) all of whose actions are trivial. A semiconjugacy is, as in the source, a continuous
non-decreasing proper map `φ : ℝ → ℝ` with `φ ∘ ρ g = ψ g ∘ φ` (proper: `φ → ±∞` at `±∞`); minimal
means every orbit is dense; the contraction property for a bounded interval `[a, b]` is that some
point `x` has `ψ g '' [a, b]` inside arbitrarily small neighbourhoods of `x` for suitable `g`.
-/

open Filter Topology

/-- The action `ρ : G →* (ℝ ≃ₜ ℝ)` is of type (iii) in Navas's trichotomy (globally contracting):
it is semiconjugate, through a continuous non-decreasing proper map `φ : ℝ → ℝ`
(`φ ∘ ρ g = ψ g ∘ φ`), to an action `ψ` by orientation-preserving homeomorphisms that is minimal
(every orbit is dense) and contracts every bounded interval: for each `[a, b]` there is a point `x`
such that suitable group elements send `[a, b]` into arbitrarily small neighbourhoods of `x`. -/
def IsTypeIII {G : Type*} [Group G] (ρ : G →* (ℝ ≃ₜ ℝ)) : Prop :=
  ∃ (ψ : G →* (ℝ ≃ₜ ℝ)) (φ : ℝ → ℝ), (∀ g, Monotone (ψ g)) ∧ Continuous φ ∧ Monotone φ ∧
    Tendsto φ atTop atTop ∧ Tendsto φ atBot atBot ∧ (∀ g x, φ (ρ g x) = ψ g (φ x)) ∧
    (∀ x, Dense (Set.range fun g => ψ g x)) ∧
    ∀ a b : ℝ, ∃ x : ℝ, ∀ ε > 0, ∃ g, (ψ g) '' Set.Icc a b ⊆ Set.Ioo (x - ε) (x + ε)

/-- Navas, Question 4: there is an infinite finitely generated group that acts on the real line by
orientation-preserving homeomorphisms without a global fixed point, and all of whose actions by
orientation-preserving homeomorphisms of the line without global fixed points are of type (iii). -/
def existsGroupAllLineActionsTypeIII : Prop :=
  ∃ (G : Type) (_ : Group G), Group.FG G ∧ Infinite G ∧
    (∃ ρ : G →* (ℝ ≃ₜ ℝ), (∀ g, Monotone (ρ g)) ∧ ∀ x, ∃ g, ρ g x ≠ x) ∧
    ∀ ρ : G →* (ℝ ≃ₜ ℝ), (∀ g, Monotone (ρ g)) → (∀ x, ∃ g, ρ g x ≠ x) → IsTypeIII ρ

/--
Resolved true: Hyde, Lodha, Navas and Rivas show that the finitely generated infinite simple
left-orderable groups G_ρ of Hyde and Lodha (quasi-periodic labelling ρ) have all their faithful
actions on ℝ without global fixed points of type (iii), and present this as the answer to Navas's
Question 4; simplicity makes every action without a global fixed point faithful. Source: A. Navas,
Group actions on 1-manifolds: a list of very concrete open questions, Proceedings of the
International Congress of Mathematicians 2018, Vol. 2, World Scientific (2018), 2029-2056,
arXiv:1712.06462, Question 4; resolution: J. Hyde, Y. Lodha, A. Navas, C. Rivas, Uniformly perfect
finitely generated simple left orderable groups, Ergodic Theory Dynam. Systems 41 (2021), 534-552,
arXiv:1901.03314, Corollary 0.3 (for a quasi-periodic labelling ρ, every faithful action of the
finitely generated infinite simple group G_ρ on ℝ without global fixed points is of type (iii)),
stated there to answer Navas's Question 4; since G_ρ is simple, every action without global fixed
points is faithful. Answered independently by N. Matte Bon and M. Triestino, arXiv:1811.12256,
https://arxiv.org/abs/1901.03314.
-/
public theorem_wanted existsGroupAllLineActionsTypeIII_holds : existsGroupAllLineActionsTypeIII

end MathlibExt.GroupTheory.AllLineActionsGloballyContractingAMR120Problem0004Wanted
