/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finitely generated groups of C^(1+α) diffeomorphisms not embedding in C^(1+β) (Navas, Question 13)

Navas, Question 13: given `0 < α < β < 1`, does there exist a finitely generated group of `C^{1+α}`
diffeomorphisms of the circle/interval that does not embed into the group of `C^{1+β}`
diffeomorphisms?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.GroupTheory.Finiteness

@[expose] public section

namespace MathlibExt.GroupTheory.DiffeomorphismCriticalRegularityAMR120Problem0012Wanted

/-!
Source: A. Navas, Group actions on 1-manifolds: a list of very concrete open questions, Proceedings
of the International Congress of Mathematicians 2018, Vol. 2, World Scientific (2018), 2029-2056,
arXiv:1712.06462, Question 13. UnsolvedMath record UM-00800298 (`AMR-120-0012`), dataset
ulamai/UnsolvedMath v1.8.0.

Both manifolds of the question are stated, each with the target group on the same manifold: `[0, 1]`
(homeomorphisms of `Set.Icc 0 1`) and the circle `ℝ / ℤ` (`AddCircle 1`). An orientation-preserving
`C^{1+α}` diffeomorphism is `C¹` with positive derivative and `α`-Hölder derivative (on `[0, 1]`
with one-sided derivatives at the endpoints; on the circle through a degree-one lift `F`, that is `F
(x + 1) = F x + 1`). A group does not embed into the `C^{1+β}` group when every injective
homomorphism into the homeomorphism group has an image element that is not `C^{1+β}`.
-/

/-- `f` is an orientation-preserving `C^{1+α}` diffeomorphism of the interval `[0, 1]`: it is
monotone and agrees on `[0, 1]` with a function `F` that is `C¹` on `[0, 1]` (one-sided derivatives
at the endpoints), has positive derivative there, and whose derivative is `α`-Hölder continuous. -/
def IsIntervalDiffOneAlpha (α : ℝ) (f : Set.Icc (0 : ℝ) 1 ≃ₜ Set.Icc (0 : ℝ) 1) : Prop :=
  Monotone f ∧ ∃ F : ℝ → ℝ, (∀ x : Set.Icc (0 : ℝ) 1, (f x : ℝ) = F x) ∧
    ContDiffOn ℝ 1 F (Set.Icc 0 1) ∧ (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < derivWithin F (Set.Icc 0 1) x) ∧
    ∃ C : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |derivWithin F (Set.Icc 0 1) x - derivWithin F (Set.Icc 0 1) y| ≤ C * |x - y| ^ α

/-- `f` is an orientation-preserving `C^{1+α}` diffeomorphism of the circle `ℝ / ℤ`: it lifts to a
`C¹` map `F : ℝ → ℝ` with `F (x + 1) = F x + 1`, positive derivative, and `α`-Hölder continuous
derivative. -/
def IsCircleDiffOneAlpha (α : ℝ) (f : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ)) : Prop :=
  ∃ F : ℝ → ℝ, (∀ x : ℝ, f (x : AddCircle (1 : ℝ)) = (F x : AddCircle (1 : ℝ))) ∧
    (∀ x, F (x + 1) = F x + 1) ∧ ContDiff ℝ 1 F ∧ (∀ x, 0 < deriv F x) ∧
    ∃ C : ℝ, ∀ x y : ℝ, |deriv F x - deriv F y| ≤ C * |x - y| ^ α

/-- Navas, Question 13 for the interval: for `0 < α < β < 1` there is a finitely generated group of
orientation-preserving `C^{1+α}` diffeomorphisms of `[0, 1]` that does not embed into the group of
`C^{1+β}` diffeomorphisms of `[0, 1]`. -/
def intervalNotSmoothable : Prop :=
  ∀ α β : ℝ, 0 < α → α < β → β < 1 →
    ∃ G : Subgroup (Set.Icc (0 : ℝ) 1 ≃ₜ Set.Icc (0 : ℝ) 1), G.FG ∧
      (∀ g ∈ G, IsIntervalDiffOneAlpha α g) ∧
      ∀ φ : G →* (Set.Icc (0 : ℝ) 1 ≃ₜ Set.Icc (0 : ℝ) 1), Function.Injective φ →
        ∃ g, ¬ IsIntervalDiffOneAlpha β (φ g)

/-- Navas, Question 13 for the circle: for `0 < α < β < 1` there is a finitely generated group of
orientation-preserving `C^{1+α}` diffeomorphisms of the circle that does not embed into the group
of `C^{1+β}` diffeomorphisms of the circle. -/
def circleNotSmoothable : Prop :=
  ∀ α β : ℝ, 0 < α → α < β → β < 1 →
    ∃ G : Subgroup (AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ)), G.FG ∧
      (∀ g ∈ G, IsCircleDiffOneAlpha α g) ∧
      ∀ φ : G →* (AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ)), Function.Injective φ →
        ∃ g, ¬ IsCircleDiffOneAlpha β (φ g)

/--
Resolved true for the interval: Kim and Koberda's Main Theorem gives, for each `α ≥ 1`, finitely
generated subgroups of `Diff^α_+(I)` with no injective homomorphism into `Diff^β_+(I)` for any `β >
α`; apply it with exponents `1 + α < 1 + β`. Navas's list records the question as solved by Kim and
Koberda. Source: A. Navas, Group actions on 1-manifolds: a list of very concrete open questions,
Proceedings of the International Congress of Mathematicians 2018, Vol. 2, World Scientific (2018),
2029-2056, arXiv:1712.06462, Question 13; resolution: S.-h. Kim, T. Koberda, Diffeomorphism groups
of critical regularity, Invent. Math. 221 (2020), 421-501, arXiv:1711.05589, Main Theorem (for every
real α ≥ 1 and M ∈ {I, S¹}, the class of countable subgroups of Diff^α_+(M) minus the union over β >
α of those of Diff^β_+(M) contains finitely generated groups; Diff^{k+τ}_+(M) = C^k diffeomorphisms
with τ-Hölder k-th derivative); Navas's list, Added in Proof: 'Question 13 has been recently solved
by Kim and Koberda', https://arxiv.org/abs/1711.05589.
-/
public theorem_wanted intervalNotSmoothable_holds : intervalNotSmoothable

/--
Resolved true for the circle: Kim and Koberda's Main Theorem covers `M = S¹` as well, with exponents
`1 + α < 1 + β`. Navas's list records the question as solved by Kim and Koberda. Source: A. Navas,
Group actions on 1-manifolds: a list of very concrete open questions, Proceedings of the
International Congress of Mathematicians 2018, Vol. 2, World Scientific (2018), 2029-2056,
arXiv:1712.06462, Question 13; resolution: S.-h. Kim, T. Koberda, Diffeomorphism groups of critical
regularity, Invent. Math. 221 (2020), 421-501, arXiv:1711.05589, Main Theorem (for every real α ≥ 1
and M ∈ {I, S¹}, the class of countable subgroups of Diff^α_+(M) minus the union over β > α of those
of Diff^β_+(M) contains finitely generated groups; Diff^{k+τ}_+(M) = C^k diffeomorphisms with
τ-Hölder k-th derivative); Navas's list, Added in Proof: 'Question 13 has been recently solved by
Kim and Koberda', https://arxiv.org/abs/1711.05589.
-/
public theorem_wanted circleNotSmoothable_holds : circleNotSmoothable

end MathlibExt.GroupTheory.DiffeomorphismCriticalRegularityAMR120Problem0012Wanted
