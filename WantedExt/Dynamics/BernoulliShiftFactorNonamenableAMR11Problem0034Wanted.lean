/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Bernoulli shifts over non-amenable groups (Abért, Some questions, Question 34)

M. Abért, Some questions (2010), Question 34: let `Γ` be a non-amenable group. Does `{0, 1}^Γ`
factor onto `{0, 1, 2}^Γ`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Probability.ProductMeasure
public import MathlibExt.GroupTheory.AmenableGroup

@[expose] public section

namespace MathlibExt.Dynamics.BernoulliShiftFactorNonamenableAMR11Problem0034Wanted

/-!
Source: M. Abért, Some questions (2010), Question 34, https://www.renyi.hu/~abert/questions.pdf.
UnsolvedMath record UM-01200034 (`AMR-011-0034`), dataset ulamai/UnsolvedMath v1.8.0.

Bernoulli shifts carry the uniform product measures and the shift action `(γ • x) h = x (γ⁻¹ h)`. A
factor map is a measurable `Γ`-equivariant map pushing one measure to the other (Bowen's
definition). `Γ` is countable, as in the resolving theorem; non-amenable is the negation of
MathlibExt's Følner condition `IsAmenable`, equivalent to amenability for countable discrete groups.
-/

/-- The shift action of `Γ` on `Γ → A`: `(γ • x) h = x (γ⁻¹ h)`. -/
def shift {Γ A : Type*} [Group Γ] (γ : Γ) (x : Γ → A) : Γ → A :=
  fun h => x (γ⁻¹ * h)

/-- The uniform Bernoulli measure on `{0, 1}^Γ`. -/
noncomputable def twoShiftMeasure (Γ : Type*) : MeasureTheory.Measure (Γ → Fin 2) :=
  MeasureTheory.Measure.infinitePi fun _ => ProbabilityTheory.uniformOn (Set.univ : Set (Fin 2))

/-- The uniform Bernoulli measure on `{0, 1, 2}^Γ`. -/
noncomputable def threeShiftMeasure (Γ : Type*) : MeasureTheory.Measure (Γ → Fin 3) :=
  MeasureTheory.Measure.infinitePi fun _ => ProbabilityTheory.uniformOn (Set.univ : Set (Fin 3))

/-- Abért's Question 34, answered: for every countable non-amenable group `Γ` the Bernoulli shift
`{0, 1}^Γ` factors onto `{0, 1, 2}^Γ` (uniform base measures): some measurable `Γ`-equivariant map
pushes the first measure to the second. -/
def nonamenableTwoShiftFactorsOntoThreeShift : Prop :=
  ∀ (Γ : Type) [Group Γ] [Countable Γ], ¬ IsAmenable Γ →
    ∃ Φ : (Γ → Fin 2) → (Γ → Fin 3), Measurable Φ ∧
      (∀ (γ : Γ) (x : Γ → Fin 2), Φ (shift γ x) = shift γ (Φ x)) ∧
      (twoShiftMeasure Γ).map Φ = threeShiftMeasure Γ

/--
Resolved true: Bowen proved that for every countable non-amenable group all Bernoulli shifts are
weakly isomorphic (each factors onto the other); in particular the uniform 2-shift factors onto the
uniform 3-shift. Source: M. Abért, Some questions (2010), Question 34,
https://www.renyi.hu/~abert/questions.pdf; resolution: L. Bowen, Finitary random interlacements and
the Gaboriau-Lyons problem, Geom. Funct. Anal. 29 (2019), 659-689, arXiv:1707.09573, Corollary 1.3:
"Let Γ be any countable non-amenable group. Then all Bernoulli shifts over Γ are weakly isomorphic",
i.e. factor onto each other (Ornstein–Weiss had the 2-shift onto the 4-shift for the free group of
rank 2), https://arxiv.org/abs/1707.09573.
-/
public theorem_wanted nonamenableTwoShiftFactorsOntoThreeShift_holds :
    nonamenableTwoShiftFactorsOntoThreeShift

end MathlibExt.Dynamics.BernoulliShiftFactorNonamenableAMR11Problem0034Wanted
