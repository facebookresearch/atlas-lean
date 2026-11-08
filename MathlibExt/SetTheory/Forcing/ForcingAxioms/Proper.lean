/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Nam Trang
-/
module

public import Mathlib.Order.Defs.Unbundled
public import MathlibExt.SetTheory.Cardinal.Cofinality.CountableSubsets

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 43, Logic 44, Logic 45, Logic 46, Logic 47, Logic 48

/-!
# `MathlibExt.SetTheory.Forcing.ForcingAxioms.Proper`

## References

* Jech (for `modelConds`, `modelSets`, `IsCompatible`, `IsPredenseBelow`, `IsGenericFor`,
  `IsProperForcing`)
-/

namespace MetaMathlibExt

-- Logic 43: Conditions belonging to a model

/-- The conditions of a poset ℙ belonging to the model M, i.e. M ∩ ℙ -/
def modelConds {P : Type*} (M : Set (P ⊕ Set P)) : Set P := Sum.inl ⁻¹' M

-- Logic 44: Subsets belonding to a model

/-- The subsets of ℙ belonging to the model M -/
def modelSets {P : Type*} (M : Set (P ⊕ Set P)) : Set (Set P) := Sum.inr ⁻¹' M

-- Logic 45: Compatibility

/-- Two conditions p,q∈ ℙ are compatible if there is a condition r∈ ℙ such that r≤ p and r≤ q -/
def IsCompatible {P : Type*} [PartialOrder P] (p q : P) : Prop := ∃ r : P, r ≤ p ∧ r ≤ q

-- Logic 46: Predense below

/-- A set A⊂ ℙ is predense below q∈ P if for any r≤ q, there is a∈ A such that a, r are compatible
-/
def IsPredenseBelow {P : Type*} [PartialOrder P] (A : Set P) (q : P) : Prop :=
  ∀ r ≤ q, ∃ a ∈ A, IsCompatible r a

-- Logic 47: $(M,P)$-generic condition

/-- Fix a set M ⊆ ℙ ⊔ 𝒫(ℙ) and write M_c = , p ∈ ℙ : inl(p) ∈ M ,,   Mₛ = , D ⊆ ℙ : inr(D) ∈ M ,. No
model-theoretic condition is imposed on M here. In the intended application M is (the trace of) a
countable elementary submodel M ≺ H(θ) with ℙ ∈ M — uncollapsed, hence not transitive — but
genericity refers only to M_c and Mₛ, so those are all the definition records. The elementarity is
supplied where it is used: by the club in IsProper, not here.

A condition q is (M,ℙ)-generic if for every D ∈ Mₛ that is dense in ℙ, the set D ∩ M_c is predense
below q: ∀ D ∈ Mₛ [ D  dense ⟶ ∀ r ≤ q ∃ a ∈ D ∩ M_c ∃ s ∈ ℙ (s ≤ r ∧ s ≤ a) ].
-/
def IsGenericFor {P : Type*} [PartialOrder P] (M : Set (P ⊕ Set P)) (q : P) : Prop :=
  ∀ D ∈ modelSets M, IsCoinitial D → IsPredenseBelow (D ∩ modelConds M) q

-- Logic 48: Proper Forcings

/-- ℙ is proper if, setting X = ℙ ⊔ 𝒫(ℙ), there is a club C ⊆ [X]^ω such that for every M ∈ C and
every p ∈ M_c there is an (M,ℙ)-generic condition q ≤ p.

The union is disjoint: M_c and Mₛ are read off the two halves separately. The literature's
requirement ℙ ∈ M is not imposed — ℙ is the element inr(ℙ) of X, and cofinality of C already
supplies members containing it.
-/
def IsProperForcing (P : Type*) [PartialOrder P] : Prop :=
  ∃ C : Set (Set (P ⊕ Set P)), IsClubOmega C ∧
    ∀ M ∈ C, ∀ p ∈ modelConds M, ∃ q ≤ p, IsGenericFor M q

end MetaMathlibExt

end
