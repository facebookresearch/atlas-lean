/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# AMR 22, Problem 7082
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

namespace MathlibExt.Analysis.AMR22Problem7082Wanted

/-! Source record `AMR-022-7082__2307082`. -/

/-- Unit disc `𝔻` from [AMR-022-7082] Problem 7.82. -/
noncomputable def UnitDisc : Set ℂ := Metric.ball (0 : ℂ) 1

/-- Condition (a) from [AMR-022-7082] Problem 7.82: for every fixed
`z ∈ 𝔻`, the map `w ↦ F w z` is injective on `E`. -/
def IsInjectiveInParam (E : Set ℂ) (F : ℂ → ℂ → ℂ) : Prop :=
  ∀ z ∈ UnitDisc, Set.InjOn (fun w => F w z) E

/-- Condition (b) from [AMR-022-7082] Problem 7.82: for each `w ∈ E`,
the map `z ↦ F w z` is analytic on `𝔻`. -/
def IsAnalyticInDisc (E : Set ℂ) (F : ℂ → ℂ → ℂ) : Prop :=
  ∀ w ∈ E, AnalyticOn ℂ (F w) UnitDisc

/-- Condition (c) from [AMR-022-7082] Problem 7.82: at parameter zero,
the motion is the identity on `E`. -/
def IsNormalizedAtZero (E : Set ℂ) (F : ℂ → ℂ → ℂ) : Prop :=
  ∀ w ∈ E, F w 0 = w

/-- Agreement on `E` from [AMR-022-7082] Problem 7.82: `G = F` on
`E × 𝔻`. -/
def AgreesOnDisc (E : Set ℂ) (F G : ℂ → ℂ → ℂ) : Prop :=
  ∀ w ∈ E, ∀ z ∈ UnitDisc, G w z = F w z

/-- Extension question from [AMR-022-7082] Problem 7.82 (Sullivan,
Thurston, Royden): every `F` on `E × 𝔻` satisfying (a), (b), (c)
extends to a `G` on `ℂ × 𝔻` satisfying (a), (b), (c). -/
def conjecture : Prop :=
  ∀ (E : Set ℂ) (F : ℂ → ℂ → ℂ),
    IsInjectiveInParam E F →
      IsAnalyticInDisc E F →
        IsNormalizedAtZero E F →
          ∃ G : ℂ → ℂ → ℂ,
            IsInjectiveInParam Set.univ G ∧
              IsAnalyticInDisc Set.univ G ∧
                IsNormalizedAtZero Set.univ G ∧ AgreesOnDisc E F G

/--
Resolved true: Resolved affirmatively by Słodkowski’s extended λ-lemma: every holomorphic motion
over the unit disk extends to a holomorphic motion of the Riemann sphere. Source: Zbigniew
Słodkowski, Holomorphic motions and polynomial hulls, Proceedings of the American Mathematical
Society 111 (1991), 347–355, https://doi.org/10.2307/2048323. Moved from
`OpenConjectures/Analysis/AMR22Problem7082`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Analysis.AMR22Problem7082Wanted
