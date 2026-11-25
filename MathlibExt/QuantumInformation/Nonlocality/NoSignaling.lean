/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `e4e4de3e175eab51e689706fcab2456068d90482`.

Co-authored by Adam Kiezun, Tsutomu Okano (@toskua), and Avocado
(upstream author line credits @toskua and Avocado); ported with attribution.
-/

module

public import MathlibExt.QuantumInformation.Nonlocality.Scenario
public import MathlibExt.QuantumInformation.Nonlocality.Local
public import Mathlib.Geometry.Convex.ConvexSpace.Defs

/-!
# No-signaling for finite Bell behaviors

One-party and finite-coalition marginals, full multipartite no-signaling
(every coalition marginal is independent of the settings outside the
coalition), the preserved singleton-marginal predicate, deterministic
no-signaling, and local implies no-signaling.
-/

@[expose] public section

open Finset BigOperators

namespace QuantumInformation
namespace Nonlocality

namespace BellScenario

namespace Behavior

/-- One-party marginal: probability that party `p` outputs `o`
given settings `x`, summing over all joint outcomes with that
local outcome. -/
noncomputable def marginal {S : BellScenario} (B : Behavior S)
    (p : Fin S.numParties) (x : S.SettingAssignment)
    (o : Fin S.numOutcomes) : ℝ :=
  ∑ y ∈ Finset.univ.filter
    (fun y : S.OutcomeAssignment => y p = o), B.prob x y

/-- Finite-coalition marginal: probability that the joint outcome agrees
with `o` on every party in the Finset `K`, given settings `x`. Only the
restriction of `o` to `K` matters. -/
noncomputable def coalitionMarginal {S : BellScenario} (B : Behavior S)
    (K : Finset (Fin S.numParties)) (x : S.SettingAssignment)
    (o : S.OutcomeAssignment) : ℝ :=
  ∑ y ∈ Finset.univ.filter
    (fun y : S.OutcomeAssignment => ∀ p ∈ K, y p = o p), B.prob x y

end Behavior

/-- Singleton-marginal setting independence: the marginal of each party
depends only on its own setting. This is the former meaning of
`IsNoSignaling`, preserved under a precise name; for multipartite
scenarios it is strictly weaker than full no-signaling. -/
def HasSettingIndependentSingletonMarginals (S : BellScenario)
    (B : Behavior S) : Prop :=
  ∀ (p : Fin S.numParties) (x x' : S.SettingAssignment)
    (o : Fin S.numOutcomes), x p = x' p → B.marginal p x o = B.marginal p x' o

/-- Full multipartite no-signaling: the marginal of every coalition `K`
is independent of the settings outside `K`. -/
def IsNoSignaling (S : BellScenario) (B : Behavior S) : Prop :=
  ∀ (K : Finset (Fin S.numParties)) (x x' : S.SettingAssignment),
    (∀ p ∈ K, x p = x' p) → ∀ o : S.OutcomeAssignment,
      B.coalitionMarginal K x o = B.coalitionMarginal K x' o

/-- Singleton-coalition marginal equals the one-party marginal at the
restricted outcome. -/
theorem Behavior.coalitionMarginal_singleton {S : BellScenario} (B : Behavior S)
    (p : Fin S.numParties) (x : S.SettingAssignment)
    (o : S.OutcomeAssignment) :
    B.coalitionMarginal {p} x o = B.marginal p x (o p) := by
  have hset : Finset.univ.filter
        (fun y : S.OutcomeAssignment =>
          ∀ q ∈ ({p} : Finset (Fin S.numParties)), y q = o q)
        = Finset.univ.filter (fun y : S.OutcomeAssignment => y p = o p) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact h p (Finset.mem_singleton_self p)
    · intro h q hq
      rw [Finset.mem_singleton] at hq
      subst hq
      exact h
  unfold Behavior.marginal Behavior.coalitionMarginal
  rw [hset]

/-- Full no-signaling implies singleton-marginal setting independence. -/
theorem IsNoSignaling.hasSingletonMarginals {S : BellScenario} {B : Behavior S}
    (h : IsNoSignaling S B) : HasSettingIndependentSingletonMarginals S B := by
  intro p x x' o hx
  have e1 : B.marginal p x o = B.coalitionMarginal {p} x (fun _ => o) :=
    (Behavior.coalitionMarginal_singleton B p x (fun _ => o)).symm
  have e2 : B.marginal p x' o = B.coalitionMarginal {p} x' (fun _ => o) :=
    (Behavior.coalitionMarginal_singleton B p x' (fun _ => o)).symm
  rw [e1, e2]
  apply h
  intro q hq
  rw [Finset.mem_singleton] at hq
  subst hq
  exact hx

/-- Empty-coalition marginal equals one by normalization. -/
theorem Behavior.coalitionMarginal_empty {S : BellScenario} (B : Behavior S)
    (x : S.SettingAssignment) (o : S.OutcomeAssignment) :
    B.coalitionMarginal ∅ x o = 1 := by
  have hfilter : Finset.univ.filter
        (fun y : S.OutcomeAssignment =>
          ∀ p ∈ (∅ : Finset (Fin S.numParties)), y p = o p) = Finset.univ := by
    ext y
    simp
  unfold Behavior.coalitionMarginal
  rw [hfilter]
  exact B.normalized x

/-- Two-party upgrade: singleton-marginal setting independence implies full
coalition no-signaling when `S.numParties = 2`. Empty coalitions are
normalization (`= 1`), singleton coalitions reduce to the hypothesis via
`coalitionMarginal_singleton`, and two-element coalitions are full, forcing
`x = x'`. -/
theorem HasSettingIndependentSingletonMarginals.toIsNoSignaling_of_numParties_eq_two
    {S : BellScenario} (h2 : S.numParties = 2) {B : Behavior S}
    (h : HasSettingIndependentSingletonMarginals S B) :
    IsNoSignaling S B := by
  intro K x x' hx o
  have hcard_univ : (Finset.univ : Finset (Fin S.numParties)).card = 2 := by
    rw [Finset.card_univ, Fintype.card_fin, h2]
  have hKle : K.card ≤ 2 := hcard_univ ▸ Finset.card_le_univ K
  have hK01 : K.card = 0 ∨ K.card = 1 ∨ K.card = 2 := by omega
  rcases hK01 with h0 | h1 | h2c
  · have hK : K = ∅ := Finset.card_eq_zero.mp h0
    rw [hK, Behavior.coalitionMarginal_empty,
      Behavior.coalitionMarginal_empty]
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h1
    have hm : p ∈ K := by
      rw [hp]
      exact Finset.mem_singleton_self p
    rw [hp, Behavior.coalitionMarginal_singleton,
      Behavior.coalitionMarginal_singleton]
    exact h p x x' (o p) (hx p hm)
  · have hcardα : Fintype.card (Fin S.numParties) = 2 := by
      rw [Fintype.card_fin, h2]
    have hK : K = Finset.univ :=
      Finset.eq_univ_of_card K (h2c.trans hcardα.symm)
    have hxx : x = x' := by
      funext p
      apply hx p
      rw [hK]
      exact Finset.mem_univ p
    rw [hxx]

/-- Two-party equivalence between full coalition no-signaling and
singleton-marginal setting independence. -/
theorem isNoSignaling_iff_singleton_of_numParties_eq_two {S : BellScenario}
    (h2 : S.numParties = 2) {B : Behavior S} :
    IsNoSignaling S B ↔ HasSettingIndependentSingletonMarginals S B :=
  ⟨IsNoSignaling.hasSingletonMarginals,
    fun h => h.toIsNoSignaling_of_numParties_eq_two h2⟩

private theorem deterministicBehavior_coalitionMarginal (S : BellScenario)
    (f : S.DeterministicResponse) (K : Finset (Fin S.numParties))
    (x : S.SettingAssignment) (o : S.OutcomeAssignment) :
    (deterministicBehavior S f).coalitionMarginal K x o =
      if ∀ p ∈ K, f p (x p) = o p then (1 : ℝ) else 0 := by
  unfold Behavior.coalitionMarginal
  simp only [deterministicBehavior_prob]
  let y₀ := S.responseToOutcome f x
  let s : Finset S.OutcomeAssignment :=
    Finset.univ.filter (fun y : S.OutcomeAssignment => ∀ p ∈ K, y p = o p)
  have hmem : ∀ (y : S.OutcomeAssignment),
      y ∈ s ↔ ∀ p ∈ K, y p = o p := by
    intro y
    simp [s, Finset.mem_filter]
  have hsum : (∑ y ∈ s, if y = y₀ then (1 : ℝ) else 0) =
      if y₀ ∈ s then (1 : ℝ) else 0 := by
    rw [Finset.sum_ite_eq' s y₀]
  calc
    (∑ y ∈ s, if y = y₀ then (1 : ℝ) else 0) =
        if y₀ ∈ s then (1 : ℝ) else 0 := hsum
    _ = if ∀ p ∈ K, f p (x p) = o p then (1 : ℝ) else 0 := by
      by_cases h : y₀ ∈ s
      · have hp : ∀ p ∈ K, f p (x p) = o p := (hmem y₀).mp h
        rw [ite_eq_left h, ite_eq_left hp]
      · have hp : ¬ (∀ p ∈ K, f p (x p) = o p) :=
          fun h_eq => h ((hmem y₀).mpr h_eq)
        rw [ite_eq_right h, ite_eq_right hp]

private theorem deterministic_isNoSignaling (S : BellScenario)
    (f : S.DeterministicResponse) :
    IsNoSignaling S (deterministicBehavior S f) := by
  intro K x x' hx o
  simp only [deterministicBehavior_coalitionMarginal]
  have hcond : (∀ p ∈ K, f p (x p) = o p) ↔ (∀ p ∈ K, f p (x' p) = o p) := by
    constructor
    · intro h p hp
      have e := hx p hp
      have h1 := h p hp
      rw [e] at h1
      exact h1
    · intro h p hp
      have e := hx p hp
      have h1 := h p hp
      rw [← e] at h1
      exact h1
  simp only [hcond]

private theorem mixtureBehavior_coalitionMarginal (S : BellScenario)
    (weights : Convexity.StdSimplex ℝ S.DeterministicResponse)
    (K : Finset (Fin S.numParties)) (x : S.SettingAssignment)
    (o : S.OutcomeAssignment) :
    (mixtureBehavior S weights).coalitionMarginal K x o =
      ∑ f : S.DeterministicResponse,
        weights.weights f * (deterministicBehavior S f).coalitionMarginal K x o := by
  unfold Behavior.coalitionMarginal
  simp only [mixtureBehavior_prob]
  let s : Finset S.OutcomeAssignment :=
    Finset.univ.filter (fun y : S.OutcomeAssignment => ∀ p ∈ K, y p = o p)
  calc
    (∑ y ∈ s, ∑ f : S.DeterministicResponse,
        weights.weights f * (deterministicBehavior S f).prob x y) =
        ∑ y ∈ s, ∑ f ∈ Finset.univ,
          weights.weights f * (deterministicBehavior S f).prob x y := by rfl
    _ = ∑ f ∈ Finset.univ, ∑ y ∈ s,
          weights.weights f * (deterministicBehavior S f).prob x y := by
      rw [Finset.sum_comm]
    _ = ∑ f : S.DeterministicResponse, ∑ y ∈ s,
          weights.weights f * (deterministicBehavior S f).prob x y := by rfl
    _ = ∑ f : S.DeterministicResponse,
          weights.weights f * ∑ y ∈ s, (deterministicBehavior S f).prob x y := by
      congr 1
      ext f
      rw [Finset.mul_sum]
    _ = ∑ f : S.DeterministicResponse,
          weights.weights f * (deterministicBehavior S f).coalitionMarginal K x o := by rfl

private theorem mixtureBehavior_isNoSignaling (S : BellScenario)
    (weights : Convexity.StdSimplex ℝ S.DeterministicResponse) :
    IsNoSignaling S (mixtureBehavior S weights) := by
  intro K x x' hx o
  simp only [mixtureBehavior_coalitionMarginal]
  have hdet : ∀ f : S.DeterministicResponse,
      (deterministicBehavior S f).coalitionMarginal K x o =
      (deterministicBehavior S f).coalitionMarginal K x' o := by
    intro f
    exact deterministic_isNoSignaling S f K x x' hx o
  calc
    (∑ f : S.DeterministicResponse,
        weights.weights f * (deterministicBehavior S f).coalitionMarginal K x o) =
        ∑ f : S.DeterministicResponse,
          weights.weights f * (deterministicBehavior S f).coalitionMarginal K x' o := by
      congr 1
      ext f
      rw [hdet f]
    _ = _ := rfl

/-- Every local behavior is no-signaling. -/
theorem isLocal_isNoSignaling {S : BellScenario} {B : Behavior S}
    (hLocal : IsLocal S B) : IsNoSignaling S B := by
  obtain ⟨weights, rfl⟩ := hLocal
  exact mixtureBehavior_isNoSignaling S weights

end BellScenario

end Nonlocality
end QuantumInformation
