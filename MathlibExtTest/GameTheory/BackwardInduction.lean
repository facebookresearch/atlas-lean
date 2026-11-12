/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.BackwardInduction
import Mathlib.Tactic

/-! Examples for `MathlibExt.GameTheory.BackwardInduction`: in the entry game,
(In, Accommodate) is a backward-induction and subgame-perfect profile, while
(Out, Fight) is a Nash equilibrium that is not subgame perfect. -/

namespace MathlibExtTest.GameTheory.BackwardInduction

section Examples

open MathlibExt.GameTheory PerfectInfoGame Profile

/-- Out payoff: player 0 gets 0, player 1 gets 2. -/
def outPayoff : Fin 2 → ℝ := ![0, 2]

/-- Fight payoff: both get -1. -/
def fightPayoff : Fin 2 → ℝ := ![-1, -1]

/-- Accommodate payoff: both get 1. -/
def accomPayoff : Fin 2 → ℝ := ![1, 1]

def outLeaf : PerfectInfoGame (Fin 2) := PerfectInfoGame.leaf outPayoff
def fightLeaf : PerfectInfoGame (Fin 2) := PerfectInfoGame.leaf fightPayoff
def accomLeaf : PerfectInfoGame (Fin 2) := PerfectInfoGame.leaf accomPayoff

/-- Player 1's subgame after In: Fight (0) or Accommodate (1). -/
def subChild : Fin (1 + 1) → PerfectInfoGame (Fin 2) := ![fightLeaf, accomLeaf]

def subGame : PerfectInfoGame (Fin 2) := PerfectInfoGame.node 1 subChild

/-- Root game: Out (0) or In (1). -/
def rootChild : Fin (1 + 1) → PerfectInfoGame (Fin 2) := ![outLeaf, subGame]

def entryGame : PerfectInfoGame (Fin 2) := PerfectInfoGame.node 0 rootChild

/-- Subprofiles for the subgame leaves. -/
def subSub : ∀ k, Profile (subChild k)
  | 0 => Profile.leaf fightPayoff
  | 1 => Profile.leaf accomPayoff

/-- Subgame profile: Accommodate. -/
def accomSubProfile : Profile subGame :=
  Profile.node 1 subChild 1 subSub

/-- Subgame profile: Fight. -/
def fightSubProfile : Profile subGame :=
  Profile.node 1 subChild 0 subSub

/-- Root subprofiles for (In, Accommodate). -/
def rootSubInAccom : ∀ k, Profile (rootChild k)
  | 0 => Profile.leaf outPayoff
  | 1 => accomSubProfile

/-- Root subprofiles for (Out, Fight). -/
def rootSubOutFight : ∀ k, Profile (rootChild k)
  | 0 => Profile.leaf outPayoff
  | 1 => fightSubProfile

/-- Profile (In, Accommodate). -/
def inAccomProfile : Profile entryGame :=
  Profile.node 0 rootChild 1 rootSubInAccom

/-- Profile (Out, Fight). -/
def outFightProfile : Profile entryGame :=
  Profile.node 0 rootChild 0 rootSubOutFight

theorem accomSubProfile_isBI : IsBackwardInduction accomSubProfile := by
  unfold accomSubProfile
  apply IsBackwardInduction.node
  · intro k
    fin_cases k
    · show ((-1 : ℝ) ≤ 1)
      norm_num
    · show ((1 : ℝ) ≤ 1)
      norm_num
  · intro k
    fin_cases k
    · exact IsBackwardInduction.leaf _
    · exact IsBackwardInduction.leaf _

theorem inAccomProfile_isBI : IsBackwardInduction inAccomProfile := by
  unfold inAccomProfile
  apply IsBackwardInduction.node
  · intro k
    fin_cases k
    · show ((0 : ℝ) ≤ 1)
      norm_num
    · show ((1 : ℝ) ≤ 1)
      norm_num
  · intro k
    fin_cases k
    · exact IsBackwardInduction.leaf _
    · exact accomSubProfile_isBI

theorem inAccomProfile_isSP : IsSubgamePerfect inAccomProfile :=
  inAccomProfile_isBI.isSubgamePerfect

theorem outFightProfile_notSP : ¬ IsSubgamePerfect outFightProfile := by
  intro hsp
  unfold outFightProfile entryGame at hsp
  cases hsp with
  | node hnash hsub =>
    have hsub1 := hsub 1
    cases hsub1 with
    | node hnash1 hsub1' =>
      have hdev : Deviation 1 fightSubProfile accomSubProfile := by
        unfold fightSubProfile accomSubProfile
        apply Deviation.self
        intro k
        fin_cases k
        · exact Deviation.leaf _
        · exact Deviation.leaf _
      have hle := hnash1 1 accomSubProfile hdev
      simp [accomSubProfile, Profile.outcome, subSub, subChild,
        accomPayoff, fightPayoff] at hle
      norm_num at hle

theorem outLeafOutcome0 (τ' : Profile (PerfectInfoGame.leaf outPayoff)) : τ'.outcome 0 = 0 := by
  cases τ'
  rfl

theorem outLeafOutcome1 (τ' : Profile (PerfectInfoGame.leaf outPayoff)) : τ'.outcome 1 = 2 := by
  cases τ'
  rfl

theorem fightLeafOutcome0 (τ' : Profile (PerfectInfoGame.leaf fightPayoff)) : τ'.outcome 0 = -1 := by
  cases τ'
  rfl

theorem fightDeviate0 (τ' : Profile subGame) (h : Deviation 0 fightSubProfile τ') :
    τ'.outcome 0 = -1 := by
  unfold fightSubProfile subGame at h
  cases h
  case other hij sub'' h' =>
    exact fightLeafOutcome0 (sub'' 0)

theorem outFightProfile_isNash : IsNash outFightProfile := by
  intro j τ' hdev
  unfold outFightProfile entryGame at hdev ⊢
  fin_cases j
  · cases hdev
    case self a' sub' h =>
      fin_cases a'
      · have heq : (sub' 0).outcome 0 = 0 := outLeafOutcome0 (sub' 0)
        show (sub' 0).outcome 0 ≤ (rootSubOutFight 0).outcome 0
        rw [heq]
        show ((0 : ℝ) ≤ 0)
        norm_num
      · have heq : (sub' 1).outcome 0 = -1 := fightDeviate0 (sub' 1) (h 1)
        show (sub' 1).outcome 0 ≤ (rootSubOutFight 0).outcome 0
        rw [heq]
        show ((-1 : ℝ) ≤ 0)
        norm_num
    case other hij sub' h =>
      exact absurd rfl hij
  · cases hdev
    case other hij sub' h =>
      have heq : (sub' 0).outcome 1 = 2 := outLeafOutcome1 (sub' 0)
      show (sub' 0).outcome 1 ≤ (rootSubOutFight 0).outcome 1
      rw [heq]
      show ((2 : ℝ) ≤ 2)
      norm_num

end Examples

#print axioms MathlibExt.GameTheory.PerfectInfoGame.Profile.exists_isBackwardInduction
#print axioms MathlibExt.GameTheory.PerfectInfoGame.Profile.IsBackwardInduction.isSubgamePerfect
#print axioms MathlibExt.GameTheory.PerfectInfoGame.Profile.exists_isBackwardInduction_isSubgamePerfect

end MathlibExtTest.GameTheory.BackwardInduction
