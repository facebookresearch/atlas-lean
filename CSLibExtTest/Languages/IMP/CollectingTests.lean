/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.IMP.Collecting

@[expose] public section

set_option autoImplicit false

namespace Cslib.IMP.CollectingTests

/-- The constantly zero state. -/
def zeroState : State :=
  fun _ => 0

/-- The state obtained from `zeroState` by setting variable `0` to
`2`. -/
def twoState : State :=
  Function.update zeroState 0 2

/-- The state obtained from `zeroState` by setting variable `0` to
`1`. -/
def oneState : State :=
  Function.update zeroState 0 1

/-- A loop decrementing variable `0` until it reaches zero. -/
def countdown : Cmd :=
  .while (.not (.eq (.var 0) (.const 0)))
    (.assign 0 (.sub (.var 0) (.const 1)))

/-- An assignment's target configuration is collected. -/
theorem assign_target_mem_collecting :
    (.skip, Function.update zeroState 0 4) ∈
      collecting {(.assign 0 (.const 4), zeroState)} := by
  rw [collecting_eq_reachableConfigs]
  unfold reachableConfigs
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  exact ⟨_, rfl, Relation.ReflTransGen.single
    (Step.assign zeroState 0 (.const 4))⟩

/-- After one iteration of `countdown`, the loop configuration with
variable `0` equal to `1` is collected. -/
theorem countdown_one_mem_collecting :
    (countdown, oneState) ∈ collecting {(countdown, twoState)} := by
  rw [collecting_eq_reachableConfigs]
  unfold reachableConfigs
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  have hEval : AExp.eval (.sub (.var 0) (.const 1)) twoState = 1 := by
    decide
  have hState : Function.update twoState 0 1 = oneState := by
    simp only [twoState, oneState, Function.update_idem]
  have hGuard : BExp.eval (.not (.eq (.var 0) (.const 0))) twoState = true := by
    decide
  have hAssign : Step (.assign 0 (.sub (.var 0) (.const 1)), twoState) (.skip, oneState) := by
    have hStep := Step.assign twoState 0 (.sub (.var 0) (.const 1))
    rw [hEval] at hStep
    rw [hState] at hStep
    exact hStep
  refine ⟨_, rfl, ?_⟩
  refine Relation.ReflTransGen.tail ?_ (Step.seqSkip _ _)
  refine Relation.ReflTransGen.tail ?_ (Step.seqStep hAssign)
  refine Relation.ReflTransGen.tail ?_ (Step.iteTrue (elseBranch := .skip) hGuard)
  exact Relation.ReflTransGen.single (Step.whileStep _ _ _)

/-- From a single `skip` configuration, the same command in a
different state is not collected. -/
theorem skip_other_state_not_mem_collecting :
    (.skip, oneState) ∉ collecting {(.skip, zeroState)} := by
  rw [collecting_eq_reachableConfigs]
  unfold reachableConfigs
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  intro hEx
  obtain ⟨c, hc, hsteps⟩ := hEx
  have hInv : ∀ x, Steps (.skip, zeroState) x → x = (.skip, zeroState) := by
    intro x h
    induction h with
    | refl => rfl
    | tail _ hStep ih =>
      rw [ih] at hStep
      exact absurd hStep Step.skip_not_step
  rw [hc] at hsteps
  have hEq := hInv _ hsteps
  have hStateEq : oneState = zeroState := congrArg Prod.snd hEq
  have h0 : oneState 0 = zeroState 0 := congrFun hStateEq 0
  simp only [oneState, zeroState, Function.update_self] at h0
  exact absurd h0 (by decide)

/-- An initial configuration is collected, by one unfolding of the
public fixed-point equation. -/
theorem initial_mem_collecting_via_unfold :
    (.assign 0 (.const 4), zeroState) ∈
      collecting {(.assign 0 (.const 4), zeroState)} := by
  rw [← collectingStep_collecting]
  unfold collectingStep
  simp only [Set.mem_union]
  exact Or.inl rfl

end Cslib.IMP.CollectingTests
