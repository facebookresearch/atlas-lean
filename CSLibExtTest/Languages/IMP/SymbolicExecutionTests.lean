/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Tests for bounded symbolic execution
-/
module

public import CSLibExt.Languages.IMP.SymbolicExecution

/-!
# Tests for bounded symbolic execution
-/

@[expose] public section

namespace Cslib.IMP.SymbolicTests

open Cslib.IMP Cslib.IMP.Symbolic

/-- T1 command x := 1 - 2. -/
def t1_cmd : Cmd :=
  .assign 0 (.sub (.const 1) (.const 2))

/-- T2 command with branch fork. -/
def t2_cmd : Cmd :=
  .seq (.assign 1 (.add (.var 0) (.const 1)))
    (.ite (.le (.var 1) (.const 3))
      (.assign 2 (.mul (.var 1) (.const 2)))
      (.assign 2 (.const 0)))

/-- T3 countdown loop. -/
def t3_cmd : Cmd :=
  .while (.le (.const 1) (.var 0))
    (.assign 0 (.sub (.var 0) (.const 1)))

/-- T4 nested loops. -/
def t4_cmd : Cmd :=
  .seq (.assign 3 (.const 2))
    (.while (.le (.const 1) (.var 3))
      (.seq (.assign 3 (.sub (.var 3) (.const 1)))
        (.seq (.assign 4 (.const 2))
          (.while (.le (.const 1) (.var 4))
            (.assign 4
              (.sub (.var 4) (.const 1)))))))

/-- T5a unknown branch kept. -/
def t5a_cmd : Cmd :=
  .ite (.eq (.mul (.var 0) (.var 0)) (.const 4))
    (.assign 1 (.const 1)) (.assign 1 (.const 2))

/-- T5b pruned branch. -/
def t5b_cmd : Cmd :=
  .ite (.le (.const 1) (.const 0))
    (.assign 1 (.const 1)) (.assign 1 (.const 2))

/-- T5c unknown unsat kept. -/
def t5c_cmd : Cmd :=
  .ite (.eq (.mul (.var 0) (.var 0)) (.const 2))
    (.assign 1 (.const 1)) (.assign 1 (.const 2))

/-- Bridge table mapping 0 to 3. -/
def t_bridge : ConstTable :=
  fun x => if x = 0 then some 3 else none

/-- T2c witness: x = 2 takes the then-branch. -/
def s2 : State :=
  Function.update (fun _ => 0) 0 2

/-- T2c witness: x = 3 takes the else-branch. -/
def s3 : State :=
  Function.update (fun _ => 0) 0 3

/-- T3b witness: x = 3 runs three iterations. -/
def sx3 : State :=
  Function.update (fun _ => 0) 0 3

/-- T3c witness: x = 4 exceeds bound 3. -/
def sx4 : State :=
  Function.update (fun _ => 0) 0 4

/-- T5a witness: x = 2 satisfies x * x = 4. -/
def sx2 : State :=
  Function.update (fun _ => 0) 0 2

/-- T4d witness: concrete zero initial state. -/
def s_t4 : State :=
  fun _ => 0

theorem t1_a :
    (paths 0 t1_cmd).length = 1 ∧
    ((paths 0 t1_cmd)[0]?.map Path.guard) =
      some (.truth true) ∧
    ((paths 0 t1_cmd)[0]?.map
      (fun p => p.store 0)) = some (.const 0) ∧
    ((paths 0 t1_cmd)[0]?.map Path.cost) = some 0 ∧
    (cutoffs 0 t1_cmd).length = 0 := by decide

theorem t1_b (σ : Nat → AExp) (s : State) :
    (AExp.subst σ
      (.sub (.const 1) (.const 2))).eval s = 0 := by
  rw [AExp.eval_subst]
  rfl

theorem t1_c_run (s : State) :
    BigStep t1_cmd s (Function.update s 0 0) := by
  have he : (.sub (.const 1) (.const 2) : AExp).eval s
      = 0 := rfl
  have h := BigStep.assign s 0 (.sub (.const 1) (.const 2))
  rw [he] at h
  exact h

theorem t2_a :
    (paths 0 t2_cmd).length = 2 ∧
    (cutoffs 0 t2_cmd).length = 0 := by decide

theorem t2_cover (s : State) :
    ∃ l ∈ leaves 0 t2_cmd,
      (match l with
        | .done p => p.guard
        | .cut p => p.guard).eval s = true :=
  leaves_cover 0 t2_cmd s

theorem t3_a_len : (leaves 3 t3_cmd).length = 5 := by
  decide

theorem t4_a :
    (leaves 5 t4_cmd).length = 1 ∧
    (paths 5 t4_cmd).length = 0 ∧
    (cutoffs 5 t4_cmd).length = 1 := by decide

theorem t4_b :
    (leaves 6 t4_cmd).length = 1 ∧
    (paths 6 t4_cmd).length = 1 ∧
    (cutoffs 6 t4_cmd).length = 0 := by decide

theorem t4_c : (cutoffs 2 t4_cmd).length = 1 := by decide

theorem t5a_len : (paths 0 t5a_cmd).length = 2 := by decide

theorem t5b_len : (paths 0 t5b_cmd).length = 1 := by decide

theorem t5b_prune (s : State) :
    BExp.eval (.le (.const 1) (.const 0))
      (Store.eval Path.init.store s) = false := by
  have h : Path.assume (.le (.const 1) (.const 0))
      Path.init = none := rfl
  exact Path.assume_eq_none h s

theorem t5c_len : (paths 0 t5c_cmd).length = 2 := by decide

theorem t_bexp_subst (σ : Nat → AExp) (s : State) :
    (BExp.subst σ (.truth true)).eval s = true := by
  rw [BExp.eval_subst]
  rfl

theorem t_bridge_afold :
    afold t_bridge (.add (.var 0) (.var 1)) =
      afold emptyTable
        (AExp.subst (tableStore t_bridge)
          (.add (.var 0) (.var 1))) :=
  afold_eq_subst t_bridge _

theorem t_bridge_bfold :
    bfold t_bridge (.le (.add (.var 0) (.var 1))
        (.const 5)) =
      bfold emptyTable
        (BExp.subst (tableStore t_bridge)
          (.le (.add (.var 0) (.var 1)) (.const 5))) :=
  bfold_eq_subst t_bridge _

theorem t_bridge_approx (s : State) :
    ConstApprox t_bridge s ↔
      Store.eval (tableStore t_bridge) s = s :=
  constApprox_iff t_bridge s

theorem t_init_eval (s : State) :
    Store.eval Store.init s = s :=
  Store.eval_init s

theorem t_update_eval (σ : Store) (s : State) :
    Store.eval (Function.update σ 0 (.const 1)) s =
      Function.update (Store.eval σ s) 0 1 := by
  have h := Store.eval_update σ 0 (.const 1) s
  simpa using h

theorem t_erase (s : State) :
    BigStep t1_cmd s (Function.update s 0 0) := by
  have hc : BigStepCost t1_cmd s
      (Function.update s 0 0) 0 := by
    have he : (.sub (.const 1) (.const 2) : AExp).eval s
        = 0 := rfl
    have h := BigStepCost.assign s 0 (.sub (.const 1)
      (.const 2))
    rw [he] at h
    simpa [t1_cmd] using h
  exact (bigStepCost_erase _ _ _).mp ⟨0, hc⟩

theorem t_sound (q : Path) (s : State)
    (hm : q ∈ paths 0 t1_cmd)
    (hg : q.guard.eval s = true) :
    BigStepCost t1_cmd s (Store.eval q.store s)
      q.cost ∧ q.cost ≤ 0 :=
  paths_sound 0 t1_cmd q s hm hg

theorem t_complete (s f : State) (n : Nat)
    (h : BigStepCost t1_cmd s f n) (hle : n ≤ 0) :
    ∃ q ∈ paths 0 t1_cmd, q.guard.eval s = true ∧
      Store.eval q.store s = f ∧ q.cost = n :=
  paths_complete 0 t1_cmd s f n h hle

theorem t_cutcost (q : Path)
    (hm : q ∈ cutoffs 3 t3_cmd) : q.cost = 3 :=
  cutoffs_cost 3 t3_cmd q hm

theorem t_exh (s : State)
    (hno : ∀ q ∈ paths 3 t3_cmd,
      q.guard.eval s ≠ true) :
    (∃ q ∈ cutoffs 3 t3_cmd,
      q.guard.eval s = true) ∧
      (∀ f n, BigStepCost t3_cmd s f n → 3 < n) :=
  exhausted_of_no_path 3 t3_cmd s hno

theorem t1_c_guards :
    (paths 0 t1_cmd).map Path.guard = [.truth true] := by
  decide

theorem t1_c_stores :
    (paths 0 t1_cmd).map (fun p => p.store 0) =
      [.const 0] := by
  decide

theorem t1_c_costs :
    (paths 0 t1_cmd).map Path.cost = [0] := by
  decide

theorem t1_c_sound (s : State) (q : Path)
    (hm : q ∈ paths 0 t1_cmd) :
    q.guard.eval s = true ∧
      (Store.eval q.store s) 0 = 0 ∧ q.cost = 0 ∧
      BigStepCost t1_cmd s (Store.eval q.store s) 0 := by
  have hmg : q.guard ∈ (paths 0 t1_cmd).map Path.guard :=
    List.mem_map.mpr ⟨q, hm, rfl⟩
  rw [t1_c_guards] at hmg
  simp at hmg
  have hms : q.store 0 ∈
      (paths 0 t1_cmd).map (fun p => p.store 0) :=
    List.mem_map.mpr ⟨q, hm, rfl⟩
  rw [t1_c_stores] at hms
  simp at hms
  have hmc : q.cost ∈ (paths 0 t1_cmd).map Path.cost :=
    List.mem_map.mpr ⟨q, hm, rfl⟩
  rw [t1_c_costs] at hmc
  simp at hmc
  have hg : q.guard.eval s = true := by rw [hmg]; rfl
  have hsnd :
      BigStepCost t1_cmd s (Store.eval q.store s) 0 := by
    have h := (paths_sound 0 t1_cmd q s hm hg).1
    rw [hmc] at h
    exact h
  refine ⟨hg, ?_, hmc, hsnd⟩
  have happ : (Store.eval q.store s) 0
      = (q.store 0).eval s := rfl
  rw [happ, hms]; rfl

theorem t2_a_guards :
    (paths 0 t2_cmd).map Path.guard =
      [.and (.truth true)
          (.le (.add (.var 0) (.const 1)) (.const 3)),
        .and (.truth true)
          (.not (.le (.add (.var 0) (.const 1))
            (.const 3)))] := by
  decide

theorem t2_a_store1 :
    (paths 0 t2_cmd).map (fun p => p.store 1) =
      [.add (.var 0) (.const 1),
        .add (.var 0) (.const 1)] := by
  decide

theorem t2_a_store2 :
    (paths 0 t2_cmd).map (fun p => p.store 2) =
      [.mul (.add (.var 0) (.const 1)) (.const 2),
        .const 0] := by
  decide

theorem t2_a_costs :
    (paths 0 t2_cmd).map Path.cost = [0, 0] := by
  decide

theorem t2_c_then :
    ∃ q ∈ paths 0 t2_cmd,
      q.guard.eval s2 = true ∧
        (Store.eval q.store s2) 2 = 6 ∧ q.cost = 0 ∧
        BigStepCost t2_cmd s2 (Store.eval q.store s2) 0 := by
  have hlen : (paths 0 t2_cmd).length = 2 := t2_a.1
  match hpaths : paths 0 t2_cmd with
  | [] => simp [hpaths] at hlen
  | [_] => simp [hpaths] at hlen
  | q0 :: _q1 :: _rest =>
    have hmem0 : q0 ∈ paths 0 t2_cmd := by
      rw [hpaths]; simp
    have hgg := t2_a_guards
    rw [hpaths] at hgg
    simp at hgg
    obtain ⟨hg0, -, -⟩ := hgg
    have hs2 := t2_a_store2
    rw [hpaths] at hs2
    simp at hs2
    obtain ⟨hs0, -, -⟩ := hs2
    have hcc := t2_a_costs
    rw [hpaths] at hcc
    simp at hcc
    obtain ⟨hc0, -, -⟩ := hcc
    have hgeval : q0.guard.eval s2 = true := by
      rw [hg0]; rfl
    have hval : (Store.eval q0.store s2) 2 = 6 := by
      have happ : (Store.eval q0.store s2) 2
          = (q0.store 2).eval s2 := rfl
      rw [happ, hs0]; rfl
    have hsnd :
        BigStepCost t2_cmd s2 (Store.eval q0.store s2) 0 := by
      have h := (paths_sound 0 t2_cmd q0 s2 hmem0 hgeval).1
      rw [hc0] at h
      exact h
    exact ⟨q0, by simp, hgeval, hval, hc0, hsnd⟩

theorem t2_c_else :
    ∃ q ∈ paths 0 t2_cmd,
      q.guard.eval s3 = true ∧
        (Store.eval q.store s3) 2 = 0 ∧ q.cost = 0 ∧
        BigStepCost t2_cmd s3 (Store.eval q.store s3) 0 := by
  have hlen : (paths 0 t2_cmd).length = 2 := t2_a.1
  match hpaths : paths 0 t2_cmd with
  | [] => simp [hpaths] at hlen
  | [_] => simp [hpaths] at hlen
  | _q0 :: q1 :: _rest =>
    have hmem1 : q1 ∈ paths 0 t2_cmd := by
      rw [hpaths]; simp
    have hgg := t2_a_guards
    rw [hpaths] at hgg
    simp at hgg
    obtain ⟨-, hg1, -⟩ := hgg
    have hs2 := t2_a_store2
    rw [hpaths] at hs2
    simp at hs2
    obtain ⟨-, hs1, -⟩ := hs2
    have hcc := t2_a_costs
    rw [hpaths] at hcc
    simp at hcc
    obtain ⟨-, hc1, -⟩ := hcc
    have hgeval : q1.guard.eval s3 = true := by
      rw [hg1]; rfl
    have hval : (Store.eval q1.store s3) 2 = 0 := by
      have happ : (Store.eval q1.store s3) 2
          = (q1.store 2).eval s3 := rfl
      rw [happ, hs1]; rfl
    have hsnd :
        BigStepCost t2_cmd s3 (Store.eval q1.store s3) 0 := by
      have h := (paths_sound 0 t2_cmd q1 s3 hmem1 hgeval).1
      rw [hc1] at h
      exact h
    exact ⟨q1, by simp, hgeval, hval, hc1, hsnd⟩

theorem t3_a_costs_all :
    (leaves 3 t3_cmd).map
        (fun l => match l with | .done p => p.cost | .cut p => p.cost) =
      [0, 1, 2, 3, 3] := by
  decide

theorem t3_a_stores :
    (paths 3 t3_cmd).map (fun p => p.store 0) =
      [.var 0, .sub (.var 0) (.const 1),
        .sub (.sub (.var 0) (.const 1)) (.const 1),
        .sub (.sub (.sub (.var 0) (.const 1)) (.const 1))
          (.const 1)] := by
  decide

theorem t3_a_costs :
    (paths 3 t3_cmd).map Path.cost = [0, 1, 2, 3] := by
  decide

theorem t3_b_evals :
    (paths 3 t3_cmd).map (fun q => q.guard.eval sx3) =
      [false, false, false, true] := by
  decide

theorem t3_b_cover :
    ∃ q ∈ paths 3 t3_cmd,
      q.guard.eval sx3 = true ∧
        (Store.eval q.store sx3) 0 = 0 ∧ q.cost = 3 ∧
        BigStepCost t3_cmd sx3 (Store.eval q.store sx3) 3 := by
  have hlen : (paths 3 t3_cmd).length = 4 := by decide
  match hpaths : paths 3 t3_cmd with
  | [] => simp [hpaths] at hlen
  | [_] => simp [hpaths] at hlen
  | [_ , _] => simp [hpaths] at hlen
  | [_ , _, _] => simp [hpaths] at hlen
  | _q0 :: _q1 :: _q2 :: q3 :: _rest =>
    have hmem3 : q3 ∈ paths 3 t3_cmd := by
      rw [hpaths]; simp
    have hev := t3_b_evals
    rw [hpaths] at hev
    simp at hev
    obtain ⟨-, -, -, heval, -⟩ := hev
    have hst := t3_a_stores
    rw [hpaths] at hst
    simp at hst
    obtain ⟨-, -, -, hs3, -⟩ := hst
    have hcc := t3_a_costs
    rw [hpaths] at hcc
    simp at hcc
    obtain ⟨-, -, -, hc3, -⟩ := hcc
    have hval : (Store.eval q3.store sx3) 0 = 0 := by
      have happ : (Store.eval q3.store sx3) 0
          = (q3.store 0).eval sx3 := rfl
      rw [happ, hs3]; rfl
    have hsnd :
        BigStepCost t3_cmd sx3 (Store.eval q3.store sx3) 3 := by
      have h := (paths_sound 3 t3_cmd q3 sx3 hmem3 heval).1
      rw [hc3] at h
      exact h
    exact ⟨q3, by simp, heval, hval, hc3, hsnd⟩

theorem t3_c_evals :
    (paths 3 t3_cmd).map (fun q => q.guard.eval sx4) =
      [false, false, false, false] := by
  decide

theorem t3_c_no_path (q : Path) (hm : q ∈ paths 3 t3_cmd) :
    q.guard.eval sx4 ≠ true := by
  have h : q.guard.eval sx4 ∈
      (paths 3 t3_cmd).map (fun q => q.guard.eval sx4) :=
    List.mem_map.mpr ⟨q, hm, rfl⟩
  rw [t3_c_evals] at h
  simp at h
  intro hcon
  exact absurd (h.symm.trans hcon) (by decide)

theorem t3_c_cut_evals :
    (cutoffs 3 t3_cmd).map (fun q => q.guard.eval sx4) =
      [true] := by
  decide

theorem t3_c_cut_cost :
    (cutoffs 3 t3_cmd).map Path.cost = [3] := by
  decide

theorem t3_c_paths4_costs :
    (paths 4 t3_cmd).map Path.cost = [0, 1, 2, 3, 4] := by
  decide

theorem t3_c_paths4_evals :
    (paths 4 t3_cmd).map (fun q => q.guard.eval sx4) =
      [false, false, false, false, true] := by
  decide

theorem t3_cost4 :
    BigStepCost t3_cmd sx4 (Function.update sx4 0 0) 4 := by
  have hfin : Function.update
        (Function.update (Function.update (Function.update sx4 0 3) 0 2) 0 1)
        0 0
        = Function.update sx4 0 0 := by
    funext x
    by_cases hx : x = 0
    · subst hx
      rfl
    · simp [Function.update, hx]
  rw [← hfin]
  have a0 : BigStepCost (.assign 0 (.sub (.var 0) (.const 1))) sx4
      (Function.update sx4 0 3) 0 := by
    have he : (.sub (.var 0) (.const 1) : AExp).eval sx4 = 3 := rfl
    have h := BigStepCost.assign sx4 0 (.sub (.var 0) (.const 1))
    rw [he] at h
    exact h
  have a1 : BigStepCost (.assign 0 (.sub (.var 0) (.const 1)))
      (Function.update sx4 0 3)
      (Function.update (Function.update sx4 0 3) 0 2) 0 := by
    have he : (.sub (.var 0) (.const 1) : AExp).eval
        (Function.update sx4 0 3) = 2 := rfl
    have h := BigStepCost.assign (Function.update sx4 0 3) 0
      (.sub (.var 0) (.const 1))
    rw [he] at h
    exact h
  have a2 : BigStepCost (.assign 0 (.sub (.var 0) (.const 1)))
      (Function.update (Function.update sx4 0 3) 0 2)
      (Function.update (Function.update (Function.update sx4 0 3) 0 2)
        0 1) 0 := by
    have he : (.sub (.var 0) (.const 1) : AExp).eval
        (Function.update (Function.update sx4 0 3) 0 2) = 1 := rfl
    have h := BigStepCost.assign
      (Function.update (Function.update sx4 0 3) 0 2) 0
      (.sub (.var 0) (.const 1))
    rw [he] at h
    exact h
  have a3 : BigStepCost (.assign 0 (.sub (.var 0) (.const 1)))
      (Function.update (Function.update (Function.update sx4 0 3) 0 2)
        0 1)
      (Function.update
        (Function.update (Function.update (Function.update sx4 0 3) 0 2)
          0 1) 0 0) 0 := by
    have he : (.sub (.var 0) (.const 1) : AExp).eval
        (Function.update (Function.update (Function.update sx4 0 3) 0 2)
          0 1) = 0 := rfl
    have h := BigStepCost.assign
      (Function.update (Function.update (Function.update sx4 0 3) 0 2)
        0 1) 0
      (.sub (.var 0) (.const 1))
    rw [he] at h
    exact h
  have g0 : (.le (.const 1) (.var 0) : BExp).eval sx4 = true := rfl
  have g1 : (.le (.const 1) (.var 0) : BExp).eval
      (Function.update sx4 0 3) = true := rfl
  have g2 : (.le (.const 1) (.var 0) : BExp).eval
      (Function.update (Function.update sx4 0 3) 0 2) = true := rfl
  have g3 : (.le (.const 1) (.var 0) : BExp).eval
      (Function.update (Function.update (Function.update sx4 0 3) 0 2)
        0 1) = true := rfl
  have gf : (.le (.const 1) (.var 0) : BExp).eval
      (Function.update
        (Function.update (Function.update (Function.update sx4 0 3) 0 2)
          0 1) 0 0) = false := rfl
  have w4 : BigStepCost t3_cmd
      (Function.update
        (Function.update (Function.update (Function.update sx4 0 3) 0 2)
          0 1) 0 0)
      (Function.update
        (Function.update (Function.update (Function.update sx4 0 3) 0 2)
          0 1) 0 0) 0 := BigStepCost.whileFalse gf
  have w3 : BigStepCost t3_cmd
      (Function.update (Function.update (Function.update sx4 0 3) 0 2)
        0 1)
      (Function.update
        (Function.update (Function.update (Function.update sx4 0 3) 0 2)
          0 1) 0 0) 1 := BigStepCost.whileTrue g3 a3 w4
  have w2 : BigStepCost t3_cmd
      (Function.update (Function.update sx4 0 3) 0 2)
      (Function.update
        (Function.update (Function.update (Function.update sx4 0 3) 0 2)
          0 1) 0 0) 2 := BigStepCost.whileTrue g2 a2 w3
  have w1 : BigStepCost t3_cmd
      (Function.update sx4 0 3)
      (Function.update
        (Function.update (Function.update (Function.update sx4 0 3) 0 2)
          0 1) 0 0) 3 := BigStepCost.whileTrue g1 a1 w2
  have w0 : BigStepCost t3_cmd sx4
      (Function.update
        (Function.update (Function.update (Function.update sx4 0 3) 0 2)
          0 1) 0 0) 4 := BigStepCost.whileTrue g0 a0 w1
  exact w0

theorem t3_c_run4 :
    BigStepCost t3_cmd sx4 (Function.update sx4 0 0) 4 ∧
      BigStep t3_cmd sx4 (Function.update sx4 0 0) :=
  ⟨t3_cost4, (bigStepCost_erase _ _ _).mp ⟨4, t3_cost4⟩⟩

theorem t3_c_exhausted :
    (∃ q ∈ cutoffs 3 t3_cmd, q.guard.eval sx4 = true) ∧
      (∀ f n, BigStepCost t3_cmd sx4 f n → 3 < n) :=
  exhausted_of_no_path 3 t3_cmd sx4 t3_c_no_path

theorem t3_c_bound : 3 < 4 :=
  t3_c_exhausted.2 _ 4 t3_cost4

theorem t4_ab_cut_store3 :
    (cutoffs 5 t4_cmd).map (fun p => p.store 3) =
      [.const 0] := by
  decide

theorem t4_ab_cut_store4 :
    (cutoffs 5 t4_cmd).map (fun p => p.store 4) =
      [.const 1] := by
  decide

theorem t4_ab_cut_cost :
    (cutoffs 5 t4_cmd).map Path.cost = [5] := by
  decide

theorem t4_ab_path_store3 :
    (paths 6 t4_cmd).map (fun p => p.store 3) =
      [.const 0] := by
  decide

theorem t4_ab_path_store4 :
    (paths 6 t4_cmd).map (fun p => p.store 4) =
      [.const 0] := by
  decide

theorem t4_ab_path_cost :
    (paths 6 t4_cmd).map Path.cost = [6] := by
  decide

theorem t4_d_evals6 :
    (paths 6 t4_cmd).map (fun q => q.guard.eval s_t4) =
      [true] := by
  decide

theorem t4_cost6 (s : State) :
    BigStepCost t4_cmd s
      (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update
          (Function.update s 3 2) 3 1) 4 2) 4 1) 4 0) 3 0) 4 2) 4 1) 4 0)
      6 := by
  have a_top : BigStepCost (.assign 3 (.const 2)) s
      (Function.update s 3 2) 0 := by
    have he : ((.const 2 : AExp)).eval s = 2 := rfl
    have h := BigStepCost.assign s 3 (.const 2)
    rw [he] at h
    exact h
  have g_o1 : (.le (.const 1) (.var 3) : BExp).eval
      (Function.update s 3 2) = true := rfl
  have a_o1 : BigStepCost (.assign 3 (.sub (.var 3) (.const 1)))
      (Function.update s 3 2)
      (Function.update (Function.update s 3 2) 3 1) 0 := by
    have he : (.sub (.var 3) (.const 1) : AExp).eval
        (Function.update s 3 2) = 1 := rfl
    have h := BigStepCost.assign (Function.update s 3 2) 3
      (.sub (.var 3) (.const 1))
    rw [he] at h
    exact h
  have a_x1 : BigStepCost (.assign 4 (.const 2))
      (Function.update (Function.update s 3 2) 3 1)
      (Function.update (Function.update (Function.update s 3 2) 3 1)
        4 2) 0 := by
    have he : ((.const 2 : AExp)).eval
        (Function.update (Function.update s 3 2) 3 1) = 2 := rfl
    have h := BigStepCost.assign
      (Function.update (Function.update s 3 2) 3 1) 4 (.const 2)
    rw [he] at h
    exact h
  have g_i11 : (.le (.const 1) (.var 4) : BExp).eval
      (Function.update (Function.update (Function.update s 3 2) 3 1)
        4 2) = true := rfl
  have a_i11 : BigStepCost (.assign 4 (.sub (.var 4) (.const 1)))
      (Function.update (Function.update (Function.update s 3 2) 3 1)
        4 2)
      (Function.update
        (Function.update (Function.update (Function.update s 3 2) 3 1)
          4 2) 4 1) 0 := by
    have he : (.sub (.var 4) (.const 1) : AExp).eval
        (Function.update (Function.update (Function.update s 3 2) 3 1)
          4 2) = 1 := rfl
    have h := BigStepCost.assign
      (Function.update (Function.update (Function.update s 3 2) 3 1)
        4 2) 4
      (.sub (.var 4) (.const 1))
    rw [he] at h
    exact h
  have g_i12 : (.le (.const 1) (.var 4) : BExp).eval
      (Function.update
        (Function.update (Function.update (Function.update s 3 2) 3 1)
          4 2) 4 1) = true := rfl
  have a_i12 : BigStepCost (.assign 4 (.sub (.var 4) (.const 1)))
      (Function.update
        (Function.update (Function.update (Function.update s 3 2) 3 1)
          4 2) 4 1)
      (Function.update
        (Function.update
          (Function.update (Function.update (Function.update s 3 2) 3 1)
            4 2) 4 1) 4 0) 0 := by
    have he : (.sub (.var 4) (.const 1) : AExp).eval
        (Function.update
          (Function.update (Function.update (Function.update s 3 2) 3 1)
            4 2) 4 1) = 0 := rfl
    have h := BigStepCost.assign
      (Function.update
        (Function.update (Function.update (Function.update s 3 2) 3 1)
          4 2) 4 1) 4
      (.sub (.var 4) (.const 1))
    rw [he] at h
    exact h
  have g_i1f : (.le (.const 1) (.var 4) : BExp).eval
      (Function.update
        (Function.update
          (Function.update (Function.update (Function.update s 3 2) 3 1)
            4 2) 4 1) 4 0) = false := rfl
  have w_i_m5 : BigStepCost
      (.while (.le (.const 1) (.var 4))
        (.assign 4 (.sub (.var 4) (.const 1))))
      (Function.update
        (Function.update
          (Function.update (Function.update (Function.update s 3 2) 3 1)
            4 2) 4 1) 4 0)
      (Function.update
        (Function.update
          (Function.update (Function.update (Function.update s 3 2) 3 1)
            4 2) 4 1) 4 0) 0 :=
    BigStepCost.whileFalse g_i1f
  have w_i_m4 : BigStepCost
      (.while (.le (.const 1) (.var 4))
        (.assign 4 (.sub (.var 4) (.const 1))))
      (Function.update
        (Function.update (Function.update (Function.update s 3 2) 3 1)
          4 2) 4 1)
      (Function.update
        (Function.update
          (Function.update (Function.update (Function.update s 3 2) 3 1)
            4 2) 4 1) 4 0) 1 :=
    BigStepCost.whileTrue g_i12 a_i12 w_i_m5
  have w_i_m3 : BigStepCost
      (.while (.le (.const 1) (.var 4))
        (.assign 4 (.sub (.var 4) (.const 1))))
      (Function.update (Function.update (Function.update s 3 2) 3 1)
        4 2)
      (Function.update
        (Function.update
          (Function.update (Function.update (Function.update s 3 2) 3 1)
            4 2) 4 1) 4 0) 2 :=
    BigStepCost.whileTrue g_i11 a_i11 w_i_m4
  have s_x1 := BigStepCost.seq a_x1 w_i_m3
  have s_o1 := BigStepCost.seq a_o1 s_x1
  have g_o2 : (.le (.const 1) (.var 3) : BExp).eval
      (Function.update
        (Function.update
          (Function.update (Function.update (Function.update s 3 2) 3 1)
            4 2) 4 1) 4 0) = true := rfl
  have a_o2 : BigStepCost (.assign 3 (.sub (.var 3) (.const 1)))
      (Function.update
        (Function.update
          (Function.update (Function.update (Function.update s 3 2) 3 1)
            4 2) 4 1) 4 0)
      (Function.update
        (Function.update
          (Function.update
            (Function.update (Function.update (Function.update s 3 2) 3 1)
              4 2) 4 1) 4 0) 3 0) 0 := by
    have he : (.sub (.var 3) (.const 1) : AExp).eval
        (Function.update
          (Function.update
            (Function.update (Function.update (Function.update s 3 2) 3 1)
              4 2) 4 1) 4 0) = 0 := rfl
    have h := BigStepCost.assign
      (Function.update
        (Function.update
          (Function.update (Function.update (Function.update s 3 2) 3 1)
            4 2) 4 1) 4 0) 3
      (.sub (.var 3) (.const 1))
    rw [he] at h
    exact h
  have a_x2 : BigStepCost (.assign 4 (.const 2))
      (Function.update
        (Function.update
          (Function.update
            (Function.update (Function.update (Function.update s 3 2) 3 1)
              4 2) 4 1) 4 0) 3 0)
      (Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update (Function.update (Function.update s 3 2) 3 1)
                4 2) 4 1) 4 0) 3 0) 4 2) 0 := by
    have he : ((.const 2 : AExp)).eval
        (Function.update
          (Function.update
            (Function.update
              (Function.update (Function.update (Function.update s 3 2) 3 1)
                4 2) 4 1) 4 0) 3 0) = 2 := rfl
    have h := BigStepCost.assign
      (Function.update
        (Function.update
          (Function.update
            (Function.update (Function.update (Function.update s 3 2) 3 1)
              4 2) 4 1) 4 0) 3 0) 4
      (.const 2)
    rw [he] at h
    exact h
  have g_i21 : (.le (.const 1) (.var 4) : BExp).eval
      (Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update (Function.update (Function.update s 3 2) 3 1)
                4 2) 4 1) 4 0) 3 0) 4 2) = true := rfl
  have a_i21 : BigStepCost (.assign 4 (.sub (.var 4) (.const 1)))
      (Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update (Function.update (Function.update s 3 2) 3 1)
                4 2) 4 1) 4 0) 3 0) 4 2)
      (Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update (Function.update (Function.update s 3 2)
                  3 1) 4 2) 4 1) 4 0) 3 0) 4 2) 4 1) 0 := by
    have he : (.sub (.var 4) (.const 1) : AExp).eval
        (Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update (Function.update (Function.update s 3 2)
                  3 1) 4 2) 4 1) 4 0) 3 0) 4 2) = 1 := rfl
    have h := BigStepCost.assign
      (Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update (Function.update (Function.update s 3 2)
                3 1) 4 2) 4 1) 4 0) 3 0) 4 2) 4
      (.sub (.var 4) (.const 1))
    rw [he] at h
    exact h
  have g_i22 : (.le (.const 1) (.var 4) : BExp).eval
      (Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update (Function.update (Function.update s 3 2)
                  3 1) 4 2) 4 1) 4 0) 3 0) 4 2) 4 1) = true := rfl
  have a_i22 : BigStepCost (.assign 4 (.sub (.var 4) (.const 1)))
      (Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update (Function.update (Function.update s 3 2)
                  3 1) 4 2) 4 1) 4 0) 3 0) 4 2) 4 1)
      (Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update
                  (Function.update (Function.update (Function.update s 3 2)
                    3 1) 4 2) 4 1) 4 0) 3 0) 4 2) 4 1) 4 0) 0 := by
    have he : (.sub (.var 4) (.const 1) : AExp).eval
        (Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update
                  (Function.update (Function.update (Function.update s 3 2)
                    3 1) 4 2) 4 1) 4 0) 3 0) 4 2) 4 1) = 0 := rfl
    have h := BigStepCost.assign
      (Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update (Function.update (Function.update s 3 2)
                  3 1) 4 2) 4 1) 4 0) 3 0) 4 2) 4 1) 4
      (.sub (.var 4) (.const 1))
    rw [he] at h
    exact h
  have g_i2f : (.le (.const 1) (.var 4) : BExp).eval
      (Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update
                  (Function.update (Function.update (Function.update s 3 2)
                    3 1) 4 2) 4 1) 4 0) 3 0) 4 2) 4 1) 4 0)
      = false := rfl
  have w_i_m9 : BigStepCost
      (.while (.le (.const 1) (.var 4))
        (.assign 4 (.sub (.var 4) (.const 1))))
      (Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update
                  (Function.update (Function.update (Function.update s 3 2)
                    3 1) 4 2) 4 1) 4 0) 3 0) 4 2) 4 1) 4 0)
      (Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update
                  (Function.update (Function.update (Function.update s 3 2)
                    3 1) 4 2) 4 1) 4 0) 3 0) 4 2) 4 1) 4 0) 0 :=
    BigStepCost.whileFalse g_i2f
  have w_i_m8 : BigStepCost
      (.while (.le (.const 1) (.var 4))
        (.assign 4 (.sub (.var 4) (.const 1))))
      (Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update (Function.update (Function.update s 3 2)
                  3 1) 4 2) 4 1) 4 0) 3 0) 4 2) 4 1)
      (Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update
                  (Function.update (Function.update (Function.update s 3 2)
                    3 1) 4 2) 4 1) 4 0) 3 0) 4 2) 4 1) 4 0) 1 :=
    BigStepCost.whileTrue g_i22 a_i22 w_i_m9
  have w_i_m7 : BigStepCost
      (.while (.le (.const 1) (.var 4))
        (.assign 4 (.sub (.var 4) (.const 1))))
      (Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update (Function.update (Function.update s 3 2) 3 1)
                4 2) 4 1) 4 0) 3 0) 4 2)
      (Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update
                  (Function.update (Function.update (Function.update s 3 2)
                    3 1) 4 2) 4 1) 4 0) 3 0) 4 2) 4 1) 4 0) 2 :=
    BigStepCost.whileTrue g_i21 a_i21 w_i_m8
  have s_x2 := BigStepCost.seq a_x2 w_i_m7
  have s_o2 := BigStepCost.seq a_o2 s_x2
  have g_of : (.le (.const 1) (.var 3) : BExp).eval
      (Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update
                  (Function.update (Function.update (Function.update s 3 2)
                    3 1) 4 2) 4 1) 4 0) 3 0) 4 2) 4 1) 4 0)
      = false := rfl
  have w_o_m9 : BigStepCost
      (.while (.le (.const 1) (.var 3))
        (.seq (.assign 3 (.sub (.var 3) (.const 1)))
          (.seq (.assign 4 (.const 2))
            (.while (.le (.const 1) (.var 4))
              (.assign 4 (.sub (.var 4) (.const 1)))))))
      (Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update
                  (Function.update (Function.update (Function.update s 3 2)
                    3 1) 4 2) 4 1) 4 0) 3 0) 4 2) 4 1) 4 0)
      (Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update
                  (Function.update (Function.update (Function.update s 3 2)
                    3 1) 4 2) 4 1) 4 0) 3 0) 4 2) 4 1) 4 0) 0 :=
    BigStepCost.whileFalse g_of
  have w_o_m5 : BigStepCost
      (.while (.le (.const 1) (.var 3))
        (.seq (.assign 3 (.sub (.var 3) (.const 1)))
          (.seq (.assign 4 (.const 2))
            (.while (.le (.const 1) (.var 4))
              (.assign 4 (.sub (.var 4) (.const 1)))))))
      (Function.update
        (Function.update
          (Function.update (Function.update (Function.update s 3 2) 3 1)
            4 2) 4 1) 4 0)
      (Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update
                  (Function.update (Function.update (Function.update s 3 2)
                    3 1) 4 2) 4 1) 4 0) 3 0) 4 2) 4 1) 4 0) 3 :=
    BigStepCost.whileTrue g_o2 s_o2 w_o_m9
  have w_o_m1 : BigStepCost
      (.while (.le (.const 1) (.var 3))
        (.seq (.assign 3 (.sub (.var 3) (.const 1)))
          (.seq (.assign 4 (.const 2))
            (.while (.le (.const 1) (.var 4))
              (.assign 4 (.sub (.var 4) (.const 1)))))))
      (Function.update s 3 2)
      (Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update
                  (Function.update (Function.update (Function.update s 3 2)
                    3 1) 4 2) 4 1) 4 0) 3 0) 4 2) 4 1) 4 0) 6 :=
    BigStepCost.whileTrue g_o1 s_o1 w_o_m5
  have w_top : BigStepCost t4_cmd s
      (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update
          (Function.update s 3 2) 3 1) 4 2) 4 1) 4 0) 3 0) 4 2) 4 1) 4 0)
      6 :=
    BigStepCost.seq a_top w_o_m1
  exact w_top

theorem t4_d_run :
    ∃ q ∈ paths 6 t4_cmd,
      q.guard.eval s_t4 = true ∧
        (Store.eval q.store s_t4) 3 = 0 ∧
        (Store.eval q.store s_t4) 4 = 0 ∧ q.cost = 6 ∧
        BigStepCost t4_cmd s_t4
          (Function.update (Function.update (Function.update
            (Function.update (Function.update (Function.update
              (Function.update (Function.update (Function.update s_t4 3 2)
                3 1) 4 2) 4 1) 4 0) 3 0) 4 2) 4 1) 4 0) 6 ∧
        BigStep t4_cmd s_t4
          (Function.update (Function.update (Function.update
            (Function.update (Function.update (Function.update
              (Function.update (Function.update (Function.update s_t4 3 2)
                3 1) 4 2) 4 1) 4 0) 3 0) 4 2) 4 1) 4 0) := by
  have hlen : (paths 6 t4_cmd).length = 1 := t4_b.2.1
  obtain ⟨q, hpaths⟩ : ∃ q, paths 6 t4_cmd = [q] := by
    match h : paths 6 t4_cmd with
    | [] => simp [h] at hlen
    | [q] => exact ⟨q, rfl⟩
    | _ :: _ :: _ =>
      simp only [h, List.length_cons] at hlen
      have hfalse : False := by omega
      exact False.elim hfalse
  have hmem : q ∈ paths 6 t4_cmd := by
    rw [hpaths]
    simp
  have hev : q.guard.eval s_t4 = true := by
    have h := t4_d_evals6
    rw [hpaths] at h
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at h
    exact h.1
  have hs3 : q.store 3 = .const 0 := by
    have h := t4_ab_path_store3
    rw [hpaths] at h
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at h
    exact h.1
  have hs4 : q.store 4 = .const 0 := by
    have h := t4_ab_path_store4
    rw [hpaths] at h
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at h
    exact h.1
  have hcc : q.cost = 6 := by
    have h := t4_ab_path_cost
    rw [hpaths] at h
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at h
    exact h.1
  have hv3 : (Store.eval q.store s_t4) 3 = 0 := by
    have happ : (Store.eval q.store s_t4) 3
        = (q.store 3).eval s_t4 := rfl
    rw [happ, hs3]
    rfl
  have hv4 : (Store.eval q.store s_t4) 4 = 0 := by
    have happ : (Store.eval q.store s_t4) 4
        = (q.store 4).eval s_t4 := rfl
    rw [happ, hs4]
    rfl
  have hrun := t4_cost6 s_t4
  have hbig := (bigStepCost_erase _ _ _).mp ⟨6, hrun⟩
  exact ⟨q, hmem, hev, hv3, hv4, hcc, hrun, hbig⟩

theorem t4_d_hno (q : Path) (hm : q ∈ paths 5 t4_cmd) :
    q.guard.eval s_t4 ≠ true := by
  have hlen : (paths 5 t4_cmd).length = 0 := t4_a.2.1
  match hpaths : paths 5 t4_cmd with
  | [] =>
    rw [hpaths] at hm
    simp at hm
  | _ :: _ =>
    rw [hpaths] at hlen
    simp only [List.length_cons] at hlen
    omega

theorem t4_d_complete :
    ∃ q ∈ paths 6 t4_cmd,
      q.guard.eval s_t4 = true ∧ q.cost = 6 := by
  have hrun := t4_cost6 s_t4
  have hle : 6 ≤ 6 := by omega
  obtain ⟨q, hmem, hguard, -, hcost⟩ :=
    paths_complete 6 t4_cmd s_t4 _ 6 hrun hle
  exact ⟨q, hmem, hguard, hcost⟩

theorem t4_d_exhausted :
    (∃ q ∈ cutoffs 5 t4_cmd, q.guard.eval s_t4 = true) ∧
      (∀ f n, BigStepCost t4_cmd s_t4 f n → 5 < n) :=
  exhausted_of_no_path 5 t4_cmd s_t4 t4_d_hno

theorem t4_d_bound : 5 < 6 :=
  t4_d_exhausted.2 _ 6 (t4_cost6 s_t4)

theorem t5a_evals :
    (paths 0 t5a_cmd).map (fun q => q.guard.eval sx2) =
      [true, false] := by
  decide

theorem t5a_vals :
    (paths 0 t5a_cmd).map
        (fun q => (Store.eval q.store sx2) 1) = [1, 2] := by
  decide

theorem t5a_cover :
    ∃ q ∈ paths 0 t5a_cmd,
      q.guard.eval sx2 = true ∧
        (Store.eval q.store sx2) 1 = 1 ∧
        BigStepCost t5a_cmd sx2 (Store.eval q.store sx2)
          q.cost := by
  have hlen : (paths 0 t5a_cmd).length = 2 := t5a_len
  match hpaths : paths 0 t5a_cmd with
  | [] => simp [hpaths] at hlen
  | [_] => simp [hpaths] at hlen
  | q0 :: _q1 :: _rest =>
    have hmem0 : q0 ∈ paths 0 t5a_cmd := by
      rw [hpaths]; simp
    have hev := t5a_evals
    rw [hpaths] at hev
    simp at hev
    obtain ⟨heval, -, -⟩ := hev
    have hvv := t5a_vals
    rw [hpaths] at hvv
    simp at hvv
    obtain ⟨hval, -, -⟩ := hvv
    have hsnd :=
      (paths_sound 0 t5a_cmd q0 sx2 hmem0 heval).1
    exact ⟨q0, by simp, heval, hval, hsnd⟩

theorem t5b_guard :
    (paths 0 t5b_cmd).map Path.guard =
      [.and (.truth true) (.truth true)] := by
  decide

theorem t5b_store1 :
    (paths 0 t5b_cmd).map (fun p => p.store 1) =
      [.const 2] := by
  decide

theorem t_bridge_afold_out :
    afold t_bridge (.add (.var 0) (.var 1)) =
      .add (.const 3) (.var 1) := by
  decide

theorem t_bexp_subst_var :
    BExp.subst (fun x => .add (.var x) (.const 1))
        (.le (.var 0) (.const 3)) =
      .le (.add (.var 0) (.const 1)) (.const 3) := by
  rfl

theorem t_bexp_subst_var_eval :
    (BExp.subst (fun x => .add (.var x) (.const 1))
      (.le (.var 0) (.const 3))).eval sx2 = true := by
  rw [BExp.eval_subst]
  rfl

#print axioms t1_a
#print axioms t1_b
#print axioms t1_c_run
#print axioms t2_a
#print axioms t2_cover
#print axioms t3_a_len
#print axioms t4_a
#print axioms t4_b
#print axioms t4_c
#print axioms t5a_len
#print axioms t5b_len
#print axioms t5b_prune
#print axioms t5c_len
#print axioms t_bexp_subst
#print axioms t_bridge_afold
#print axioms t_bridge_bfold
#print axioms t_bridge_approx
#print axioms t_init_eval
#print axioms t_update_eval
#print axioms t_erase
#print axioms t_sound
#print axioms t_complete
#print axioms t_cutcost
#print axioms t_exh
#print axioms t1_c_guards
#print axioms t1_c_stores
#print axioms t1_c_costs
#print axioms t1_c_sound
#print axioms t2_a_guards
#print axioms t2_a_store1
#print axioms t2_a_store2
#print axioms t2_a_costs
#print axioms t2_c_then
#print axioms t2_c_else
#print axioms t3_a_costs_all
#print axioms t3_a_stores
#print axioms t3_a_costs
#print axioms t3_b_evals
#print axioms t3_b_cover
#print axioms t3_c_evals
#print axioms t3_c_no_path
#print axioms t3_c_cut_evals
#print axioms t3_c_cut_cost
#print axioms t3_c_paths4_costs
#print axioms t3_c_paths4_evals
#print axioms t3_cost4
#print axioms t3_c_run4
#print axioms t3_c_exhausted
#print axioms t3_c_bound
#print axioms t4_ab_cut_store3
#print axioms t4_ab_cut_store4
#print axioms t4_ab_cut_cost
#print axioms t4_ab_path_store3
#print axioms t4_ab_path_store4
#print axioms t4_ab_path_cost
#print axioms t4_d_evals6
#print axioms t4_cost6
#print axioms t4_d_run
#print axioms t4_d_hno
#print axioms t4_d_complete
#print axioms t4_d_exhausted
#print axioms t4_d_bound
#print axioms t5a_evals
#print axioms t5a_vals
#print axioms t5a_cover
#print axioms t5b_guard
#print axioms t5b_store1
#print axioms t_bridge_afold_out
#print axioms t_bexp_subst_var
#print axioms t_bexp_subst_var_eval
#print axioms Cslib.IMP.AExp.subst
#print axioms Cslib.IMP.BExp.subst
#print axioms Cslib.IMP.BigStepCost
#print axioms Cslib.IMP.Symbolic.Store
#print axioms Cslib.IMP.Symbolic.Store.init
#print axioms Cslib.IMP.Symbolic.Store.eval
#print axioms Cslib.IMP.Symbolic.tableStore
#print axioms Cslib.IMP.Symbolic.Path
#print axioms Cslib.IMP.Symbolic.Path.init
#print axioms Cslib.IMP.Symbolic.Path.assign
#print axioms Cslib.IMP.Symbolic.Path.assume
#print axioms Cslib.IMP.Symbolic.Path.tick
#print axioms Cslib.IMP.Symbolic.Leaf
#print axioms Cslib.IMP.Symbolic.Leaf.bind
#print axioms Cslib.IMP.Symbolic.Leaf.done?
#print axioms Cslib.IMP.Symbolic.Leaf.cut?
#print axioms Cslib.IMP.Symbolic.loop
#print axioms Cslib.IMP.Symbolic.run
#print axioms Cslib.IMP.Symbolic.leaves
#print axioms Cslib.IMP.Symbolic.paths
#print axioms Cslib.IMP.Symbolic.cutoffs
#print axioms Cslib.IMP.AExp.eval_subst
#print axioms Cslib.IMP.BExp.eval_subst
#print axioms Cslib.IMP.bigStepCost_erase
#print axioms Cslib.IMP.Symbolic.Store.eval_init
#print axioms Cslib.IMP.Symbolic.Store.eval_update
#print axioms Cslib.IMP.Symbolic.afold_eq_subst
#print axioms Cslib.IMP.Symbolic.bfold_eq_subst
#print axioms Cslib.IMP.Symbolic.constApprox_iff
#print axioms Cslib.IMP.Symbolic.Path.assume_eq_none
#print axioms Cslib.IMP.Symbolic.paths_sound
#print axioms Cslib.IMP.Symbolic.paths_complete
#print axioms Cslib.IMP.Symbolic.leaves_cover
#print axioms Cslib.IMP.Symbolic.cutoffs_cost
#print axioms Cslib.IMP.Symbolic.exhausted_of_no_path

end Cslib.IMP.SymbolicTests
