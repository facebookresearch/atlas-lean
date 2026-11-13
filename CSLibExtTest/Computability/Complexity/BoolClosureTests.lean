/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Complexity.BoolClosure
import CSLibExt.Computability.Complexity.PathInP
import CSLibExt.Computability.Complexity.Karp.ThreeSatComplete

/-!
# Concrete regression clients for canonical P Boolean closures

The executable probes compare actual stored machine configurations, including
all stacks and control state. The one-fewer-step and wrong-order probes must
reject, not merely check that the intended output occurs somewhere.
-/

@[expose] public section

set_option autoImplicit false

open Turing Function MetaMathlibExt TM2Program ComplexityTheory
open Cslib.Complexity Cslib.Complexity.BoolClosure Cslib.Complexity.DenseSAT

namespace BoolClosureTest

private theorem singleton_false :
    Run singletonTM.m 1 (initList singletonTM [false])
      (haltList singletonTM [true, false, false]) := singletonTM_run false

private theorem singleton_true :
    Run singletonTM.m 1 (initList singletonTM [true])
      (haltList singletonTM [true, true, false]) := singletonTM_run true

private theorem singleton_zero_rejected (b : Bool) :
    ¬ Run singletonTM.m 0 (initList singletonTM [b])
      (haltList singletonTM [true, b, false]) := by
  intro h
  have hl := congrArg (fun c => c.map TM2.Cfg.l) h
  cases hl

private theorem singleton_encoding (b : Bool) :
    BitstringEncoding.bitEncode [b] = [true, b, false] := rfl

private def checkDup (steps : ℕ) (x : List Bool) (expected : List Verifier.G) : Bool :=
  letI : DecidableEq (dupTM.Γ 0) := inferInstanceAs (DecidableEq Bool)
  letI : DecidableEq (dupTM.Γ 1) := inferInstanceAs (DecidableEq Verifier.G)
  letI : DecidableEq (dupTM.Γ 2) := inferInstanceAs (DecidableEq Bool)
  match (flip bind dupTM.step)^[steps] (some (initList dupTM x)) with
  | none => false
  | some c => decide ((c.l : Option (Fin 6)) = none ∧ (c.var : Bool) = false ∧
      (c.stk 0 : List Bool) = [] ∧ (c.stk 1 : List Verifier.G) = expected ∧
      (c.stk 2 : List Bool) = [])

private theorem dup_empty : checkDup 6 [] (Verifier.pairEncode ([], [])) = true := by decide
private theorem dup_singleton :
    checkDup 10 [true] (Verifier.pairEncode ([true], [true])) = true := by decide
private theorem dup_nonpalindrome :
    checkDup 18 [true, false, false]
      (Verifier.pairEncode ([true, false, false], [true, false, false])) = true := by decide
private theorem dup_long_nonpalindrome :
    checkDup 26 [false, true, true, false, true]
      (Verifier.pairEncode ([false, true, true, false, true], [false, true, true, false, true])) = true := by
  decide
private theorem dup_empty_short : checkDup 5 [] (Verifier.pairEncode ([], [])) = false := by decide
private theorem dup_nonpalindrome_short :
    checkDup 17 [true, false, false]
      (Verifier.pairEncode ([true, false, false], [true, false, false])) = false := by decide
private theorem dup_reversed_rejected :
    checkDup 18 [true, false, false]
      (Verifier.pairEncode ([false, false, true], [true, false, false])) = false := by decide

private def checkSwap (steps : ℕ) (a b : List Bool) (expected : List Verifier.G) : Bool :=
  letI : DecidableEq (swapTM.Γ 0) := inferInstanceAs (DecidableEq Verifier.G)
  letI : DecidableEq (swapTM.Γ 1) := inferInstanceAs (DecidableEq Bool)
  letI : DecidableEq (swapTM.Γ 2) := inferInstanceAs (DecidableEq Bool)
  match (flip bind swapTM.step)^[steps] (some (initList swapTM (Verifier.pairEncode (a, b)))) with
  | none => false
  | some c => decide ((c.l : Option (Fin 7)) = none ∧ (c.var : Bool) = false ∧
      (c.stk 0 : List Verifier.G) = expected ∧ (c.stk 1 : List Bool) = [] ∧
      (c.stk 2 : List Bool) = [])

private theorem swap_same_io : swapTM.k₀ = swapTM.k₁ := rfl
private theorem swap_empty : checkSwap 7 [] [] (Verifier.pairEncode ([], [])) = true := by decide
private theorem swap_left_only :
    checkSwap 9 [true] [] (Verifier.pairEncode ([], [true])) = true := by decide
private theorem swap_right_only :
    checkSwap 9 [] [false] (Verifier.pairEncode ([false], [])) = true := by decide
private theorem swap_asymmetric :
    checkSwap 17 [true, false, false] [false, true]
      (Verifier.pairEncode ([false, true], [true, false, false])) = true := by decide
private theorem swap_other_asymmetric :
    checkSwap 15 [false] [true, true, false]
      (Verifier.pairEncode ([true, true, false], [false])) = true := by decide
private theorem swap_empty_short : checkSwap 6 [] [] (Verifier.pairEncode ([], [])) = false := by decide
private theorem swap_asymmetric_short :
    checkSwap 16 [true, false, false] [false, true]
      (Verifier.pairEncode ([false, true], [true, false, false])) = false := by decide
private theorem swap_unswapped_rejected :
    checkSwap 9 [true] [] (Verifier.pairEncode ([true], [])) = false := by decide

private def checkHeads (steps : ℕ) (op : Bool → Bool → Bool) (x w : List Bool)
    (expected : Bool) : Bool :=
  let S : Bool → List Bool := update (update (fun _ => []) false x) true w
  match (flip bind (TM2.step (headsComp op).prog))^[steps] (some ⟨some 0, false, S⟩) with
  | none => false
  | some c => decide (c.l = some (if expected then 3 else 4) ∧
      c.var = x.headD false ∧ c.stk false = x ∧ c.stk true = w)

private theorem heads_direction_true :
    checkHeads 2 (fun a b => a && !b) [false, true] [true] true = true := by decide
private theorem heads_direction_false :
    checkHeads 2 (fun a b => a && !b) [true] [false, true] false = true := by decide
private theorem heads_wrong_order_rejected :
    checkHeads 2 (fun a b => a && !b) [false, true] [true] false = false := by decide
private theorem heads_empty : checkHeads 2 Bool.or [] [] false = true := by decide
private theorem heads_missing_second : checkHeads 2 Bool.and [true] [] false = true := by decide
private theorem heads_union : checkHeads 2 Bool.or [true] [false] true = true := by decide
private theorem heads_xor : checkHeads 2 Bool.xor [false, true] [true] true = true := by decide
private theorem heads_complement :
    checkHeads 2 (fun a _ => !a) [true] [] true = true := by decide
private theorem heads_one_step_rejected :
    checkHeads 1 (fun a b => a && !b) [false, true] [true] true = false := by decide

-- These witnesses are actual canonical machines, not assumptions asserting membership.
private def headLanguage (x : List Bool) : Bool := x.headD false
private theorem headLanguage_mem_P : headLanguage ∈ P :=
  isPolyTime_dup.comp (isPolyTime_heads (fun a _ => a))
private def oppositeLanguage : DecisionProblem := headLanguageᶜ
private theorem oppositeLanguage_mem_P : oppositeLanguage ∈ P := compl_mem_P headLanguage_mem_P

private def intersectionLanguage : DecisionProblem := headLanguage ⊓ oppositeLanguage
private theorem intersection_mem_P : intersectionLanguage ∈ P :=
  inf_mem_P headLanguage_mem_P oppositeLanguage_mem_P
private def unionLanguage : DecisionProblem := headLanguage ⊔ oppositeLanguage
private theorem union_mem_P : unionLanguage ∈ P :=
  sup_mem_P headLanguage_mem_P oppositeLanguage_mem_P
private def directionalLanguage (x : List Bool) : Bool := headLanguage x && !oppositeLanguage x
private theorem directional_mem_P : directionalLanguage ∈ P :=
  combine_mem_P (fun a b => a && !b) headLanguage_mem_P oppositeLanguage_mem_P
private theorem xor_mem_P : (fun x => Bool.xor (headLanguage x) (oppositeLanguage x)) ∈ P :=
  combine_mem_P Bool.xor headLanguage_mem_P oppositeLanguage_mem_P

private theorem head_true_literal : headLanguage [true, false, false] = true := rfl
private theorem head_false_literal : headLanguage [] = false := rfl
private theorem opposite_false_literal : oppositeLanguage [true, false, false] = false := rfl
private theorem opposite_true_literal : oppositeLanguage [] = true := rfl
private theorem intersection_nonvacuity :
    intersectionLanguage [true, false, false] = false ∧ headLanguage [true, false, false] = true := by
  decide
private theorem union_nonvacuity : unionLanguage [] = true ∧ headLanguage [] = false := by decide
private theorem directional_nonvacuity :
    directionalLanguage [true, false, false] = true ∧
      (oppositeLanguage [true, false, false] && !headLanguage [true, false, false]) = false := by
  decide
private theorem directional_false_literal : directionalLanguage [] = false := rfl

-- Public clients on main exercise the adapted map and Bool-to-list direction.
private theorem reduce3_map_first :
    IsPolyTime (fun p : List Bool × List Bool => (Karp.reduce3 p.1, p.2)) :=
  Karp.isPolyTime_reduce3.map_fst

private theorem path_wrap_map :
    IsPolyTime (fun p : List Bool × List Bool => ([Path.pathDec p.1], p.2)) :=
  (Path.pathDec_mem_P.comp isPolyTime_singleton).map_fst
private theorem path_complement : Path.pathDecᶜ ∈ P := compl_mem_P Path.pathDec_mem_P
private theorem path_intersection : Path.pathDec ⊓ headLanguage ∈ P :=
  inf_mem_P Path.pathDec_mem_P headLanguage_mem_P
private theorem path_union : Path.pathDec ⊔ headLanguage ∈ P :=
  sup_mem_P Path.pathDec_mem_P headLanguage_mem_P

private theorem singleton_output_bound :
    ∃ q : Polynomial ℕ, ∀ x : List Bool, ([headLanguage x] : List Bool).length ≤ q.eval x.length :=
  (headLanguage_mem_P.comp isPolyTime_singleton).length_bound

private theorem swap_twice :
    IsPolyTime (fun p : List Bool × List Bool => p) :=
  isPolyTime_swap.comp isPolyTime_swap

end BoolClosureTest
