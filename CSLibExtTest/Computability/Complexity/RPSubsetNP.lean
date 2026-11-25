/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Complexity.RPSubsetNP
import CSLibExt.Computability.Complexity.Host

/-!
# RP certificates at the length boundary

The verifier accepts every empty tape. With one random bit it recognizes inputs starting with
true, at the exact one-half threshold. With zero random bits it recognizes every input.
-/

namespace MetaMathlibExt.Complexity.KeyTheorems.RPSubsetNP.Tests

open Turing Function MetaMathlibExt.TM2Program ComplexityTheory
open Cslib.Complexity Cslib.Complexity.Classes

private def verify (x w : List Bool) := w.isEmpty || (w.headD false && x.headD false)

private abbrev component : Host.Comp where
  K := Bool
  Γ _ := Bool
  L := Option Bool
  prog
    | none => .peek true (fun _ o => o.isNone) <| .branch id (.goto fun _ => some true) <|
        .peek true (fun _ o => o.getD false) <| .branch id
          (.peek false (fun _ o => o.getD false) (.goto some)) (.goto fun _ => some false)
    | some _ => .halt
  ks := [false, true]
  ks_nodup := by decide
  mem_ks k := by cases k <;> decide

private theorem verify_polyTime : IsPolyTime (fun q : List Bool × List Bool => verify q.1 q.2) := by
  apply Host.isPolyTime_verifier (c := component) (cX := false) (cW := true) (gX := id) (gW := id)
    (start := none) (yes := some true) (no := some false) verify 1 (by decide) (by decide) rfl rfl
  intro x w
  let S := update (update (fun _ : Bool => []) false x) true w
  simp only [List.map_id]
  refine ⟨verify x w, S, Run.le (n := 1) (Run.single ?_) (by simp)⟩
  cases w with
  | nil => rfl
  | cons b w =>
    cases b
    · rfl
    · cases x with
      | nil => rfl
      | cons a x => cases a <;> rfl

-- On the negative input [], reusing the verifier directly would accept a short certificate.
example : verify [] [] = true ∧ ∀ w : List Bool, w.length = 1 → verify [] w = false := by
  refine ⟨rfl, fun w hw => ?_⟩
  cases w <;> simp_all [verify]

example : (fun x : List Bool => x.headD false) ∈ NP := by
  apply rp_subset_np
  refine ⟨1, fun q => verify q.1 q.2, verify_polyTime, fun x => ?_⟩
  have hm : (1 : Polynomial ℕ).eval x.length = 1 := Polynomial.eval_one
  generalize (1 : Polynomial ℕ).eval x.length = m at hm ⊢
  subst m
  have singleton : {r : Fin 1 → Bool | r 0 = true} = {fun _ => true} := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨fun h => funext fun i => Subsingleton.elim i 0 ▸ h, fun h => congrFun h 0⟩
  have hv (r : Fin 1 → Bool) : verify x (List.ofFn r) = (r 0 && x.headD false) := by
    rw [List.ofFn_succ]
    rfl
  simp only [hv]
  cases x.headD false <;> simp [singleton]

example : (fun _ : List Bool => true) ∈ NP := by
  apply rp_subset_np
  refine ⟨0, fun q => verify q.1 q.2, verify_polyTime, fun x => ?_⟩
  simp [verify]

end MetaMathlibExt.Complexity.KeyTheorems.RPSubsetNP.Tests
