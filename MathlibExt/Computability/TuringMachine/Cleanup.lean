/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.TuringMachine.Program

/-!
# Emptying work stacks at the end of a `TM2` run

`FinTM2` outputs (`haltList`) require every stack except the output stack to be empty at the
halt. `cleanS ks self next` empties the stacks `ks` in rounds: each round pops every stack of
`ks` once and records in the state's flag bit (`TM2Program.Flag`) whether some pop found a
symbol; a round that found nothing goes to `next`. Stacks outside `ks` are untouched.

* `stepAux_popAll`: one round as a single `stepAux`.
* `clean_run`: if every stack of `ks` has at most `m` symbols, `next` is reached within `m + 1`
  steps, with flag `false`, the stacks of `ks` empty and the others unchanged.
-/

@[expose] public section

namespace MetaMathlibExt.TM2Program

open Turing Function

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} [Flag σ]

/-- Pop every stack of `ks` once, or-ing into the flag whether some pop found a symbol. -/
def popAll : List K → TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ σ
  | [], q => q
  | k :: ks, q => .pop k (fun s o => Flag.tag (Flag.untag s || o.isSome)) (popAll ks q)

/-- One cleanup round at label `self`: pop every stack of `ks` once; repeat if something was
popped, otherwise go to `next`. -/
def cleanS (ks : List K) (self next : Λ) : TM2.Stmt Γ Λ σ :=
  .load (fun _ => Flag.tag false) <| popAll ks <|
    .branch Flag.untag (.goto fun _ => self) (.goto fun _ => next)

theorem stepAux_popAll (q : TM2.Stmt Γ Λ σ) :
    ∀ (ks : List K), ks.Nodup → ∀ (b : Bool) (S : ∀ k, List (Γ k)),
      TM2.stepAux (popAll ks q) (Flag.tag b) S =
        TM2.stepAux q (Flag.tag (b || ks.any fun k => !(S k).isEmpty))
          (fun k => if k ∈ ks then (S k).tail else S k) := by
  intro ks
  induction ks with
  | nil => intro _ b S; simp [popAll]
  | cons k ks ih =>
      intro hnd v S
      have hk : k ∉ ks := (List.nodup_cons.1 hnd).1
      simp only [popAll, TM2.stepAux, Flag.untag_tag]
      rw [ih (List.nodup_cons.1 hnd).2]
      have hne : ∀ k', k' ∈ ks → k' ≠ k := fun k' hk' he => hk (he ▸ hk')
      have hany : (ks.any fun k' => !(update S k (S k).tail k').isEmpty) =
          ks.any fun k' => !(S k').isEmpty := by
        apply Bool.eq_iff_iff.2
        simp only [List.any_eq_true]
        exact ⟨fun ⟨k', hk', h⟩ => ⟨k', hk', by rwa [update_of_ne (hne k' hk')] at h⟩,
          fun ⟨k', hk', h⟩ => ⟨k', hk', by rwa [update_of_ne (hne k' hk')]⟩⟩
      congr 1
      · rw [hany]
        cases hS : S k <;> simp [hS]
      · funext k'
        by_cases h : k' = k
        · subst h; simp [hk]
        · by_cases h' : k' ∈ ks
          · simp [h, h']
          · simp [h, h']

/-- **Cleanup**: with every stack of `ks` holding at most `m` symbols, `cleanS ks self next`
reaches `next` within `m + 1` steps, with flag `false`, the stacks of `ks` emptied and the
others unchanged. -/
theorem clean_run {M : Λ → TM2.Stmt Γ Λ σ} {ks : List K} {self next : Λ}
    (hM : M self = cleanS ks self next) (hks : ks.Nodup) :
    ∀ (m : ℕ) (v : σ) (S : ∀ k, List (Γ k)), (∀ k ∈ ks, (S k).length ≤ m) →
      RunLe M (m + 1) ⟨some self, v, S⟩
        ⟨some next, Flag.tag false, fun k => if k ∈ ks then [] else S k⟩ := by
  intro m
  induction m with
  | zero =>
      intro v S hl
      have he : ∀ k ∈ ks, S k = [] := fun k hk =>
        List.eq_nil_of_length_eq_zero (Nat.le_zero.1 (hl k hk))
      refine Run.le (Run.single ?_) le_rfl
      simp only [hM, cleanS, TM2.stepAux]
      rw [stepAux_popAll _ _ hks]
      have hany : (ks.any fun k => !(S k).isEmpty) = false := by
        rw [List.any_eq_false]
        intro k hk
        simp [he k hk]
      simp only [TM2.stepAux, hany, Bool.false_or, Flag.untag_tag, Bool.cond_false]
      congr 2
      funext k
      by_cases hk : k ∈ ks <;> simp [hk, he]
  | succ m ih =>
      intro v S hl
      set S' : ∀ k, List (Γ k) := fun k => if k ∈ ks then (S k).tail else S k with hS'
      have hl' : ∀ k ∈ ks, (S' k).length ≤ m := by
        intro k hk
        simp only [hS', hk, ite_true, List.length_tail]
        have := hl k hk; omega
      by_cases hany : (ks.any fun k => !(S k).isEmpty) = true
      · have r := ih (Flag.tag true) S' hl'
        have hfin : (fun k => if k ∈ ks then [] else S' k) = fun k => if k ∈ ks then [] else S k :=
          by funext k; by_cases hk : k ∈ ks <;> simp [hS', hk]
        rw [hfin] at r
        refine (Run.head ?_ (Run.zero _) |>.le le_rfl).trans r |>.mono (by omega)
        simp only [TM2.step, hM, cleanS, TM2.stepAux, Option.some.injEq]
        rw [stepAux_popAll _ _ hks]
        simp [TM2.stepAux, hany, hS']
      · have he : ∀ k ∈ ks, S k = [] := by
          intro k hk
          simp only [Bool.not_eq_true, List.any_eq_false, Bool.not_eq_false',
            List.isEmpty_iff] at hany
          exact hany k hk
        refine Run.le (Run.single ?_) (by omega)
        simp only [hM, cleanS, TM2.stepAux]
        rw [stepAux_popAll _ _ hks]
        simp only [Bool.not_eq_true] at hany
        simp only [TM2.stepAux, hany, Bool.false_or, Flag.untag_tag, Bool.cond_false]
        congr 2
        funext k
        by_cases hk : k ∈ ks <;> simp [hk, he]

end MetaMathlibExt.TM2Program
