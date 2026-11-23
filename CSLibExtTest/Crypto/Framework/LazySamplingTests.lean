/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.LazySampling
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases

/-!
# Tests for adaptive lazy sampling and the switching lemma

All on `D = Fin 3`.
* Consistency: a recorded query is answered from the table.
* Fresh answers: the lazy random function answers a fresh query `0` with probability `1/3`; the
  lazy random permutation with table `{0 ↦ 2}` answers a fresh query `0` with probability `1/2`
  and never `2` (a random function would give `1/3` to each).
* `collide` queries `0`, then adaptively queries `1` or `2` depending on the first answer, and
  outputs whether the two answers agree. Against a random function it outputs `1` with probability
  exactly `1/3` (eager, by counting the 9 of 27 functions; and lazily, through `lazyRF_map_fst`);
  against a random permutation never. Its advantage `1/3` equals `collisionProb (Fin 3) 2` and the
  explicit bound `q (q - 1) / (2 N) = 1/3`: the switching lemma is tight here.
* A one-query distinguisher has advantage `0` by the switching lemma, so the random-permutation
  probability `1/3` follows from the random-function count.
-/

@[expose] public section

namespace Cslib.Crypto.FrameworkTests.LazySampling

open Cslib.Crypto.Framework Cslib.Crypto.Framework.LazySampling Cslib.Probability.PMF Finset

/-- The table `{0 ↦ 2}`. -/
def T₀ : Table (Fin 3) (Fin 3) := fun z => if z = 0 then some 2 else none

/-- Consistency: the recorded query `0` gets its recorded answer `2`, and the table is kept. -/
example : rfStep T₀ 0 = PMF.pure (2, T₀) := rfStep_of_some (by decide)

example : rpStep T₀ 0 = PMF.pure (2, T₀) := rpStep_of_some (by decide)

/-- The lazy random function answers a fresh query uniformly: `0` with probability `1/3`. -/
example : (rfStep T₀ 1).map Prod.fst 0 = 3⁻¹ := by
  rw [rfStep_map_fst_of_none (by decide), uniformOfFintype_apply, Fintype.card_fin]
  norm_num

theorem freshSet_T₀ : freshSet T₀ = {0, 1} := by
  ext y
  rw [mem_freshSet]
  fin_cases y <;> simp [T₀]

/-- The lazy random permutation answers a fresh query uniformly among the unused values `0, 1`:
`0` with probability `1/2`. -/
example : (rpStep T₀ 1).map Prod.fst 0 = 2⁻¹ := by
  have hF : (freshSet T₀).Nonempty := ⟨0, by simp [freshSet_T₀]⟩
  rw [rpStep_map_fst_of_none (by decide) hF, uniformOfFinset_apply, freshSet_T₀]
  simp

/-- The used value `2` is never a fresh answer of the lazy random permutation. -/
example : (rpStep T₀ 1).map Prod.fst 2 = 0 := by
  have hF : (freshSet T₀).Nonempty := ⟨0, by simp [freshSet_T₀]⟩
  rw [rpStep_map_fst_of_none (by decide) hF, uniformOfFinset_apply, freshSet_T₀]
  simp

/-- Query `0`; on answer `y`, query `1` if `y = 0` and `2` otherwise (an adaptive choice); output
whether the two answers agree. -/
def collide : OracleComp (Fin 3) (Fin 3) Bool :=
  .query 0 fun y => .query (if y = 0 then 1 else 2) fun z => .done (decide (y = z))

theorem collide_bounded : FreeM.IsQueryBounded 2 collide := fun _ _ => trivial

/-- The second query is never `0`, so a permutation never makes `collide` output `1`. -/
theorem collide_run_perm (π : Equiv.Perm (Fin 3)) : collide.run π = false := by
  change decide (π 0 = π (if π 0 = 0 then 1 else 2)) = false
  rw [decide_eq_false_iff_not]
  split_ifs <;> exact π.injective.ne (by decide)

/-- Against a uniformly random function, `collide` outputs `1` with probability `1/3`. -/
theorem collide_rf :
    winProb ((uniformOfFintype (Fin 3 → Fin 3)).map fun f => collide.run f) = 1 / 3 := by
  rw [winProb_map_uniform]
  have h : (univ.filter fun f : Fin 3 → Fin 3 => collide.run f = true).card = 9 := by decide
  rw [h]
  norm_num

/-- Against a uniformly random permutation, `collide` never outputs `1`. -/
theorem collide_rp :
    winProb ((uniformOfFintype (Equiv.Perm (Fin 3))).map
      fun π : Equiv.Perm (Fin 3) => collide.run ⇑π) = 0 := by
  rw [map_congr_support _ fun π _ => collide_run_perm π]
  change winProb (PMF.map (Function.const _ false) _) = 0
  rw [PMF.map_const]
  simp

/-- The lazy random function gives the same probability `1/3` (lazy = eager). -/
example : winProb ((lazyRF collide Table.empty).map Prod.fst) = 1 / 3 := by
  rw [lazyRF_map_fst, collide_rf]

/-- The lazy random permutation gives the same probability `0` (lazy = eager). -/
example : winProb ((lazyRP collide Table.empty).map Prod.fst) = 0 := by
  rw [lazyRP_map_fst, collide_rp]

theorem collisionProb_fin3_two : Birthday.collisionProb (Fin 3) 2 = 1 / 3 := by
  rw [Birthday.collisionProb_eq]
  norm_num [Nat.descFactorial]

/-- The switching lemma applied to the adaptive `collide`: advantage at most `1/3`. -/
example : advantage ((uniformOfFintype (Fin 3 → Fin 3)).map fun f => collide.run f)
    ((uniformOfFintype (Equiv.Perm (Fin 3))).map fun π : Equiv.Perm (Fin 3) => collide.run ⇑π) ≤
      1 / 3 := by
  have := switching_lemma collide collide_bounded
  rwa [collisionProb_fin3_two] at this

/-- **Tightness**: `collide`'s advantage is exactly the bound `collisionProb (Fin 3) 2 = 1/3`. -/
example : advantage ((uniformOfFintype (Fin 3 → Fin 3)).map fun f => collide.run f)
    ((uniformOfFintype (Equiv.Perm (Fin 3))).map fun π : Equiv.Perm (Fin 3) => collide.run ⇑π) =
      Birthday.collisionProb (Fin 3) 2 := by
  rw [advantage, collide_rf, collide_rp, collisionProb_fin3_two]
  norm_num

/-- The explicit form `q (q - 1) / (2 N)` is also `1/3` here. -/
example : advantage ((uniformOfFintype (Fin 3 → Fin 3)).map fun f => collide.run f)
    ((uniformOfFintype (Equiv.Perm (Fin 3))).map fun π : Equiv.Perm (Fin 3) => collide.run ⇑π) ≤
      1 / 3 := by
  have := switching_lemma_le collide collide_bounded
  norm_num at this
  linarith

/-- Query `0` and output whether the answer is `0`. -/
def guess : OracleComp (Fin 3) (Fin 3) Bool := .query 0 fun y => .done (decide (y = 0))

theorem guess_rf :
    winProb ((uniformOfFintype (Fin 3 → Fin 3)).map fun f => guess.run f) = 1 / 3 := by
  rw [winProb_map_uniform]
  have h : (univ.filter fun f : Fin 3 → Fin 3 => guess.run f = true).card = 9 := by decide
  rw [h]
  norm_num

/-- A one-query distinguisher has advantage `0` (`collisionProb _ 1 = 0`), so the
random-permutation probability is the random-function probability `1/3`. -/
example : winProb ((uniformOfFintype (Equiv.Perm (Fin 3))).map
    fun π : Equiv.Perm (Fin 3) => guess.run ⇑π) = 1 / 3 := by
  have h := switching_lemma guess (q := 1) fun _ => trivial
  rw [Birthday.collisionProb_eq, Nat.descFactorial_one, pow_one,
    div_self (by norm_num), sub_self, advantage, guess_rf] at h
  have h0 := abs_nonneg (1 / 3 - winProb ((uniformOfFintype (Equiv.Perm (Fin 3))).map
    fun π : Equiv.Perm (Fin 3) => guess.run ⇑π))
  have := abs_eq_zero.1 (le_antisymm h h0)
  linarith

/-- Distinct queries get distinct answers from the lazy random permutation (`collide`'s run). -/
example : ∀ p ∈ (lazyRP collide Table.empty).support, ∀ x x' y,
    p.2 x = some y → p.2 x' = some y → x = x' :=
  injective_of_mem_support_lazyRP collide

/-- Recorded answers survive a lazy run: after `collide` from `{0 ↦ 2}`, `0` still maps to `2`. -/
example : ∀ p ∈ (lazyRF collide T₀).support, p.2 0 = some 2 := fun p hp =>
  extends_of_mem_support_runState _ collide T₀ p hp 0 2 (by decide)

/-- The switching bound from the empty table on `Fin 3` after two queries is `1/3`, and from
`{0 ↦ 2}` (two unused values) after one query it is `1/3` as well. -/
example : switchBound 3 3 2 = 1 / 3 := by norm_num [switchBound, Nat.descFactorial]

example : switchBound 3 2 1 = 1 / 3 := by norm_num [switchBound, Nat.descFactorial]

/-- The lazy switching lemma from the nonempty table `{0 ↦ 2}`: a one-query distinguisher has
advantage at most `1/3` there (a fresh query hits the used value `2` with probability `1/3`). -/
example : |winProb ((lazyRF guess T₀).map Prod.fst) - winProb ((lazyRP guess T₀).map Prod.fst)| ≤
    1 / 3 := by
  have h := lazy_switching guess 1 T₀ fun _ => trivial
  have hc : #(freshSet T₀) = 2 := by rw [freshSet_T₀]; decide
  rw [hc, Fintype.card_fin] at h
  refine h.trans (le_of_eq ?_)
  norm_num [switchBound, Nat.descFactorial]

/-- A stateless oracle run through `runState` is `evalPMF`: `guess` against fresh uniform answers
outputs `1` with probability `1/3`. -/
example : winProb ((runState (fun (s : Unit) _ => (uniformOfFintype (Fin 3)).map fun y => (y, s))
    guess ()).map Prod.fst) = 1 / 3 := by
  rw [runState_stateless_map_fst, guess, FreeM.evalPMF_liftBind]
  rw [show uniformOfFintype (Fin 3) = uniformOfFinset univ univ_nonempty from rfl,
    winProb_bind_uniformOfFinset]
  simp [FreeM.evalPMF_pure']

end Cslib.Crypto.FrameworkTests.LazySampling
