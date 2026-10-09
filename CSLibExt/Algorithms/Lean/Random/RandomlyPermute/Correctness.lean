/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Random.RandomlyPermute.Basic
import all CSLibExt.Algorithms.Lean.Random.RandomlyPermute.Basic
import Mathlib.Data.List.FinRange

/-!
# Preservation properties of Fisher–Yates swaps

The proofs follow the actual saved-vector worker. Earlier completed positions
remain fixed, and mapping values commutes with every saved swap.

Retained Lean was authored by Codex at Adam Kiezun's explicit selection.
-/

namespace Cslib.Algorithms.Lean.TimeM

universe u v

private theorem scan_frame {α : Type u} {n : Nat}
    (draws : (i : Fin n) → Fin (n - i.val)) (i : Nat) (xs : Vector α n)
    (p : Fin n) (hp : p.val < i) :
    (scan draws i xs).ret[p.val] = xs[p.val] := by
  rw [scan]
  split_ifs with hi
  · simp only [TimeM.ret_bind]
    rw [scan_frame draws (i + 1) _ p (by omega)]
    exact Vector.getElem_swap_of_ne (by omega) (by omega)
  · rfl
termination_by n - i
decreasing_by omega

private theorem map_swap {α : Type u} {β : Type v} {n : Nat}
    (f : α → β) (xs : Vector α n) (i j : Nat) (hi : i < n) (hj : j < n) :
    (xs.swap i j hi hj).map f = (xs.map f).swap i j hi hj := by
  ext k
  simp only [Vector.getElem_map, Vector.getElem_swap]
  split_ifs <;> rfl

private theorem scan_map {α : Type u} {β : Type v} {n : Nat}
    (f : α → β) (draws : (i : Fin n) → Fin (n - i.val)) (i : Nat) (xs : Vector α n) :
    (scan draws i (xs.map f)).ret = (scan draws i xs).ret.map f := by
  rw [scan, scan]
  split_ifs with hi
  · simp only [TimeM.ret_bind]
    rw [← map_swap]
    exact scan_map f draws (i + 1) _
  · rfl
termination_by n - i
decreasing_by omega

private theorem swap_reindex {α : Type u} {n : Nat} (xs : Vector α n)
    (i j : Nat) (hi : i < n) (hj : j < n) :
    xs.swap i j hi hj =
      Vector.ofFn (fun p => xs[(Equiv.swap ⟨i, hi⟩ ⟨j, hj⟩ p).val]) := by
  ext k
  simp only [Vector.getElem_swap, Vector.getElem_ofFn, Equiv.swap_apply_def, Fin.ext_iff]
  split_ifs <;> rfl

private theorem swap_perm {α : Type u} {n : Nat} (xs : Vector α n)
    (i j : Nat) (hi : i < n) (hj : j < n) :
    (xs.swap i j hi hj).toList.Perm xs.toList := by
  rw [swap_reindex, Vector.toList_ofFn]
  have hxs : List.ofFn (fun p : Fin n => xs[p.val]) = xs.toList := by
    apply List.ext_getElem
    · simp
    · intro k hk₁ hk₂
      simp
  rw [← hxs]
  exact (Equiv.swap ⟨i, hi⟩ ⟨j, hj⟩).ofFn_comp_perm (fun p => xs[p.val])

private theorem scan_perm {α : Type u} {n : Nat}
    (draws : (i : Fin n) → Fin (n - i.val)) (i : Nat) (xs : Vector α n) :
    (scan draws i xs).ret.toList.Perm xs.toList := by
  rw [scan]
  split_ifs with hi
  · simp only [TimeM.ret_bind]
    exact (scan_perm draws (i + 1) _).trans (swap_perm xs _ _ _ _)
  · exact List.Perm.refl _
termination_by n - i
decreasing_by omega

/-- Every occurrence is preserved by the saved Fisher–Yates swaps, even when
input values repeat. -/
public theorem randomlyPermute_perm {α : Type u} {n : Nat} (xs : Vector α n)
    (draws : (i : Fin n) → Fin (n - i.val)) :
    (randomlyPermute xs draws).ret.toList.Perm xs.toList :=
  scan_perm draws 0 xs

private theorem scan_reindex {α : Type u} {n : Nat}
    (draws : (i : Fin n) → Fin (n - i.val)) (i : Nat) (xs : Vector α n) :
    ∃ σ : Equiv.Perm (Fin n),
      (scan draws i xs).ret = Vector.ofFn (fun p => xs[(σ p).val]) := by
  rw [scan]
  split_ifs with hi
  · simp only [TimeM.ret_bind]
    obtain ⟨σ, hσ⟩ := scan_reindex draws (i + 1)
      (xs.swap i (i + (draws ⟨i, hi⟩).val) hi (by
        have hd : (draws ⟨i, hi⟩).val < n - i := (draws ⟨i, hi⟩).isLt
        omega))
    refine ⟨σ.trans (Equiv.swap ⟨i, hi⟩
      ⟨i + (draws ⟨i, hi⟩).val, by
        have hd : (draws ⟨i, hi⟩).val < n - i := (draws ⟨i, hi⟩).isLt
        omega⟩), ?_⟩
    rw [hσ, swap_reindex]
    simp only [Vector.getElem_ofFn, Equiv.trans_apply]
  · refine ⟨Equiv.refl _, ?_⟩
    ext p
    simp
termination_by n - i
decreasing_by omega

private theorem scan_ret_congr {α : Type u} {n : Nat}
    (draws₁ draws₂ : (i : Fin n) → Fin (n - i.val)) (i : Nat) (xs : Vector α n)
    (h : ∀ p : Fin n, i ≤ p.val → draws₁ p = draws₂ p) :
    (scan draws₁ i xs).ret = (scan draws₂ i xs).ret := by
  rw [scan, scan]
  split_ifs with hi
  · have hd := h ⟨i, hi⟩ (by rfl)
    simp only [TimeM.ret_bind, hd]
    exact scan_ret_congr draws₁ draws₂ (i + 1) _ (fun p hp => h p (by omega))
  · rfl
termination_by n - i
decreasing_by omega

private theorem scan_head {α : Type u} {n : Nat}
    (draws : (i : Fin n) → Fin (n - i.val)) (i : Nat) (xs : Vector α n) (hi : i < n) :
    (scan draws i xs).ret[i] = xs[i + (draws ⟨i, hi⟩).val]'(by
      have hd : (draws ⟨i, hi⟩).val < n - i := (draws ⟨i, hi⟩).isLt
      omega) := by
  rw [scan]
  simp only [hi, ↓reduceDIte, TimeM.ret_bind]
  rw [scan_frame draws (i + 1) _ ⟨i, hi⟩ (Nat.lt_succ_self i)]
  exact Vector.getElem_swap_left _ _

private theorem scan_draws_injective {α : Type u} {n : Nat}
    (draws₁ draws₂ : (i : Fin n) → Fin (n - i.val)) (i : Nat) (xs : Vector α n)
    (hxs : Function.Injective fun p : Fin n => xs[p.val])
    (hfinal : (scan draws₁ i xs).ret = (scan draws₂ i xs).ret) :
    ∀ p : Fin n, i ≤ p.val → draws₁ p = draws₂ p := by
  by_cases hi : i < n
  · let j₁ : Fin n := ⟨i + (draws₁ ⟨i, hi⟩).val, by
      have hd : (draws₁ ⟨i, hi⟩).val < n - i := (draws₁ ⟨i, hi⟩).isLt
      omega⟩
    let j₂ : Fin n := ⟨i + (draws₂ ⟨i, hi⟩).val, by
      have hd : (draws₂ ⟨i, hi⟩).val < n - i := (draws₂ ⟨i, hi⟩).isLt
      omega⟩
    have hv : xs[j₁.val] = xs[j₂.val] := by
      have h := congrArg (fun ys : Vector α n => ys[i]'hi) hfinal
      simpa only [scan_head draws₁ i xs hi, scan_head draws₂ i xs hi] using h
    have hj := congrArg Fin.val (hxs hv)
    have hd : draws₁ ⟨i, hi⟩ = draws₂ ⟨i, hi⟩ := by
      apply Fin.ext
      dsimp [j₁, j₂] at hj
      omega
    let saved := xs.swap i j₂.val hi j₂.isLt
    have hsaved : Function.Injective fun p : Fin n => saved[p.val] := by
      intro a b hab
      apply (Equiv.swap ⟨i, hi⟩ j₂).injective
      apply hxs
      simpa only [saved, swap_reindex, Vector.getElem_ofFn] using hab
    have hnext : (scan draws₁ (i + 1) saved).ret = (scan draws₂ (i + 1) saved).ret := by
      rw [scan, scan] at hfinal
      simpa only [hi, ↓reduceDIte, TimeM.ret_bind, hd] using hfinal
    intro p hp
    by_cases hpi : p.val = i
    · have hp' : p = ⟨i, hi⟩ := Fin.ext hpi
      subst p
      exact hd
    · exact scan_draws_injective draws₁ draws₂ (i + 1) saved hsaved hnext p (by omega)
  · intro p hp
    have := p.isLt
    omega
termination_by n - i
decreasing_by omega

noncomputable section

@[no_expose] private def positionPerm {n : Nat}
    (draws : (i : Fin n) → Fin (n - i.val)) : Equiv.Perm (Fin n) :=
  Classical.choose (scan_reindex draws 0 (Vector.ofFn fun p : Fin n => p))

private theorem positionPerm_eq {n : Nat} (draws : (i : Fin n) → Fin (n - i.val)) :
    (randomlyPermute (Vector.ofFn fun p : Fin n => p) draws).ret =
      Vector.ofFn (positionPerm draws) := by
  simpa only [randomlyPermute, positionPerm, Vector.getElem_ofFn] using
    Classical.choose_spec (scan_reindex draws 0 (Vector.ofFn fun p : Fin n => p))

private theorem positionPerm_injective (n : Nat) :
    Function.Injective (positionPerm (n := n)) := by
  intro draws₁ draws₂ h
  have hfinal :
      (scan draws₁ 0 (Vector.ofFn fun p : Fin n => p)).ret =
        (scan draws₂ 0 (Vector.ofFn fun p : Fin n => p)).ret := by
    change (randomlyPermute _ draws₁).ret = (randomlyPermute _ draws₂).ret
    rw [positionPerm_eq, positionPerm_eq, h]
  apply funext
  intro p
  exact scan_draws_injective draws₁ draws₂ 0 (Vector.ofFn fun p : Fin n => p)
    (by intro a b hab; simpa only [Vector.getElem_ofFn] using hab) hfinal p (by omega)

end

/-- Empty Fisher–Yates execution retrieves no choices and performs no swaps. -/
public theorem randomlyPermute_empty {α : Type u} (xs : Vector α 0)
    (draws : (i : Fin 0) → Fin (0 - i.val)) :
    randomlyPermute xs draws = ⟨xs, (0, 0)⟩ := by
  rw [randomlyPermute, scan]
  rfl

/-- Singleton execution retains its element but still retrieves the final
unique draw and executes its self-swap. -/
public theorem randomlyPermute_singleton {α : Type u} (xs : Vector α 1)
    (draws : (i : Fin 1) → Fin (1 - i.val)) :
    randomlyPermute xs draws = ⟨xs, (1, 1)⟩ := by
  apply TimeM.ext
  · rw [randomlyPermute, scan]
    simp only [show (0 : Nat) < 1 by decide, ↓reduceDIte, TimeM.ret_bind]
    rw [scan]
    simp only [show ¬(1 : Nat) < 1 by decide, ↓reduceDIte, TimeM.ret_pure]
    ext p hp
    have hp0 : p = 0 := by omega
    subst p
    simp
  · exact randomlyPermute_time xs draws

end Cslib.Algorithms.Lean.TimeM
