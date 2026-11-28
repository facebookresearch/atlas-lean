/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleIndex
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Finset.Card

/-!
# Adjacent descents and the shuffle cut

For `σ ∈ S_n`, an ordinary descent position is `j` with `j+1<n` and `σ(j)>σ(j+1)`. Its descent
number is the cardinality of this set.

A permutation of `Fin(p+q)` is a `(p,q)`-shuffle precisely when every descent is at the cut
between the blocks, meaning `j+1=p`. Thus a two-block shuffle has at most one descent. Zero
descents characterize the identity permutation, and a positive length `n` gives fewer than `n`
descents.

Reference: Stanley, *Enumerative Combinatorics*, Volume 1, Chapter 1.
-/

@[expose] public section
noncomputable section

namespace Equiv.Perm

/-- Let `n : ℕ` and `σ : Equiv.Perm (Fin n)`. `descentPositions σ` is the finite set of `j : Fin
n` such that `j.val+1<n` and `σ j > σ(j+1)`. The successor bound omits the final position. -/
def descentPositions {n : ℕ} (σ : Perm (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun j => ∃ h : j.val + 1 < n, σ j > σ ⟨j.val + 1, h⟩)

/-- Let `n : ℕ` and `σ : Equiv.Perm (Fin n)`. `descentNumber σ = (descentPositions σ).card`,
counting positions `j` with `j+1<n` and `σ j > σ(j+1)`. -/
def descentNumber {n : ℕ} (σ : Perm (Fin n)) : ℕ := (descentPositions σ).card

/-- For `p,q : ℕ` and `σ ∈ S_(p+q)`, `IsShuffle σ` holds if and only if every adjacent descent `σ
j > σ(j+1)` with `j+1<p+q` satisfies `j+1=p`. This is equivalent to increasing order inside
each of the two input blocks. -/
theorem isShuffle_iff_descents_at_cut {p q : ℕ} (σ : Perm (Fin (p + q))) :
    AlgebraicTopology.EilenbergZilber.IsShuffle σ ↔
      ∀ (j : Fin (p + q)) (h : j.val + 1 < p + q),
        σ j > σ ⟨j.val + 1, h⟩ → j.val + 1 = p := by
  constructor
  · intro hs j h hd
    by_cases hl : j.val + 1 < p
    · let i₀ : Fin p := ⟨j.val, by omega⟩
      let i₁ : Fin p := ⟨j.val + 1, hl⟩
      have hh := hs.1 (show i₀ < i₁ by change j.val < j.val + 1; omega)
      change σ (Fin.castAdd q i₀) < σ (Fin.castAdd q i₁) at hh
      have h₀ : Fin.castAdd q i₀ = j := by apply Fin.ext; rfl
      have h₁ : Fin.castAdd q i₁ = (⟨j.val + 1, h⟩ : Fin (p + q)) := by apply Fin.ext; rfl
      rw [h₀, h₁] at hh
      exact False.elim (lt_asymm (a := σ j) (b := σ ⟨j.val + 1, h⟩) hh hd)
    by_cases hr : p ≤ j.val
    · let i₀ : Fin q := ⟨j.val - p, by have hj := j.isLt; omega⟩
      let i₁ : Fin q := ⟨j.val + 1 - p, by omega⟩
      have hh := hs.2 (show i₀ < i₁ by change j.val - p < j.val + 1 - p; omega)
      change σ (Fin.natAdd p i₀) < σ (Fin.natAdd p i₁) at hh
      have h₀ : Fin.natAdd p i₀ = j := by apply Fin.ext; dsimp [i₀]; omega
      have h₁ : Fin.natAdd p i₁ = (⟨j.val + 1, h⟩ : Fin (p + q)) := by
        apply Fin.ext; dsimp [i₁]; omega
      rw [h₀, h₁] at hh
      exact False.elim (lt_asymm (a := σ j) (b := σ ⟨j.val + 1, h⟩) hh hd)
    omega
  · intro hs
    have hstep (j : Fin (p + q)) (h : j.val + 1 < p + q) (hc : j.val + 1 ≠ p) :
        σ j < σ ⟨j.val + 1, h⟩ := by
      have hnot : ¬σ j > σ ⟨j.val + 1, h⟩ := fun hd => hc (hs j h hd)
      have hne : σ j ≠ σ ⟨j.val + 1, h⟩ := by
        intro he
        have hindex := congrArg Fin.val (σ.injective he)
        change j.val = j.val + 1 at hindex
        omega
      exact lt_of_le_of_ne (le_of_not_gt hnot) hne
    constructor
    · cases p with
      | zero =>
        intro i
        exact Fin.elim0 i
      | succ p =>
        apply Fin.strictMono_iff_lt_succ.mpr
        intro i
        let j := Fin.castAdd q i.castSucc
        have hj : j.val + 1 < p + 1 + q := by dsimp [j]; have hi := i.isLt; omega
        have hc : j.val + 1 ≠ p + 1 := by dsimp [j]; have hi := i.isLt; omega
        have hh := hstep j hj hc
        have hn : (⟨j.val + 1, hj⟩ : Fin (p + 1 + q)) = Fin.castAdd q i.succ := by
          apply Fin.ext; rfl
        rw [hn] at hh
        exact hh
    · cases q with
      | zero =>
        intro i
        exact Fin.elim0 i
      | succ q =>
        apply Fin.strictMono_iff_lt_succ.mpr
        intro i
        let j := Fin.natAdd p i.castSucc
        have hj : j.val + 1 < p + (q + 1) := by dsimp [j]; have hi := i.isLt; omega
        have hc : j.val + 1 ≠ p := by dsimp [j]; omega
        have hh := hstep j hj hc
        have hn : (⟨j.val + 1, hj⟩ : Fin (p + (q + 1))) = Fin.natAdd p i.succ := by
          apply Fin.ext; dsimp [j]; omega
        rw [hn] at hh
        exact hh

/-- Let `n : ℕ` and `σ : Equiv.Perm (Fin n)`. `descentPositions σ = ∅` if and only if `σ = 1`. -/
theorem descentPositions_eq_empty_iff {n : ℕ} (σ : Perm (Fin n)) :
    descentPositions σ = ∅ ↔ σ = 1 := by
  classical
  constructor
  · intro hzero
    cases n with
    | zero => exact Subsingleton.elim _ _
    | succ n =>
      apply (Equiv.Perm.monotone_iff σ).1
      apply StrictMono.monotone
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      have hnot : ¬σ i.castSucc > σ i.succ := by
        intro hd
        have hmem : i.castSucc ∈ descentPositions σ := by
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ _, ⟨by
            change i.val + 1 < n + 1
            exact i.succ.isLt, hd⟩⟩
        rw [hzero] at hmem
        simp at hmem
      have hne : σ i.castSucc ≠ σ i.succ := by
        intro he
        have h := congrArg Fin.val (σ.injective he)
        simp only [Fin.val_castSucc, Fin.val_succ] at h
        omega
      exact lt_of_le_of_ne (le_of_not_gt hnot) hne
  · rintro rfl
    apply Finset.ext
    intro j
    constructor
    · intro hj
      obtain ⟨h, hd⟩ := (Finset.mem_filter.mp hj).2
      change j.val + 1 < j.val at hd
      omega
    · simp

/-- Let `n : ℕ` and `σ : Equiv.Perm (Fin n)`. `descentNumber σ = 0` if and only if `σ = 1`,
including `n=0`. -/
theorem descentNumber_eq_zero_iff {n : ℕ} (σ : Perm (Fin n)) : descentNumber σ = 0 ↔ σ = 1 := by
  rw [descentNumber, Finset.card_eq_zero, descentPositions_eq_empty_iff]

/-- Let `n : ℕ` and `σ : Equiv.Perm (Fin n)`. If `0<n`, then `descentNumber σ < n`, since at most
the `n-1` successor positions can be descents. -/
theorem descentNumber_lt {n : ℕ} (σ : Perm (Fin n)) (hn : 0 < n) : descentNumber σ < n := by
  classical
  cases n with
  | zero => omega
  | succ n =>
    have hlast : Fin.last n ∉ descentPositions σ := by
      intro hmem
      obtain ⟨h, _⟩ := (Finset.mem_filter.mp hmem).2
      simp only [Fin.val_last] at h
      omega
    have hss : descentPositions σ ⊂ Finset.univ := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
      intro heq
      apply hlast
      rw [heq]
      exact Finset.mem_univ _
    simpa only [descentNumber, Finset.card_univ, Fintype.card_fin] using Finset.card_lt_card hss

/-- For `p,q : ℕ` and `σ ∈ S_(p+q)` satisfying the `(p,q)`-shuffle condition, `descentNumber σ ≤
1`. Any descent must lie at the single cut `j+1=p`. -/
theorem descentNumber_le_one_of_shuffle {p q : ℕ} (σ : Perm (Fin (p + q)))
    (hs : AlgebraicTopology.EilenbergZilber.IsShuffle σ) : descentNumber σ ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  obtain ⟨hi', hdi⟩ := (Finset.mem_filter.mp hi).2
  obtain ⟨hj', hdj⟩ := (Finset.mem_filter.mp hj).2
  have hci := (isShuffle_iff_descents_at_cut σ).1 hs i hi' hdi
  have hcj := (isShuffle_iff_descents_at_cut σ).1 hs j hj' hdj
  apply Fin.ext
  omega

end Equiv.Perm
