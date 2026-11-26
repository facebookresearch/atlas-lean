/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Combinatorics.Perm.CyclicHeadFixing
public import MathlibExt.Combinatorics.Perm.ShuffleDescents
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Closing-edge partitions of cyclic rotations

For a permutation of `N=n+1` letters, the cyclic descent count is the ordinary count plus the
closing comparison `σ(0)<σ(n)`. A position rotation with a closing descent has ordinary count
`c(σ)-1`; one without it has ordinary count `c(σ)`.

Exactly `c(σ)` rotation positions have a closing descent. Thus a finite sum over rotations
splits into these two closing-edge parts, of sizes `c(σ)` and `N-c(σ)`. For one letter, the
first part is empty and the ordinary count is zero.

Fixing a zero head preserves the ordinary tail count; when the tail is nonempty, it adds one
closing cyclic descent.

Reference: Stanley, *Enumerative Combinatorics*, Volume 1, Chapter 1.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace Equiv.Perm

/-- Let `n : ℕ`, `N=n+1`, `ρ=finRotate N`, and `σ ∈ S_N = Equiv.Perm (Fin N)`. Write
`c(σ)=cyclicDescentNumber σ`, counting positions `i : Fin N` with `σ(ρ i)<σ i`. Products
compose as `(u*v)(i)=u(v(i))`. The ordinary count is `descentNumber σ = ∑ i : Fin n, if
σ(i.succ)<σ(i.castSucc) then 1 else 0`, omitting the closing edge. -/
theorem descentNumber_eq_adjacent_sum {n : ℕ} (σ : Perm (Fin (n + 1))) :
    descentNumber σ = ∑ i : Fin n, if σ i.succ < σ i.castSucc then 1 else 0 := by
  classical
  let P := fun j : Fin (n + 1) => ∃ h : j.val + 1 < n + 1,
    σ j > σ ⟨j.val + 1, h⟩
  have hpositions : descentPositions σ = Finset.univ.filter P := by
    apply Finset.ext
    intro j
    simp only [descentPositions, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hj, hd⟩
      exact ⟨hj, hd⟩
    · rintro ⟨hj, hd⟩
      exact ⟨hj, hd⟩
  have h : descentNumber σ = ∑ j : Fin (n + 1), if P j then 1 else 0 := by
    calc
      _ = (Finset.univ.filter P).card := congrArg Finset.card hpositions
      _ = ∑ j ∈ Finset.univ.filter P, (1 : ℕ) := by simp
      _ = _ := by rw [Finset.sum_filter]
  rw [h, Fin.sum_univ_castSucc]
  have hp (i : Fin n) : P i.castSucc ↔ σ i.succ < σ i.castSucc := by
    constructor
    · rintro ⟨h, hd⟩
      exact hd
    · intro hd
      exact ⟨Nat.succ_lt_succ i.isLt, hd⟩
  have hlast : ¬ P (Fin.last n) := by
    rintro ⟨h, hd⟩
    simp only [Fin.val_last] at h
    omega
  simp only [hp, hlast, if_false, add_zero]

/-- Let `n : ℕ`, `N=n+1`, `ρ=finRotate N`, and `σ ∈ S_N = Equiv.Perm (Fin N)`. Write
`c(σ)=cyclicDescentNumber σ`, counting positions `i : Fin N` with `σ(ρ i)<σ i`. Products
compose as `(u*v)(i)=u(v(i))`. `c(σ)=descentNumber σ + (if σ 0<σ(Fin.last n) then 1 else 0)`. -/
theorem cyclicDescentNumber_eq_ordinary_closing {n : ℕ} (σ : Perm (Fin (n + 1))) :
    cyclicDescentNumber σ = descentNumber σ + if σ 0 < σ (Fin.last n) then 1 else 0 := by
  rw [cyclicDescentNumber, Fin.sum_univ_castSucc, descentNumber_eq_adjacent_sum]
  rw [finRotate_last]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hrotate : finRotate (n + 1) i.castSucc = i.succ := by
    change finRotate (n + 1) ⟨i.val, _⟩ = ⟨i.val + 1, _⟩
    exact finRotate_of_lt i.isLt
  rw [hrotate]

/-- For `n : ℕ` and `π ∈ S_n`, the embedding `H_n(π)=headFixingHom n π` fixes zero and sends `j+1`
to `π(j)+1`. It satisfies `descentNumber(H_n π)=descentNumber π`. -/
theorem descentNumber_headFixing (n : ℕ) (π : Perm (Fin n)) :
    descentNumber (headFixingHom n π) = descentNumber π := by
  cases n with
  | zero =>
    have hπ : π = 1 := Subsingleton.elim _ _
    subst π
    rw [map_one]
    exact ((descentNumber_eq_zero_iff (1 : Perm (Fin 1))).mpr rfl).trans
      ((descentNumber_eq_zero_iff (1 : Perm (Fin 0))).mpr rfl).symm
  | succ n =>
    rw [descentNumber_eq_adjacent_sum, descentNumber_eq_adjacent_sum]
    let a : Fin (n + 1) → ℕ := fun i =>
      if headFixingPermutation (n + 1) π i.succ <
        headFixingPermutation (n + 1) π i.castSucc then 1 else 0
    change (∑ i : Fin (n + 1), a i) =
      ∑ i : Fin n, if π i.succ < π i.castSucc then 1 else 0
    have hzero : a 0 = 0 := by
      change (if headFixingPermutation (n + 1) π (0 : Fin (n + 1)).succ <
          headFixingPermutation (n + 1) π 0 then 1 else 0) = 0
      rw [headFixingPermutation_succ, headFixingPermutation_zero]
      simp only [Fin.lt_def, Fin.val_succ, Fin.val_zero, Nat.not_lt_zero, if_false]
    have hsucc (i : Fin n) : a i.succ = if π i.succ < π i.castSucc then 1 else 0 := by
      change (if headFixingPermutation (n + 1) π i.succ.succ <
          headFixingPermutation (n + 1) π i.succ.castSucc then 1 else 0) = _
      have hi : i.succ.castSucc = i.castSucc.succ := by apply Fin.ext; rfl
      rw [hi, headFixingPermutation_succ, headFixingPermutation_succ]
      simp only [Fin.lt_def, Fin.val_succ, Nat.add_lt_add_iff_right]
    rw [Fin.sum_univ_succ, hzero, zero_add]
    exact Finset.sum_congr rfl (fun i _ => hsucc i)

/-- For `n : ℕ` with `0<n` and `π ∈ S_n`, `cyclicDescentNumber(headFixingHom n π)=descentNumber
π+1`. The fixed head is zero and the nonempty tail contributes the closing descent. -/
theorem cyclicDescentNumber_headFixing (n : ℕ) (π : Perm (Fin n)) (hn : 0 < n) :
    cyclicDescentNumber (headFixingHom n π) = descentNumber π + 1 := by
  cases n with
  | zero => omega
  | succ n =>
    rw [cyclicDescentNumber_eq_ordinary_closing, descentNumber_headFixing]
    change descentNumber π +
      (if headFixingPermutation (n + 1) π 0 <
        headFixingPermutation (n + 1) π (Fin.last n).succ then 1 else 0) = _
    simp only [headFixingPermutation_zero, headFixingPermutation_succ,
      Fin.lt_def, Fin.val_zero, Fin.val_succ, Nat.zero_lt_succ, if_true]

/-- Let `n : ℕ`, `N=n+1`, `ρ=finRotate N`, and `σ ∈ S_N = Equiv.Perm (Fin N)`. Write
`c(σ)=cyclicDescentNumber σ`, counting positions `i : Fin N` with `σ(ρ i)<σ i`. Products
compose as `(u*v)(i)=u(v(i))`. For `r : Fin N`, `closingDescent σ r` is the predicate
`(σ*ρ^r.val) 0 < (σ*ρ^r.val)(Fin.last n)`. -/
def closingDescent {n : ℕ} (σ : Perm (Fin (n + 1))) (r : Fin (n + 1)) : Prop :=
  (σ * finRotate (n + 1) ^ r.val) 0 < (σ * finRotate (n + 1) ^ r.val) (Fin.last n)

private theorem closingDescent_at_cut {n : ℕ}
    (σ : Perm (Fin (n + 1))) (r : Fin (n + 1)) :
    closingDescent σ r ↔
      σ (finRotate (n + 1) (closingCutEquiv n r)) < σ (closingCutEquiv n r) := by
  have h : (finRotate (n + 1) ^ r.val) 0 =
      finRotate (n + 1) ((finRotate (n + 1) ^ r.val) (Fin.last n)) := by
    calc
      _ = (finRotate (n + 1) ^ r.val) (finRotate (n + 1) (Fin.last n)) := by rw [finRotate_last]
      _ = _ := by
        have hp : finRotate (n + 1) ^ r.val * finRotate (n + 1) =
            finRotate (n + 1) * finRotate (n + 1) ^ r.val := by rw [← pow_succ, ← pow_succ']
        exact congrArg (fun p : Perm (Fin (n + 1)) => p (Fin.last n)) hp
  simp only [closingDescent, Equiv.Perm.mul_apply, closingCutEquiv_apply, h]

open scoped Classical in
/-- Let `n : ℕ`, `N=n+1`, `ρ=finRotate N`, and `σ ∈ S_N = Equiv.Perm (Fin N)`. Write
`c(σ)=cyclicDescentNumber σ`, counting positions `i : Fin N` with `σ(ρ i)<σ i`. Products
compose as `(u*v)(i)=u(v(i))`. `∑ r : Fin N, if closingDescent σ r then 1 else 0 = c(σ)`.
Every cyclic edge occurs once as the closing edge of a rotation. -/
theorem closingDescent_sum {n : ℕ} (σ : Perm (Fin (n + 1))) :
    (∑ r : Fin (n + 1), if closingDescent σ r then 1 else 0) = cyclicDescentNumber σ := by
  classical
  simp_rw [closingDescent_at_cut]
  exact Fintype.sum_equiv (closingCutEquiv n)
    (fun r : Fin (n + 1) => if σ (finRotate (n + 1) (closingCutEquiv n r)) < σ (closingCutEquiv n r) then 1 else 0)
    (fun i : Fin (n + 1) => if σ (finRotate (n + 1) i) < σ i then 1 else 0)
    (fun _ => rfl)

open scoped Classical in
/-- Let `n : ℕ`, `N=n+1`, `ρ=finRotate N`, and `σ ∈ S_N = Equiv.Perm (Fin N)`. Write
`c(σ)=cyclicDescentNumber σ`, counting positions `i : Fin N` with `σ(ρ i)<σ i`. Products
compose as `(u*v)(i)=u(v(i))`. For `r : Fin N`, `descentNumber(σ*ρ^r.val) = if closingDescent
σ r then c(σ)-1 else c(σ)`, with subtraction in `ℕ`. -/
theorem descentNumber_rotation {n : ℕ} (σ : Perm (Fin (n + 1))) (r : Fin (n + 1)) :
    descentNumber (σ * finRotate (n + 1) ^ r.val) =
      if closingDescent σ r then cyclicDescentNumber σ - 1 else cyclicDescentNumber σ := by
  classical
  have h := cyclicDescentNumber_eq_ordinary_closing (σ * finRotate (n + 1) ^ r.val)
  rw [cyclicDescentNumber_rotate_positions_pow] at h
  by_cases hc : closingDescent σ r
  · have hc' : (σ * finRotate (n + 1) ^ r.val) 0 <
        (σ * finRotate (n + 1) ^ r.val) (Fin.last n) := hc
    rw [if_pos hc]
    rw [if_pos hc'] at h
    omega
  · have hc' : ¬ (σ * finRotate (n + 1) ^ r.val) 0 <
        (σ * finRotate (n + 1) ^ r.val) (Fin.last n) := hc
    rw [if_neg hc]
    rw [if_neg hc'] at h
    omega

/-- Let `n : ℕ`, `N=n+1`, `ρ=finRotate N`, and `σ ∈ S_N = Equiv.Perm (Fin N)`. Write
`c(σ)=cyclicDescentNumber σ`, counting positions `i : Fin N` with `σ(ρ i)<σ i`. Products
compose as `(u*v)(i)=u(v(i))`. For a commutative additive monoid `T` and `f : ℕ → T`, `∑ r :
Fin N, f(descentNumber(σ*ρ^r.val)) = c(σ) • f(c(σ)-1) + (N-c(σ)) • f(c(σ))`. The scalar action
is repeated addition, and the two weights count the closing-descent and non-descent parts. -/
theorem sum_descentNumber_rotations {T : Type*} [AddCommMonoid T]
    {n : ℕ} (σ : Perm (Fin (n + 1))) (f : ℕ → T) :
    (∑ r : Fin (n + 1), f (descentNumber (σ * finRotate (n + 1) ^ r.val))) =
      cyclicDescentNumber σ • f (cyclicDescentNumber σ - 1) +
        (n + 1 - cyclicDescentNumber σ) • f (cyclicDescentNumber σ) := by
  classical
  let S := Finset.univ.filter (closingDescent σ)
  have hcard : S.card = cyclicDescentNumber σ := by
    calc
      _ = ∑ r ∈ S, (1 : ℕ) := by simp
      _ = ∑ r : Fin (n + 1), if closingDescent σ r then 1 else 0 := by dsimp only [S]; rw [Finset.sum_filter]
      _ = _ := closingDescent_sum σ
  have hneg : Finset.univ.filter (fun r : Fin (n + 1) => ¬ closingDescent σ r) = Finset.univ \ S := by
    ext r
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, not_and, not_true]
  have hnegcard : (Finset.univ.filter (fun r : Fin (n + 1) => ¬ closingDescent σ r)).card =
      n + 1 - cyclicDescentNumber σ := by
    rw [hneg, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_univ,
      Fintype.card_fin, hcard]
  simp_rw [descentNumber_rotation]
  simp only [apply_ite]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, hcard, hnegcard]

end Equiv.Perm
