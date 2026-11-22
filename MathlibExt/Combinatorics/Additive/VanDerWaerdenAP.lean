/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.Basic

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.HalesJewett

/-!
# Van der Waerden's theorem on a one-based finite interval

This file derives the finite interval form of van der Waerden's theorem from the Hales-Jewett
theorem.
-/

namespace MetaMathlibExt

@[expose] public section

open scoped BigOperators Finset

private theorem vdw_sum_le {ι : Type*} [Fintype ι] (k : Nat) (x : ι → Fin k) :
    ∑ i, (x i).val ≤ (k - 1) * Fintype.card ι := by
  calc
    ∑ i, (x i).val ≤ ∑ _i : ι, (k - 1) := by
      simpa using Finset.sum_le_sum (s := Finset.univ)
        (fun i _hi ↦ Nat.le_sub_one_of_lt (x i).isLt)
    _ = (k - 1) * Fintype.card ι := by
      simp [Nat.mul_comm]

private theorem vdw_line_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {k : Nat}
    (l : Combinatorics.Line (Fin k) ι) (s : Finset ι)
    (hs : s = Finset.univ.filter fun i ↦ l.idxFun i = none) (x : Fin k) :
    1 + ∑ i, (l x i).val =
      (1 + ∑ i ∈ sᶜ, ((l.idxFun i).map (fun y ↦ y.val)).getD 0) + x.val * s.card := by
  classical
  rw [← Finset.sum_add_sum_compl s]
  have hactive : ∑ i ∈ s, (l x i).val = s.card * x.val := by
    apply Finset.sum_const_nat
    intro i hi
    rw [hs, Finset.mem_filter] at hi
    rw [l.apply_none x i hi.2]
  have hfixed : ∑ i ∈ sᶜ, (l x i).val =
      ∑ i ∈ sᶜ, ((l.idxFun i).map (fun y ↦ y.val)).getD 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hs, Finset.compl_filter, Finset.mem_filter] at hi
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists.mp hi.2
    simp [← hy, Option.map_some, Option.getD]
  rw [hactive, hfixed, Nat.mul_comm s.card x.val]
  omega

private theorem vdw_active_card_pos {ι : Type*} [Fintype ι] {k : Nat}
    (l : Combinatorics.Line (Fin k) ι) (s : Finset ι)
    (hs : s = Finset.univ.filter fun i ↦ l.idxFun i = none) : 0 < s.card := by
  rw [Finset.card_pos]
  obtain ⟨i, hi⟩ := l.proper
  refine ⟨i, ?_⟩
  rw [hs, Finset.mem_filter]
  exact ⟨Finset.mem_univ i, hi⟩

private theorem vdw_line_endpoint_le {ι : Type*} [Fintype ι] [DecidableEq ι] {k : Nat}
    (hk : 0 < k) (l : Combinatorics.Line (Fin k) ι) (s : Finset ι)
    (hs : s = Finset.univ.filter fun i ↦ l.idxFun i = none) :
    (1 + ∑ i ∈ sᶜ, ((l.idxFun i).map (fun y ↦ y.val)).getD 0) +
        (k - 1) * s.card ≤ (k - 1) * Fintype.card ι + 1 := by
  let x : Fin k := ⟨k - 1, by omega⟩
  have hline := vdw_line_sum l s hs x
  have hbound := vdw_sum_le k (l x)
  dsimp [x] at hline
  calc
    _ = 1 + ∑ i, (l x i).val := hline.symm
    _ ≤ 1 + (k - 1) * Fintype.card ι := Nat.add_le_add_left hbound 1
    _ = (k - 1) * Fintype.card ι + 1 := Nat.add_comm _ _

private theorem vdw_encode_mem {ι : Type*} [Fintype ι] (k : Nat) (x : ι → Fin k) :
    1 ≤ 1 + ∑ i, (x i).val ∧
      1 + ∑ i, (x i).val ≤ (k - 1) * Fintype.card ι + 1 := by
  constructor
  · omega
  · have hbound := vdw_sum_le k x
    omega

/-- **Van der Waerden's theorem.** For all positive integers $r$ and $k$ there is a natural
number $N$ such that for every coloring of $\{1, \dots, N\}$ with $r$ colors there are natural
numbers $a \ge 1$ and $d \ge 1$ with $a + (k - 1)d \le N$ such that each of the $k$ terms
$a, a + d, \dots, a + (k - 1)d$ has the same color as $a$.

Proves `Wanted` entry `vanDerWaerden`.

Proof: apply the Hales–Jewett theorem to the digit-sum encoding $x \mapsto 1 + \sum_i x_i$
of words over the alphabet $\{0, \dots, k - 1\}$, so that a combinatorial line becomes an
arithmetic progression. This follows the standard derivation in Graham, Rothschild, and
Spencer, *Ramsey Theory*, Section 2.3, from van der Waerden (1927).

Source: https://en.wikipedia.org/wiki/Van_der_Waerden%27s_theorem
-/
theorem vanDerWaerden : ∀ (r k : Nat), 0 < r → 0 < k →
    ∃ N : Nat, ∀ c : {m : Nat // 1 ≤ m ∧ m ≤ N} → Fin r, ∃ a d : Nat,
      1 ≤ a ∧ 1 ≤ d ∧ a + (k - 1) * d ≤ N ∧
        ∀ i : Nat, i < k → ∀ (h₁ : 1 ≤ a + i * d) (h₂ : a + i * d ≤ N)
          (h₀ : 1 ≤ a ∧ a ≤ N), c ⟨a + i * d, h₁, h₂⟩ = c ⟨a, h₀⟩ := by
  intro r k _hr hk
  classical
  obtain ⟨ι, _inst, hι⟩ :=
    Combinatorics.Line.exists_mono_in_high_dimension (Fin k) (Fin r)
  let N := (k - 1) * Fintype.card ι + 1
  refine ⟨N, ?_⟩
  intro c
  let C : (ι → Fin k) → Fin r := fun x ↦
    c ⟨1 + ∑ i, (x i).val, by simpa [N] using vdw_encode_mem k x⟩
  obtain ⟨l, lineColor, hcolor⟩ := hι C
  let s : Finset ι := Finset.univ.filter fun i ↦ l.idxFun i = none
  have hs : s = Finset.univ.filter fun i ↦ l.idxFun i = none := rfl
  let a := 1 + ∑ i ∈ sᶜ, ((l.idxFun i).map (fun y ↦ y.val)).getD 0
  let d := s.card
  refine ⟨a, d, ?_, ?_, ?_, ?_⟩
  · dsimp [a]
    omega
  · simpa [d] using vdw_active_card_pos l s hs
  · simpa [a, d, N] using vdw_line_endpoint_le hk l s hs
  · intro i hi h₁ h₂ h₀
    let x : Fin k := ⟨i, hi⟩
    let z : Fin k := ⟨0, hk⟩
    have hsame : C (l x) = C (l z) := (hcolor x).trans (hcolor z).symm
    have hx : 1 + ∑ j, (l x j).val = a + i * d := by
      simpa [a, d, x] using vdw_line_sum l s hs x
    have hz : 1 + ∑ j, (l z j).val = a := by
      simpa [a, d, z] using vdw_line_sum l s hs z
    simpa only [C, hx, hz] using hsame

end

end MetaMathlibExt
