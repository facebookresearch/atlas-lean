/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Data.UnionFind.Lemmas
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# Exact path compression for canonical Batteries union-find

The public facts describe the actual original parent chain, complete saved records
and first-root depth of canonical FIND. Private source-refinement proofs count
one root test per visit and one carried parent assignment per nonroot. These
selected events are not a logarithmic, inverse-Ackermann or physical RAM bound.

Source: CLRS, fourth edition, §19.3, printed529–530. Codex-authored conversion
of the accepted counted proof under Adam Kiezun's explicit producer override.
-/

open Cslib.Algorithms.Lean

namespace Batteries.UnionFind

namespace Internal
/-- Source refinement only: every visited root test and every carried parent write is ticked.
The canonical array and `FindAux` representation are unchanged. -/
@[no_expose] def countedAux (self : UnionFind) (x : Fin self.size) :
    TimeM (Nat × Nat) (UnionFind.FindAux self.size) := do
  TimeM.tick (1, 0)
  let y := self.arr[x.val].parent
  if h : y = x then
    pure ⟨self.arr, x, rfl⟩
  else
    have := Nat.sub_lt_sub_left (self.lt_rankMax x) (self.rank'_lt _ _ h)
    let result ← countedAux self ⟨y, self.parent'_lt _ x.isLt⟩
    TimeM.tick (0, 1)
    pure ⟨result.s.modify x fun node ↦ { node with parent := result.root },
      result.root, by simp [result.size_eq]⟩
termination_by self.rankMax - self.rank x

/-- Erasing the actual visit/write events recovers the canonical recursive result. -/
theorem countedAux_ret (self : UnionFind) (x : Fin self.size) :
    (countedAux self x).ret = self.findAux x := by
  rw [countedAux, UnionFind.findAux]
  simp only [TimeM.ret_bind]
  split
  · rfl
  · have := Nat.sub_lt_sub_left (self.lt_rankMax x) (self.rank'_lt _ _ ‹_›)
    simp only [TimeM.ret_bind, TimeM.ret_pure]
    rw [countedAux_ret self ⟨_, self.parent'_lt _ x.isLt⟩]
termination_by self.rankMax - self.rank x

/-- A root still executes one source conditional and performs no parent assignment. -/
theorem countedAux_time_root (self : UnionFind) (x : Fin self.size)
    (h : self.arr[x.val].parent = x) : (countedAux self x).time = (1, 0) := by
  rw [countedAux]
  simp [h]

/-- Nonroots execute the recursive source call, then one carried-record parent assignment. -/
theorem countedAux_time_step (self : UnionFind) (x : Fin self.size)
    (h : self.arr[x.val].parent ≠ x) :
    (countedAux self x).time = (1, 0) +
      ((countedAux self ⟨self.arr[x.val].parent, self.parent'_lt _ x.isLt⟩).time +
        (0, 1)) := by
  rw [countedAux]
  simp [h]

/-- Every actual execution has exactly one more source test than parent writes. -/
theorem countedAux_time_balance (self : UnionFind) (x : Fin self.size) :
    (countedAux self x).time.1 = (countedAux self x).time.2 + 1 := by
  if h : self.arr[x.val].parent = x then
    rw [countedAux_time_root self x h]
  else
    have := Nat.sub_lt_sub_left (self.lt_rankMax x) (self.rank'_lt _ _ h)
    rw [countedAux_time_step self x h]
    have ih := countedAux_time_balance self ⟨_, self.parent'_lt _ x.isLt⟩
    simpa [Prod.fst_add, Prod.snd_add, Nat.add_comm] using ih
termination_by self.rankMax - self.rank x

theorem result_ext {n : Nat}
    (a b : (s : UnionFind) × {_root : Fin s.size // s.size = n})
    (hs : a.1.arr = b.1.arr) (hr : a.2.val.val = b.2.val.val) : a = b := by
  obtain ⟨⟨aa, ap, ar⟩, ax, ah⟩ := a
  obtain ⟨⟨ba, bp, br⟩, bx, bh⟩ := b
  dsimp at hs hr
  subst ba
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Subtype.ext
    exact Fin.ext hr

/-- This packages the same carried array and root; it does not run canonical FIND a second time. -/
@[no_expose] def countedFind (self : UnionFind) (x : Fin self.size) :
    TimeM (Nat × Nat) ((s : UnionFind) × {_root : Fin s.size // s.size = self.size}) :=
  let result := countedAux self x
  let r := result.ret
  ⟨{ 1.arr := r.s
     2.1.val := r.root
     1.parentD_lt := fun h ↦ by
       have hret := countedAux_ret self x
       change UnionFind.parentD r.s _ < r.s.size at *
       dsimp [r] at *
       rw [hret] at *
       simp only [UnionFind.FindAux.size_eq] at *
       exact UnionFind.parentD_findAux_lt h
     1.rankD_lt := fun h ↦ by
       dsimp [r] at *
       rw [countedAux_ret self x] at *
       rw [UnionFind.rankD_findAux, UnionFind.rankD_findAux]
       exact UnionFind.lt_rankD_findAux h
     2.1.isLt := show _ < r.s.size by rw [r.size_eq]; exact r.root.isLt
     2.2 := by simp [UnionFind.size, r.size_eq] }, result.time⟩

/-- Full dependent result equality includes the saved store and returned valid representative. -/
theorem countedFind_ret (self : UnionFind) (x : Fin self.size) :
    (countedFind self x).ret = self.find x := by
  apply result_ext
  · exact congrArg UnionFind.FindAux.s (countedAux_ret self x)
  · exact congrArg (fun r ↦ r.root.val) (countedAux_ret self x)

/-- A finite per-call rank-gap bound, not a logarithmic or amortized alpha bound. -/
theorem countedAux_writes_rank (self : UnionFind) (x : Fin self.size) :
    (countedAux self x).time.2 ≤ self.rankMax - self.rank x := by
  if h : self.arr[x.val].parent = x then
    rw [countedAux_time_root self x h]
    exact Nat.zero_le _
  else
    have hd := Nat.sub_lt_sub_left (self.lt_rankMax x) (self.rank'_lt _ _ h)
    have ih := countedAux_writes_rank self ⟨_, self.parent'_lt _ x.isLt⟩
    rw [countedAux_time_step self x h]
    simp only [Prod.snd_add, Nat.zero_add] at *
    omega
termination_by self.rankMax - self.rank x

theorem ancestor_step (f : Nat → Nat) (x i : Nat) :
    (∃ k : Nat, Nat.iterate f k x = i) ↔
      i = x ∨ ∃ k : Nat, Nat.iterate f k (f x) = i := by
  constructor
  · rintro ⟨_ | k, hk⟩
    · exact Or.inl hk.symm
    · exact Or.inr ⟨k, by simpa only [Function.iterate_succ_apply] using hk⟩
  · rintro (rfl | ⟨k, hk⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨k + 1, by simpa only [Function.iterate_succ_apply] using hk⟩

open Classical in
theorem parent_aux (self : UnionFind) (x : Fin self.size) (i : Nat) :
    UnionFind.parentD (self.findAux x).s i =
      if ∃ k : Nat, Nat.iterate self.parent k x.val = i then self.rootD x.val
      else self.parent i := by
  if h : self.arr[x.val].parent = x then
    have hp : self.parent x.val = x.val := by
      simpa only [UnionFind.parent, UnionFind.parentD_eq x.isLt] using h
    have hr := (self.rootD_eq_self (x := x.val)).2 hp
    have ha : (∃ k : Nat, Nat.iterate self.parent k x.val = i) ↔ i = x.val := by
      constructor
      · rintro ⟨k, hk⟩
        exact ((Function.iterate_fixed hp k).symm.trans hk).symm
      · rintro rfl
        exact ⟨0, rfl⟩
    rw [UnionFind.findAux_s (x := x), ite_eq_left h]
    change self.parent i = _
    simp only [ha, hr]
    split
    · subst i
      exact hp
    · rfl
  else
    have hd := Nat.sub_lt_sub_left (self.lt_rankMax x) (self.rank'_lt _ _ h)
    have ih := parent_aux self ⟨self.arr[x.val].parent, self.parent'_lt _ x.isLt⟩ i
    rw [UnionFind.parentD_findAux (x := x) (i := i)]
    by_cases hi : i = x.val
    · subst i
      simp only [ite_true]
      rw [ite_eq_left ⟨0, rfl⟩]
    · rw [ite_eq_right hi, ih]
      have hy : self.arr[x.val].parent = self.parent x.val :=
        (UnionFind.parentD_eq x.isLt).symm
      rw [ancestor_step self.parent x.val i]
      simp only [hy, self.rootD_parent, hi, false_or]
termination_by self.rankMax - self.rank x
end Internal

open Classical in
/-- FIND compresses every identity in the original parent chain and no other parent. -/
public theorem find_parent_eq_ite_iterate (self : UnionFind)
    (x : Fin self.size) (i : Nat) :
    (self.find x).1.parent i =
      if ∃ k : Nat, Nat.iterate self.parent k x.val = i then self.rootD x.val
      else self.parent i := by
  exact Internal.parent_aux self x i

open Classical in
/-- FIND preserves every rank and changes exactly the original-chain parent fields. -/
public theorem getElem_find (self : UnionFind) (x : Fin self.size)
    (i : Nat) (hi : i < self.size) :
    (self.find x).1.arr[i]'(by simpa using hi) =
      { parent := if ∃ k : Nat, Nat.iterate self.parent k x.val = i then
          self.rootD x.val else self.arr[i].parent
        rank := self.arr[i].rank } := by
  have hp := find_parent_eq_ite_iterate self x i
  have hs : i < (self.find x).1.arr.size := by simpa using hi
  have hparent : (self.find x).1.arr[i].parent =
      if ∃ k : Nat, Nat.iterate self.parent k x.val = i then self.rootD x.val
      else self.arr[i].parent := by
    simpa only [UnionFind.parent, UnionFind.parentD_eq hs, UnionFind.parentD_eq hi]
      using hp
  have hrank : (self.find x).1.arr[i].rank = self.arr[i].rank := by
    change (self.findAux x).s[i].rank = self.arr[i].rank
    have hr := UnionFind.rankD_findAux (self := self) (x := x) (i := i)
    have hsaux : i < (self.findAux x).s.size := by
      simpa only [UnionFind.FindAux.size_eq] using hi
    rw [UnionFind.rankD_eq hsaux] at hr
    exact hr.trans (UnionFind.rankD_eq hi)
  cases hn : (self.find x).1.arr[i] with
  | mk p r =>
    simp only [hn] at hparent hrank
    subst p r
    rfl

namespace Internal

theorem depth_aux (self : UnionFind) (x : Fin self.size) : ∃ d : Nat,
    Nat.iterate self.parent d x.val = self.rootD x.val ∧
    (∀ k < d, Nat.iterate self.parent k x.val ≠ self.rootD x.val) ∧
    (countedAux self x).time = (d + 1, d) := by
  if h : self.arr[x.val].parent = x then
    have hp : self.parent x.val = x.val := by
      simpa only [UnionFind.parent, UnionFind.parentD_eq x.isLt] using h
    refine ⟨0, (self.rootD_eq_self (x := x.val)).2 hp |>.symm, ?_, ?_⟩
    · intro k hk
      exact (Nat.not_lt_zero k hk).elim
    · exact countedAux_time_root self x h
  else
    have hd := Nat.sub_lt_sub_left (self.lt_rankMax x) (self.rank'_lt _ _ h)
    obtain ⟨d, hdroot, hfirst, htime⟩ :=
      depth_aux self ⟨self.arr[x.val].parent, self.parent'_lt _ x.isLt⟩
    have hy : self.arr[x.val].parent = self.parent x.val :=
      (UnionFind.parentD_eq x.isLt).symm
    have hr : self.rootD self.arr[x.val].parent = self.rootD x.val := by
      rw [hy, self.rootD_parent]
    refine ⟨d + 1, ?_, ?_, ?_⟩
    · rw [Function.iterate_succ_apply, ← hy, hdroot, hr]
    · intro k hk
      cases k with
      | zero =>
        intro heq
        have hp := (self.rootD_eq_self (x := x.val)).1 heq.symm
        exact h (hy.trans hp)
      | succ k =>
        simpa only [Function.iterate_succ_apply, ← hy, ← hr] using
          hfirst k (Nat.lt_of_succ_lt_succ hk)
    · rw [countedAux_time_step self x h, htime]
      simp only [Prod.mk_add_mk, Nat.add_zero, Nat.zero_add, Nat.add_assoc,
        Nat.add_comm 1]
termination_by self.rankMax - self.rank x

theorem root_iterate (self : UnionFind) (x k : Nat) :
    self.rootD (Nat.iterate self.parent k x) = self.rootD x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', self.rootD_parent, ih]

theorem allocated_iterate (self : UnionFind) (x : Fin self.size) (k : Nat) :
    Nat.iterate self.parent k x.val < self.size := by
  induction k with
  | zero => exact x.isLt
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (self.parent_lt _).2 ih

theorem first_depth_lt_size (self : UnionFind) (x : Fin self.size) (d : Nat)
    (hfirst : ∀ k < d, Nat.iterate self.parent k x.val ≠ self.rootD x.val) :
    d < self.size := by
  have hstep : ∀ k < d, self.rank (Nat.iterate self.parent k x.val) <
      self.rank (Nat.iterate self.parent (k + 1) x.val) := by
    intro k hk
    rw [Function.iterate_succ_apply']
    apply self.rank_lt
    intro hp
    exact hfirst k hk ((self.rootD_eq_self.2 hp).symm.trans (root_iterate self x.val k))
  have hstrict : ∀ a b : Nat, a < b → b ≤ d →
      self.rank (Nat.iterate self.parent a x.val) <
        self.rank (Nat.iterate self.parent b x.val) := by
    intro a b hab
    induction hab with
    | refl => intro hbd; exact hstep a (Nat.lt_of_lt_of_le (Nat.lt_succ_self a) hbd)
    | @step b hab ih =>
      intro hbd
      exact (ih (Nat.le_trans (Nat.le_succ b) hbd)).trans
        (hstep b (Nat.lt_of_lt_of_le (Nat.lt_succ_self b) hbd))
  let f : Fin (d + 1) → Fin self.size :=
    fun k ↦ ⟨Nat.iterate self.parent k.val x.val, allocated_iterate self x k.val⟩
  have hf : Function.Injective f := by
    intro a b heq
    have he : Nat.iterate self.parent a.val x.val =
        Nat.iterate self.parent b.val x.val := congrArg Fin.val heq
    apply Fin.ext
    rcases lt_trichotomy a.val b.val with hlt | heq | hgt
    · have h := hstrict a.val b.val hlt (Nat.le_of_lt_succ b.isLt)
      rw [he] at h
      exact (Nat.lt_irrefl _ h).elim
    · exact heq
    · have h := hstrict b.val a.val hgt (Nat.le_of_lt_succ a.isLt)
      rw [he] at h
      exact (Nat.lt_irrefl _ h).elim
  have hc : d + 1 ≤ self.size := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf
  exact Nat.lt_of_succ_le hc

theorem exactSourceCount (self : UnionFind) (x : Fin self.size) :
    ∃ d : Nat,
      Nat.iterate self.parent d x.val = self.rootD x.val ∧
      (∀ k < d, Nat.iterate self.parent k x.val ≠ self.rootD x.val) ∧
      (countedFind self x).time = (d + 1, d) ∧ d < self.size := by
  obtain ⟨d, hroot, hfirst, htime⟩ := depth_aux self x
  exact ⟨d, hroot, hfirst, htime, first_depth_lt_size self x d hfirst⟩

end Internal

/-- The first original-parent-chain root occurs strictly before the allocated size. -/
public theorem exists_first_iterate_rootD (self : UnionFind) (x : Fin self.size) :
    ∃ d : Nat,
      Nat.iterate self.parent d x.val = self.rootD x.val ∧
      (∀ k < d, Nat.iterate self.parent k x.val ≠ self.rootD x.val) ∧
      d < self.size := by
  obtain ⟨d, hroot, hfirst, _, hsize⟩ := Internal.exactSourceCount self x
  exact ⟨d, hroot, hfirst, hsize⟩

end Batteries.UnionFind
