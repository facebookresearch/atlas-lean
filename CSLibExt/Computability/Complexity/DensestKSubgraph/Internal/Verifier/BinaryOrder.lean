/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Karp.SubsetSumDigits
import MathlibExt.Computability.BinaryNatEncoding

/-! # Bit-length-bounded comparison on two finite stacks -/

@[expose] public section

namespace Cslib.Complexity.DensestKSubgraph.Internal.BinaryOrder

open Turing MetaMathlibExt.TM2Program MetaMathlibExt.TM2Recursive
open Cslib.Complexity.Karp.EmitSS (bitsVal_cons bitsVal_nil)

/- Only the two bit words are touched by the destructive comparator. -/
inductive K | a | b
  deriving DecidableEq

instance : Fintype K := Fintype.ofList [.a, .b] (by intro k; cases k <;> decide)

/- The last significant comparison is retained in the finite control. -/
inductive Lab | scan (s : Ordering) | done (s : Ordering)
  deriving DecidableEq

instance : Fintype Lab := Fintype.ofList
  [.scan .lt, .scan .eq, .scan .gt, .done .lt, .done .eq, .done .gt]
  (by intro l; cases l with | scan s | done s => cases s <;> decide)

/- A later (more significant) unequal bit overrides the current comparison. -/
def mergeOrder (lower upper : Ordering) : Ordering :=
  if upper = .eq then lower else upper

/- The comparison of two Boolean digits as numbers. -/
def digitOrder (a b : Bool) : Ordering :=
  if a == b then .eq else if a then .gt else .lt

private theorem merge_assoc (a b c : Ordering) :
    mergeOrder (mergeOrder a b) c = mergeOrder a (mergeOrder b c) := by
  cases c <;> rfl

private theorem cmp_digit (a b : Bool) (x y : ℕ) :
    compare (a.toNat + 2 * x) (b.toNat + 2 * y) =
      mergeOrder (digitOrder a b) (compare x y) := by
  rcases lt_trichotomy x y with h | rfl | h
  · have h' : a.toNat + 2 * x < b.toNat + 2 * y := by cases a <;> cases b <;> simp <;> omega
    rw [Nat.compare_eq_lt.mpr h, Nat.compare_eq_lt.mpr h']
    rfl
  · cases a <;> cases b <;> simp [digitOrder, mergeOrder, Nat.compare_eq_lt, Nat.compare_eq_gt]
  · have h' : b.toNat + 2 * y < a.toNat + 2 * x := by cases a <;> cases b <;> simp <;> omega
    rw [Nat.compare_eq_gt.mpr h, Nat.compare_eq_gt.mpr h']
    rfl

/- Pop the bottom-significance head digits (implicit zero when one word is exhausted). -/
def popDigits (s : Ordering) : TM2.Stmt (fun _ : K => Bool) Lab Bool :=
  .pop .a (fun _ o => o.getD false) <| .branch id
    (.pop .b (fun _ o => o.getD false) <| .goto fun b => .scan (mergeOrder s (digitOrder true b)))
    (.pop .b (fun _ o => o.getD false) <| .goto fun b => .scan (mergeOrder s (digitOrder false b)))

/- Stop only when both words are exhausted; never count up to their values. -/
def prog : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool
  | .scan s => .peek .a (fun _ o => o.isSome) <| .branch id (popDigits s)
      (.peek .b (fun _ o => o.isSome) <| .branch id (popDigits s) (.goto fun _ => .done s))
  | .done _ => .halt

/- Stack contents for the two binary input words. -/
def st (a b : List Bool) : K → List Bool
  | .a => a
  | .b => b

private theorem pop_step (s : Ordering) (a b : List Bool) (v : Bool)
    (h : a ≠ [] ∨ b ≠ []) :
    Run prog 1 ⟨some (.scan s), v, st a b⟩
      ⟨some (.scan (mergeOrder s (digitOrder (a.headD false) (b.headD false)))),
        b.headD false, st a.tail b.tail⟩ := by
  apply Run.single
  cases a with
  | nil =>
    cases b with
    | nil => simp at h
    | cons y b =>
      have he : Function.update (Function.update (st [] (y :: b)) K.a []) K.b b = st [] b := by
        funext k
        cases k <;> simp [st]
      simpa [prog, popDigits, st, TM2.stepAux] using he
  | cons x a =>
    have he : Function.update (Function.update (st (x :: a) b) K.a a) K.b b.tail = st a b.tail := by
      funext k
      cases k <;> simp [st]
    cases x <;> simpa [prog, popDigits, TM2.stepAux, st] using he

private theorem cmp_tail (a b : List Bool) :
    compare (bitsVal a) (bitsVal b) =
      mergeOrder (digitOrder (a.headD false) (b.headD false))
        (compare (bitsVal a.tail) (bitsVal b.tail)) := by
  have hv (w : List Bool) : bitsVal w = (w.headD false).toNat + 2 * bitsVal w.tail := by
    cases w <;> simp
  conv_lhs => rw [hv a, hv b]
  exact cmp_digit _ _ _ _

/- Comparison of arbitrary raw bit words in time linear in their lengths, including empty
or zero-padded words. `s` is the comparison of any less significant bits already consumed. -/
theorem run (a b : List Bool) (s : Ordering) (v : Bool) :
    ∃ w, RunLe prog (a.length + b.length + 1) ⟨some (.scan s), v, st a b⟩
      ⟨some (.done (mergeOrder s (compare (bitsVal a) (bitsVal b)))), w, st [] []⟩ := by
  by_cases h : a = [] ∧ b = []
  · obtain ⟨rfl, rfl⟩ := h
    exact ⟨false, (Run.single (by simp [prog, st, TM2.stepAux, mergeOrder])).le (by simp)⟩
  · have hn : a ≠ [] ∨ b ≠ [] := not_and_or.mp h
    have hlen : a.tail.length + b.tail.length < a.length + b.length := by
      cases a <;> cases b <;> simp_all; omega
    let s' := mergeOrder s (digitOrder (a.headD false) (b.headD false))
    obtain ⟨w, ht⟩ := run a.tail b.tail s' (b.headD false)
    have hcmp : mergeOrder s (compare (bitsVal a) (bitsVal b)) =
        mergeOrder s' (compare (bitsVal a.tail) (bitsVal b.tail)) := by
      rw [cmp_tail a b, ← merge_assoc]
    rw [hcmp]
    exact ⟨w, ((pop_step s a b v hn).le (Nat.le_refl _)).trans ht |>.mono (by omega)⟩
termination_by a.length + b.length

/- In particular, canonical binary naturals can be compared without building unary counters. -/
theorem run_encodeNat (a b : ℕ) (v : Bool) :
    ∃ w, RunLe prog (a.size + b.size + 1)
      ⟨some (.scan .eq), v, st (Computability.encodeNat a) (Computability.encodeNat b)⟩
      ⟨some (.done (compare a b)), w, st [] []⟩ := by
  have h (o : Ordering) : mergeOrder .eq o = o := by cases o <;> rfl
  simpa only [MetaMathlibExt.BinaryNatEncoding.length_encodeNat, bitsVal_encodeNat, h] using
    run (Computability.encodeNat a) (Computability.encodeNat b) .eq v

end Cslib.Complexity.DensestKSubgraph.Internal.BinaryOrder
