/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.DensestKSubgraph.Internal.Hardness.Row
public import CSLibExt.Computability.Complexity.DensestKSubgraph.Internal.Hardness.Correct
import CSLibExt.Computability.Complexity.Karp.SubsetSumDigits

/-! # Bounded reverse walk over the complete Karp adjacency stream -/

@[expose] public section

namespace Cslib.Complexity.DensestKSubgraph.Internal.CliqueWalk

open Turing Function MetaMathlibExt MetaMathlibExt.TM2Program MetaMathlibExt.TM2Embedding
open Cslib.Complexity.Karp MetaMathlibExt.BitstringEncoding
open Cslib.Complexity.DensestKSubgraph.Internal (markedEdges)
open Cslib.Complexity.DensestKSubgraph.Internal.CliqueCorrect (edgesOfBits)
open Cslib.Complexity.SatVerifier (Sym)

/- The first `i` rows of the Karp ordering, in reverse. -/
def revPairsPrefix (n : ℕ) : ℕ → List (ℕ × ℕ)
  | 0 => []
  | i + 1 => ((List.range' (i + 1) (n - (i + 1))).map (i, ·)) ++ revPairsPrefix n i

private theorem revPairsPrefix_eq (n i : ℕ) : revPairsPrefix n i =
    ((List.range i).flatMap fun a =>
      ((List.range n).reverse.filter (a < ·)).map (a, ·)).reverse := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [revPairsPrefix, List.range_succ, List.flatMap_append, List.flatMap_singleton,
      List.reverse_append, ← List.map_reverse, ← List.filter_reverse, List.reverse_reverse,
      EmitSS.filter_range_lt, ih]

/- At initialization the reversed list of pairs is exactly the input traversal. -/
theorem revPairs_eq (n : ℕ) : revPairsPrefix n n = (pairs n).reverse :=
  revPairsPrefix_eq n n

private theorem markedEdges_append {ps qs : List (ℕ × ℕ)} {xs ys : List Bool}
    (h : ps.length = xs.length) :
    markedEdges (ps ++ qs) (xs ++ ys) = markedEdges ps xs ++ markedEdges qs ys := by
  induction ps generalizing xs with
  | nil =>
    obtain rfl : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm)
    rfl
  | cons p ps ih =>
    rcases xs with _ | ⟨b, xs⟩
    · simp at h
    · have ht : ps.length = xs.length := Nat.succ.inj h
      cases b with
      | false => exact ih ht
      | true => exact congrArg (p :: ·) (ih ht)

private theorem markedEdges_reverse {ps : List (ℕ × ℕ)} {xs : List Bool}
    (h : ps.length = xs.length) :
    markedEdges ps.reverse xs.reverse = (markedEdges ps xs).reverse := by
  induction ps generalizing xs with
  | nil => simp [markedEdges]
  | cons p ps ih =>
    rcases xs with _ | ⟨b, xs⟩
    · simp at h
    · have ht : ps.length = xs.length := Nat.succ.inj h
      have hrev : ps.reverse.length = xs.reverse.length := by simpa using ht
      rw [List.reverse_cons, List.reverse_cons, markedEdges_append hrev, ih ht]
      cases b <;> simp [markedEdges]

private theorem bitEncode_list_append (xs ys : List (ℕ × ℕ)) :
    bitEncode (xs ++ ys) = bitEncode xs ++ bitEncode ys := by
  change (((xs ++ ys).map bitEncode).map delimit).flatten = _
  rw [List.map_append, List.map_append, List.flatten_append]
  rfl

private theorem row_eq (i j : ℕ) (xs out : List Bool) :
    CliqueRow.row i j xs out =
      bitEncode (markedEdges ((List.range' j xs.length).map (i, ·)) xs).reverse ++ out := by
  induction xs generalizing j out with
  | nil => rfl
  | cons b xs ih =>
    rw [CliqueRow.row, ih, List.length_cons, List.range'_succ, List.map_cons]
    cases b
    · rfl
    · change _ = bitEncode ((i, j) ::
        markedEdges ((List.range' (j + 1) xs.length).map (i, ·)) xs).reverse ++ out
      rw [List.reverse_cons, bitEncode_list_append, List.append_assoc]
      have hsingle : bitEncode ([(i, j)] : List (ℕ × ℕ)) = delimit (bitEncode (i, j)) := by
        change delimit (bitEncode (i, j)) ++ [] = _
        exact List.append_nil _
      rw [hsingle]
      simp

/- The pure stream output when the specified triangular prefix has the right length. -/
def emitPrefix (n : ℕ) : ℕ → List Bool → List Bool → List Bool
  | 0, _, out => out
  | i + 1, bits, out =>
    let d := n - (i + 1)
    emitPrefix n i (bits.drop d) (CliqueRow.row i (i + 1) (bits.take d) out)

private theorem prefix_eq (n i : ℕ) (bits out : List Bool)
    (h : bits.length = (revPairsPrefix n i).length) :
    emitPrefix n i bits out = bitEncode (markedEdges (revPairsPrefix n i) bits).reverse ++ out := by
  induction i generalizing bits out with
  | zero => rfl
  | succ i ih =>
    let d := n - (i + 1)
    have hlen : bits.length = d + (revPairsPrefix n i).length := by
      simpa [revPairsPrefix, d] using h
    have htake : (bits.take d).length = d := by simp [Nat.min_eq_left (by omega : d ≤ bits.length)]
    have hdrop : (bits.drop d).length = (revPairsPrefix n i).length := by
      simp [hlen]
    change emitPrefix n i (bits.drop d) (CliqueRow.row i (i + 1) (bits.take d) out) = _
    rw [ih _ _ hdrop, row_eq, htake, ← List.append_assoc, ← bitEncode_list_append,
      ← List.reverse_append]
    congr 3
    have hp : ((List.range' (i + 1) d).map (i, ·)).length = (bits.take d).length := by simp [htake]
    have hzip := markedEdges_append (qs := revPairsPrefix n i) (ys := bits.drop d) hp
    rw [List.take_append_drop] at hzip
    exact hzip.symm

/- The reverse walk emits the canonical edge-list encoding before its caller's suffix. -/
theorem emitPrefix_eq (n : ℕ) (bits out : List Bool) (h : bits.length = (pairs n).length) :
    emitPrefix n n bits.reverse out = bitEncode (edgesOfBits n bits) ++ out := by
  rw [prefix_eq n n bits.reverse out (by simpa [revPairs_eq] using h), revPairs_eq,
    markedEdges_reverse h.symm, List.reverse_reverse]
  rfl

/- A row machine plus a row-length counter and scratch to copy its counters. -/
inductive K | r (k : CliqueRow.K) | d | temp
  deriving DecidableEq

instance : Fintype K where
  elems := {K.d, .temp} ∪ Finset.univ.image K.r
  complete k := by cases k <;> simp

/- Physical unary row length, plus the existing heterogeneous row workspace. -/
@[reducible] def Γ : K → Type
  | .r k => CliqueRow.Γ k
  | .d | .temp => Sym

/- The row machine is resumed for each successive lower `i`. -/
inductive Lab | head | cpJ | restoreJ | incJ | cpD | restoreD | row (l : CliqueRow.Lab)
  | reset | incD | done
  deriving DecidableEq

instance : Fintype Lab where
  elems := {Lab.head, .cpJ, .restoreJ, .incJ, .cpD, .restoreD, .reset, .incD, .done} ∪
    Finset.univ.image Lab.row
  complete l := by cases l <;> simp

/- Keep the row length and its scratch outside the per-row machine. -/
def emb : SEmb CliqueRow.Γ Γ where
  e := K.r
  inj _ _ h := K.r.inj h
  ι _ := Equiv.refl _

/- Only the row's terminal label is redirected. -/
def redirect : CliqueRow.Lab → Lab
  | .done => .reset
  | l => .row l

/- Decrease `i`; set `j = i+1`; process `d` bits; increment `d` and repeat. -/
def prog : Lab → TM2.Stmt Γ Lab Bool
  | .head => decr (.r .i) .done .cpJ
  | .cpJ => xfer (.r .i) [⟨.r .j, EmitSS.U⟩, ⟨.temp, EmitSS.U⟩] .cpJ .restoreJ
  | .restoreJ => xfer .temp [⟨.r .i, EmitSS.U⟩] .restoreJ .incJ
  | .incJ => incr (.r .j) EmitSS.U .cpD
  | .cpD => xfer .d [⟨.r .left, EmitSS.U⟩, ⟨.temp, EmitSS.U⟩] .cpD .restoreD
  | .restoreD => xfer .temp [⟨.d, EmitSS.U⟩] .restoreD (.row .head)
  | .row l => mapS emb redirect (CliqueRow.prog l)
  | .reset => xfer (.r .j) [] .reset .incD
  | .incD => incr .d EmitSS.U .head
  | .done => .halt

private theorem embeds : Embeds emb redirect CliqueRow.prog prog := by
  intro l
  cases l <;> first | exact Or.inl rfl | exact Or.inr rfl

/- Exact stack layout at each row boundary or before entering a row. -/
def st (bits : List Bool) (i j left d : ℕ) (out : List Bool) : (k : K) → List (Γ k)
  | .r k => CliqueRow.st bits i j left out k
  | .d => cnt EmitSS.U d
  | .temp => []

private theorem st_update_i (bits out : List Bool) (i i' j l d : ℕ) :
    update (st bits i j l d out) (.r .i) (cnt EmitSS.U i') = st bits i' j l d out := by
  funext k
  cases k with
  | r k => cases k <;> simp [st, CliqueRow.st]
  | d | temp => rfl

private theorem st_update_j (bits out : List Bool) (i j j' l d : ℕ) :
    update (st bits i j l d out) (.r .j) (cnt EmitSS.U j') = st bits i j' l d out := by
  funext k
  cases k with
  | r k => cases k <;> simp [st, CliqueRow.st]
  | d | temp => rfl

private theorem st_update_l (bits out : List Bool) (i j l l' d : ℕ) :
    update (st bits i j l d out) (.r .left) (cnt EmitSS.U l') = st bits i j l' d out := by
  funext k
  cases k with
  | r k => cases k <;> simp [st, CliqueRow.st]
  | d | temp => rfl

private theorem st_update_d (bits out : List Bool) (i j l d d' : ℕ) :
    update (st bits i j l d out) .d (cnt EmitSS.U d') = st bits i j l d' out := by
  funext k
  cases k <;> simp [st]

private theorem row_full (i j d : ℕ) (bs rest out : List Bool) (h : bs.length = d)
    (v : Bool) :
    ∃ w, RunLe prog (d * (716 * (i + j + d) + 623) + 1)
      ⟨some (.row .head), v, st (bs ++ rest) i j d d out⟩
      ⟨some .reset, w, st rest i (j + d) 0 d (CliqueRow.row i j bs out)⟩ := by
  subst d
  obtain ⟨w, hrun⟩ := CliqueRow.run i j bs rest out v
  obtain ⟨T, h₁, h₂, h₃⟩ := runLe_embed redirect embeds hrun
    (S' := st (bs ++ rest) i j bs.length bs.length out) (by
      intro k
      exact (List.map_id _).symm)
  have he : T = st rest i (j + bs.length) 0 bs.length (CliqueRow.row i j bs out) := by
    funext k
    cases k with
    | r k => exact (h₂ k).trans (List.map_id _)
    | d | temp => exact h₃ _ (by intro k; simp [emb])
  exact ⟨w, he ▸ h₁⟩

private theorem run_one (i d : ℕ) (bs rest out : List Bool) (h : bs.length = d) (v : Bool) :
    ∃ w, RunLe prog (d * (716 * (i + (i + 1) + d) + 623) + (3 * i + 3 * d + 10))
      ⟨some .head, v, st (bs ++ rest) (i + 1) 0 0 d out⟩
      ⟨some .head, w, st rest i 0 0 (d + 1) (CliqueRow.row i (i + 1) bs out)⟩ := by
  let x := bs ++ rest
  have r₁ : Run prog 1 ⟨some .head, v, st x (i + 1) 0 0 d out⟩
      ⟨some .cpJ, true, st x i 0 0 d out⟩ := by
    rw [← st_update_i x out (i + 1) i 0 0 d]
    exact decr_run_cnt (M := prog) (self := .head) rfl v rfl
  have r₂ := copy_run (M := prog) (l₁ := .cpJ) (l₂ := .restoreJ) (next := .incJ)
    rfl rfl (by decide) (by decide) (by decide) i 0 true (st x i 0 0 d out) rfl rfl rfl
  rw [show i + 0 = i from rfl, st_update_j] at r₂
  have r₃ := incr_run (M := prog) (self := .incJ) rfl false (st x i i 0 d out)
  change Run prog 1 ⟨some .incJ, false, st x i i 0 d out⟩
    ⟨some .cpD, false, update (st x i i 0 d out) (.r .j) (cnt EmitSS.U (i + 1))⟩ at r₃
  rw [st_update_j] at r₃
  have r₄ := copy_run (M := prog) (l₁ := .cpD) (l₂ := .restoreD) (next := .row .head)
    rfl rfl (by decide) (by decide) (by decide) d 0 false (st x i (i + 1) 0 d out) rfl rfl rfl
  rw [show d + 0 = d from rfl, st_update_l] at r₄
  obtain ⟨w, r₅⟩ := row_full i (i + 1) d bs rest out h (Flag.tag false)
  let out' := CliqueRow.row i (i + 1) bs out
  have r₆ := xfer_run (M := prog) (self := .reset) rfl (by simp) (by simp) EmitSS.U (i + 1 + d)
    w (st rest i (i + 1 + d) 0 d out') rfl
  change Run prog (i + 1 + d + 1) _ ⟨some .incD, Flag.tag false,
    update (st rest i (i + 1 + d) 0 d out') (.r .j) (cnt EmitSS.U 0)⟩ at r₆
  rw [st_update_j] at r₆
  have r₇ := incr_run (M := prog) (self := .incD) rfl false (st rest i 0 0 d out')
  change Run prog 1 _ ⟨some .head, false,
    update (st rest i 0 0 d out') .d (cnt EmitSS.U (d + 1))⟩ at r₇
  rw [st_update_d] at r₇
  refine ⟨false, ((((r₁.trans r₂).trans r₃).trans r₄).le le_rfl |>.trans r₅
    |>.trans ((r₆.trans r₇).le le_rfl)).mono (by omega)⟩

/- The whole triangular walk, with a polynomial bound in the physical vertex count. -/
theorem run (n i : ℕ) (hi : i ≤ n) (bits out : List Bool) (v : Bool)
    (h : bits.length = (revPairsPrefix n i).length) :
    ∃ w, RunLe prog (i * (n * (1432 * n + 623) + (6 * n + 10)) + 1)
      ⟨some .head, v, st bits i 0 0 (n - i) out⟩
      ⟨some .done, w, st [] 0 0 0 n (emitPrefix n i bits out)⟩ := by
  induction i generalizing bits out v with
  | zero =>
    have hb : bits = [] := List.eq_nil_of_length_eq_zero h
    subst bits
    refine ⟨Flag.tag false, ?_⟩
    simpa only [Nat.zero_mul, Nat.zero_add, Nat.sub_zero, emitPrefix] using
      (decr_run_zero (M := prog) (self := .head) rfl v (S := st [] 0 0 0 n out) rfl).le le_rfl
  | succ i ih =>
    let d := n - (i + 1)
    have hlen : bits.length = d + (revPairsPrefix n i).length := by
      simpa [revPairsPrefix, d] using h
    have htake : (bits.take d).length = d := by simp [Nat.min_eq_left (by omega : d ≤ bits.length)]
    have hdrop : (bits.drop d).length = (revPairsPrefix n i).length := by simp [hlen]
    obtain ⟨w, h₁⟩ := run_one i d (bits.take d) (bits.drop d) out htake v
    rw [List.take_append_drop, show d + 1 = n - i by dsimp [d]; omega] at h₁
    obtain ⟨w', h₂⟩ :=
      ih (by omega) (bits.drop d) (CliqueRow.row i (i + 1) (bits.take d) out) w hdrop
    have hd : d ≤ n := Nat.sub_le _ _
    have hf : 716 * (i + (i + 1) + d) + 623 ≤ 1432 * n + 623 := by dsimp [d]; omega
    have hprod := Nat.mul_le_mul hd hf
    have hlocal := Nat.add_le_add hprod (show 3 * i + 3 * d + 10 ≤ 6 * n + 10 by omega)
    refine ⟨w', (h₁.trans h₂).mono ?_⟩
    rw [Nat.succ_mul i]
    let B := n * (1432 * n + 623) + (6 * n + 10)
    exact (Nat.add_le_add_right hlocal (i * B + 1)).trans_eq (by
      change B + (i * B + 1) = i * B + B + 1
      ac_rfl)

end Cslib.Complexity.DensestKSubgraph.Internal.CliqueWalk
