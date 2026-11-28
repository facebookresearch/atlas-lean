/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.NPComplete.ConstrainedSequencingToMinimizeTardyTaskWeightDefs
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.Complexity
import CSLibExt.Computability.CookLevin
import CSLibExt.Computability.Complexity.Basic
import CSLibExt.Computability.Complexity.Host
import CSLibExt.Computability.Complexity.Karp.PartitionComplete
import CSLibExt.Computability.Complexity.Karp.PartitionMembership
import CSLibExt.Computability.Complexity.PolynomialEncoding.Copy
import CSLibExt.Computability.Complexity.PolynomialEncoding.Frame
import CSLibExt.Computability.Complexity.PolynomialEncoding.ListNat
import CSLibExt.Computability.Complexity.PolynomialEncoding.ListParts
import MathlibExt.Computability.TuringMachine.BitOps
import MathlibExt.Computability.TuringMachine.Composition
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Permutation

/-!
# CONSTRAINED SEQUENCING TO MINIMIZE TARDY TASK WEIGHT is NP-hard

PARTITION reduces to it by a composition of polynomial-time maps. A three-state transducer on
the framed size list drops zero sizes, multiplies the others by `4` and adds the sizes `1, 1`
in front, which keeps PARTITION's answer and makes every size positive and the list nonempty.
The existing PARTITION-to-SUBSET-SUM map and the weighted tardy jobs construction (one task
`(2a, Σ, 2a)` per size `a`, bound `Σ`) follow, and the instance is completed with `S = [0]` and
`J = 1`. In an equal split either half can run first, so the half containing task `0` is
scheduled first and task `0` meets its deadline. Malformed input stays malformed.

The weighted tardy jobs construction and its correctness lemmas are adapted from the private
declarations of `CSLibExt/Computability/Complexity/Karp/WeightedTardyJobs.lean`, and the wrapping
machine follows the `PadMachine` of `CSLibExt/Computability/Complexity/Karp/MultiwayPartition.lean`.

Source: M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), PARTITION [SP12].
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConstrainedSequencingToMinimizeTardyTaskWeight

open MetaMathlibExt.BitstringEncoding Cslib.Complexity.PolynomialEncoding

private theorem decodeNat_eq_zero_iff (p : List Bool) :
    Computability.decodeNat p = 0 ↔ p = [] := by
  constructor
  · intro h
    by_contra hp
    simp [Computability.decodeNat, Computability.decodeNum, hp] at h
    exact (PosNum.cast_pos (α := ℕ) _).ne' h
  · rintro rfl
    rfl

private theorem decodeNat_ff (p : List Bool) (hp : p ≠ []) :
    Computability.decodeNat (false :: false :: p) = 4 * Computability.decodeNat p := by
  simp [Computability.decodeNat, Computability.decodeNum, Computability.decodePosNum, hp]
  omega

/-- States of the zero-stripping transducer on a framed list of payloads: at a block start, after
a pair marker (a payload bit follows), and inside a block (a marker or the terminator follows). -/
private inductive St | a | b | c

/-- Drop every empty payload (the encoding of `0`) and prefix every other payload with two zero
bits, which multiplies its value by `4`. Malformed input stays malformed. -/
private def strip : St → List Bool → List Bool
  | .a, [] => []
  | .a, false :: r => strip .a r
  | .a, true :: r => true :: false :: true :: false :: true :: strip .b r
  | .b, [] => []
  | .b, x :: r => x :: strip .c r
  | .c, [] => []
  | .c, true :: r => true :: strip .b r
  | .c, false :: r => false :: strip .a r

private theorem strip_c_delimit (p r : List Bool) :
    strip .c (delimit p ++ r) = delimit p ++ strip .a r := by
  induction p with
  | nil => rfl
  | cons x p ih => simp [delimit, strip, ih]

private theorem strip_a_delimit (p r : List Bool) :
    strip .a (delimit p ++ r) =
      (if p = [] then [] else delimit (false :: false :: p)) ++ strip .a r := by
  cases p with
  | nil => rfl
  | cons x p => simp [delimit, strip, strip_c_delimit]

private theorem undelimit_strip_c : ∀ (n : ℕ) (y : List Bool), y.length ≤ n →
    undelimit y = none → undelimit (strip .c y) = none := by
  intro n
  induction n with
  | zero =>
    intro y hy _
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hy)]
    rfl
  | succ n ih =>
    intro y hy h
    match y, hy, h with
    | [], _, _ => rfl
    | false :: r, _, h => simp [undelimit] at h
    | [true], _, _ => rfl
    | true :: x :: r, hy, h =>
      simp only [undelimit, Option.map_eq_none_iff] at h
      simp only [strip, undelimit, Option.map_eq_none_iff]
      exact ih r (by simp at hy; omega) h

private theorem undelimitBlocks_nil : undelimitBlocks [] = some [] := rfl

private theorem undelimitBlocks_none {x : List Bool} (hx : x ≠ []) (h : undelimit x = none) :
    undelimitBlocks x = none := by
  cases x with
  | nil => exact (hx rfl).elim
  | cons b xs => simp [undelimitBlocks, undelimitBlocksAux, h]

private theorem blocks_strip : ∀ (n : ℕ) (x : List Bool), x.length ≤ n →
    undelimitBlocks (strip .a x) = (undelimitBlocks x).map
      (fun bs => (bs.filter (· ≠ [])).map (false :: false :: ·)) := by
  intro n
  induction n with
  | zero =>
    intro x hx
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hx)]
    rfl
  | succ n ih =>
    intro x hx
    by_cases hnil : x = []
    · subst hnil
      rfl
    have hne : x ≠ [] := hnil
    cases h : undelimit x with
    | some pr =>
      obtain ⟨p, r⟩ := pr
      have hx' := (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).1 h
      subst hx'
      have hr : r.length ≤ n := by
        simp only [List.length_append, length_delimit] at hx
        omega
      rw [strip_a_delimit, blocks_delimit, Option.map_map]
      by_cases hp : p = []
      · subst hp
        simp only [↓reduceIte, List.nil_append, ih r hr]
        rfl
      · simp only [hp, ↓reduceIte, blocks_delimit, ih r hr, Option.map_map]
        congr 1
        funext bs
        simp [hp]
    | none =>
      rw [undelimitBlocks_none hne h]
      match x, hne, h with
      | false :: r, _, h => simp [undelimit] at h
      | true :: r, _, h =>
        apply undelimitBlocks_none (by simp [strip])
        have hc := undelimit_strip_c _ (true :: r) le_rfl h
        simp only [strip] at hc ⊢
        simp only [undelimit, Option.map_eq_none_iff] at hc ⊢
        exact hc

/-- The two framed entries `1, 1`. -/
private abbrev pre : List Bool := delimit [true] ++ delimit [true]

private theorem map_decode_strip (bs : List (List Bool)) :
    ((bs.filter (· ≠ [])).map (false :: false :: ·)).map Computability.decodeNat =
      ((bs.map Computability.decodeNat).filter (· ≠ 0)).map (4 * ·) := by
  induction bs with
  | nil => rfl
  | cons p bs ih =>
    by_cases hp : p = []
    · subst hp
      have hz : Computability.decodeNat [] = 0 := rfl
      simp only [List.filter_cons, List.map_cons, hz] at ih ⊢
      simpa using ih
    · have h0 : Computability.decodeNat p ≠ 0 := fun h => hp ((decodeNat_eq_zero_iff p).1 h)
      simp only [List.filter_cons, List.map_cons] at ih ⊢
      simp only [ne_eq, hp, h0, not_false_eq_true, decide_true, ↓reduceIte, List.map_cons,
        decodeNat_ff p hp, ih]

private theorem decode_pre_strip (x : List Bool) :
    bitDecode (α := List ℕ) (pre ++ strip .a x) = (bitDecode (α := List ℕ) x).map
      (fun as => 1 :: 1 :: (as.filter (· ≠ 0)).map (4 * ·)) := by
  rw [decode_list_nat, decode_list_nat, List.append_assoc, blocks_delimit, blocks_delimit,
    blocks_strip _ x le_rfl]
  cases undelimitBlocks x with
  | none => rfl
  | some bs =>
    simp only [Option.map_some, List.map_cons, map_decode_strip]
    rfl

open MetaMathlibExt.Complexity.NPComplete.Partition (PartitionFeasible partitionDec)

private theorem sum_filter_ne_zero (l : List ℕ) : (l.filter (· ≠ 0)).sum = l.sum := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases ha : a = 0 <;> simp_all

private theorem partition_filter (l : List ℕ) :
    PartitionFeasible (l.filter (· ≠ 0)) ↔ PartitionFeasible l := by
  constructor
  · rintro ⟨s, hs, he⟩
    exact ⟨s, hs.trans List.filter_sublist, by rw [he, sum_filter_ne_zero]⟩
  · rintro ⟨s, hs, he⟩
    exact ⟨s.filter (· ≠ 0), hs.filter _, by rw [sum_filter_ne_zero, sum_filter_ne_zero, he]⟩

private theorem sum_map_four (l : List ℕ) : (l.map (4 * ·)).sum = 4 * l.sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- Two unit entries next to entries scaled by `4` must go to different sides. -/
private theorem partition_pad (l : List ℕ) :
    PartitionFeasible (1 :: 1 :: l.map (4 * ·)) ↔ PartitionFeasible l := by
  constructor
  · rintro ⟨s, hs, he⟩
    simp only [List.sum_cons, sum_map_four] at he
    have key : ∀ t : List ℕ, t.Sublist (l.map (4 * ·)) →
        ∃ r : List ℕ, r.Sublist l ∧ t.sum = 4 * r.sum := by
      intro t ht
      obtain ⟨r, hr, rfl⟩ := List.sublist_map_iff.1 ht
      exact ⟨r, hr, sum_map_four r⟩
    rcases List.sublist_cons_iff.1 hs with hs | ⟨t, rfl, ht⟩
    · rcases List.sublist_cons_iff.1 hs with hs | ⟨t, rfl, ht⟩
      · obtain ⟨r, -, hr⟩ := key s hs
        omega
      · obtain ⟨r, hr, hsum⟩ := key t ht
        simp only [List.sum_cons] at he
        exact ⟨r, hr, by omega⟩
    · rcases List.sublist_cons_iff.1 ht with ht | ⟨u, rfl, hu⟩
      · obtain ⟨r, hr, hsum⟩ := key t ht
        simp only [List.sum_cons] at he
        exact ⟨r, hr, by omega⟩
      · obtain ⟨r, -, hsum⟩ := key u hu
        simp only [List.sum_cons] at he
        omega
  · rintro ⟨s, hs, he⟩
    refine ⟨1 :: s.map (4 * ·), ((hs.map _).cons 1).cons_cons 1, ?_⟩
    simp only [List.sum_cons, sum_map_four]
    omega

private theorem strip_length : ∀ (s : St) (x : List Bool), (strip s x).length ≤ 5 * x.length
  | .a, [] => le_rfl
  | .a, false :: r => by have := strip_length .a r; simp [strip]; omega
  | .a, true :: r => by have := strip_length .b r; simp [strip]; omega
  | .b, [] => le_rfl
  | .b, _ :: r => by have := strip_length .c r; simp [strip]; omega
  | .c, [] => le_rfl
  | .c, true :: r => by have := strip_length .b r; simp [strip]; omega
  | .c, false :: r => by have := strip_length .a r; simp [strip]; omega

/-- Normalization of a PARTITION input: drop zero sizes, scale the others by `4` and add the
sizes `1, 1` in front. -/
private def normalize (x : List Bool) : List Bool := pre ++ strip .a x

namespace NormMachine

open Turing Function TM2Program Cslib.Complexity.PolynomialEncoding

private inductive K | input | scratch | output
  deriving DecidableEq

private inductive Lab | start | sa | sb | sc | move | done
  deriving DecidableEq

private instance instFintypeK : Fintype K where
  elems := {K.input, .scratch, .output}
  complete k := by cases k <;> decide

private instance instFintypeLab : Fintype Lab where
  elems := {Lab.start, .sa, .sb, .sc, .move, .done}
  complete l := by cases l <;> decide

private def lab : St → Lab
  | .a => .sa
  | .b => .sb
  | .c => .sc

private def prog : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool
  | .start => pushList .scratch pre <| .goto fun _ => .sa
  | .sa => .peek .input (fun _ o => isBit some o) <| .branch id
      (.pop .input (fun _ o => bitOf some o) <| .branch id
        (pushList .scratch [true, false, true, false, true] <| .goto fun _ => .sb)
        (.goto fun _ => .sa))
      (.goto fun _ => .move)
  | .sb => .peek .input (fun _ o => isBit some o) <| .branch id
      (.pop .input (fun _ o => bitOf some o) <| .push .scratch id <| .goto fun _ => .sc)
      (.goto fun _ => .move)
  | .sc => .peek .input (fun _ o => isBit some o) <| .branch id
      (.pop .input (fun _ o => bitOf some o) <| .push .scratch id <|
        .branch id (.goto fun _ => .sb) (.goto fun _ => .sa))
      (.goto fun _ => .move)
  | .move => moveB .scratch .output some id .move .done
  | .done => .halt

private def st (x y z : List Bool) : K → List Bool
  | .input => x
  | .scratch => y
  | .output => z

private theorem loop : ∀ (x : List Bool) (s : St) (y z : List Bool) (v : Bool), ∃ v',
    Run prog (x.length + 1) ⟨some (lab s), v, st x y z⟩
      ⟨some .move, v', st [] ((strip s x).reverse ++ y) z⟩
  | [], s, y, z, v => by
    refine ⟨false, Run.single ?_⟩
    cases s <;> simp [prog, lab, TM2.stepAux, isBit, st, strip]
  | b :: x, s, y, z, v => by
    cases s <;> cases b
    · obtain ⟨v', h⟩ := loop x .a y z false
      refine ⟨v', Run.head ?_ (h.of_eq rfl) |>.of_eq (by simp)⟩
      simp [TM2.step, prog, lab, TM2.stepAux, isBit, bitOf, st]
      funext k; cases k <;> rfl
    · obtain ⟨v', h⟩ := loop x .b ([true, false, true, false, true] ++ y) z true
      have e : (strip .a (true :: x)).reverse ++ y =
          (strip .b x).reverse ++ ([true, false, true, false, true] ++ y) := by
        simp [strip]
      refine ⟨v', ?_⟩
      rw [e]
      refine Run.head ?_ h
      simp [TM2.step, prog, lab, TM2.stepAux, isBit, bitOf, st, stepAux_pushList]
      funext k; cases k <;> rfl
    · obtain ⟨v', h⟩ := loop x .c (false :: y) z false
      have e : (strip .b (false :: x)).reverse ++ y = (strip .c x).reverse ++ (false :: y) := by
        simp [strip]
      refine ⟨v', ?_⟩
      rw [e]
      refine Run.head ?_ h
      simp [TM2.step, prog, lab, TM2.stepAux, isBit, bitOf, st]
      funext k; cases k <;> rfl
    · obtain ⟨v', h⟩ := loop x .c (true :: y) z true
      have e : (strip .b (true :: x)).reverse ++ y = (strip .c x).reverse ++ (true :: y) := by
        simp [strip]
      refine ⟨v', ?_⟩
      rw [e]
      refine Run.head ?_ h
      simp [TM2.step, prog, lab, TM2.stepAux, isBit, bitOf, st]
      funext k; cases k <;> rfl
    · obtain ⟨v', h⟩ := loop x .a (false :: y) z false
      have e : (strip .c (false :: x)).reverse ++ y = (strip .a x).reverse ++ (false :: y) := by
        simp [strip]
      refine ⟨v', ?_⟩
      rw [e]
      refine Run.head ?_ h
      simp [TM2.step, prog, lab, TM2.stepAux, isBit, bitOf, st]
      funext k; cases k <;> rfl
    · obtain ⟨v', h⟩ := loop x .b (true :: y) z true
      have e : (strip .c (true :: x)).reverse ++ y = (strip .b x).reverse ++ (true :: y) := by
        simp [strip]
      refine ⟨v', ?_⟩
      rw [e]
      refine Run.head ?_ h
      simp [TM2.step, prog, lab, TM2.stepAux, isBit, bitOf, st]
      funext k; cases k <;> rfl

private theorem run (x : List Bool) :
    ∃ v S, RunLe prog (6 * x.length + 10) ⟨some .start, false, st x [] []⟩
      ⟨some .done, v, S⟩ ∧ S .output = normalize x := by
  have h₀ : Run prog 1 ⟨some .start, false, st x [] []⟩
      ⟨some .sa, false, st x pre.reverse []⟩ := by
    apply Run.single
    simp only [prog, stepAux_pushList, TM2.stepAux, TM2.Cfg.mk.injEq, true_and]
    funext k
    cases k <;> simp [st]
  obtain ⟨v₁, h₁⟩ := loop x .a pre.reverse [] false
  have hs : (strip .a x).reverse ++ pre.reverse = (normalize x).reverse := by
    simp [normalize]
  rw [hs] at h₁
  obtain ⟨v, T, h₂, _, ht, _⟩ := moveB_run (M := prog)
    (a := K.scratch) (b := .output) (self := .move) (next := .done)
    (d := some) (g := id) rfl (by decide) (normalize x).reverse (normalize x).reverse [] v₁
    (st [] (normalize x).reverse [])
    (by simp [st]) (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  refine ⟨v, T, (h₀.trans (h₁.trans h₂)).le ?_, ?_⟩
  · have := strip_length .a x
    simp only [normalize, List.length_reverse, List.length_append]
    simp only [List.length_cons, List.length_nil, length_delimit] at this ⊢
    omega
  · simpa [st] using ht

private noncomputable abbrev comp : Cslib.Complexity.Host.Comp where
  K := K
  Γ := fun _ => Bool
  L := Lab
  prog := prog
  ks := [.input, .scratch, .output]
  ks_nodup := by decide
  mem_ks k := by cases k <;> decide

private theorem isPolyTime_normalize : ComplexityTheory.IsPolyTime normalize :=
  Cslib.Complexity.Host.isPolyTime_reduction
    (c := comp) (cX := .input) (cO := .output) (gX := id) (start := .start) (done := .done)
    (Equiv.refl Bool) normalize (Polynomial.C 6 * Polynomial.X + Polynomial.C 10) rfl
    (fun x => by
      have he : update (fun _ : K => ([] : List Bool)) .input x = st x [] [] := by
        funext k
        cases k <;> rfl
      simpa [he] using run x)

end NormMachine

/-- The fixed suffix `S = [0]`, `J = 1`. -/
private abbrev sfx : List Bool := bitEncode (([0], 1) : List ℕ × ℕ)

/-- Frame a weighted tardy jobs encoding and append `S = [0]`, `J = 1`. -/
private def wrap (y : List Bool) : List Bool := delimit y ++ sfx

/-! The wrapping machine follows the `PadMachine` of
`CSLibExt/Computability/Complexity/Karp/MultiwayPartition.lean`. -/
namespace WrapMachine

open Turing Function TM2Program Cslib.Complexity.PolynomialEncoding

private inductive K | input | scratch | output
  deriving DecidableEq

private inductive Lab | start | frame | finish | done
  deriving DecidableEq

private instance instFintypeK : Fintype K where
  elems := {K.input, .scratch, .output}
  complete k := by cases k <;> decide

private instance instFintypeLab : Fintype Lab where
  elems := {Lab.start, .frame, .finish, .done}
  complete l := by cases l <;> decide

private def prog : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool
  | .start => emitR .output sfx .frame
  | .frame => emitFrame .input .scratch some id .frame .finish
  | .finish => moveB .scratch .output some id .finish .done
  | .done => .halt

private def st (x y z : List Bool) : K → List Bool
  | .input => x
  | .scratch => y
  | .output => z

private theorem run (x : List Bool) :
    ∃ v S, RunLe prog (4 * x.length + 8) ⟨some .start, false, st x [] []⟩
      ⟨some .done, v, S⟩ ∧ S .output = wrap x := by
  have h₀ : Run prog 1 ⟨some .start, false, st x [] []⟩
      ⟨some .frame, false, st x [] sfx⟩ := by
    apply Run.single
    simp only [prog, emitR, emit, stepAux_pushList, TM2.stepAux, TM2.Cfg.mk.injEq, true_and]
    funext k
    cases k <;> simp [st]
  obtain ⟨S, h₁, _, hs, ho⟩ := emitFrame_run (M := prog)
    (a := K.input) (b := .scratch) (self := .frame) (next := .finish)
    (d := some) (g := id) rfl (by decide) id (fun _ => rfl) x [] false (st x [] sfx)
    (by simp [EndsBitBlock]) (by simp [st])
  have he : S .scratch = (delimit x).reverse := by simpa [st] using hs
  obtain ⟨v, T, h₂, _, ht, _⟩ := moveB_run (M := prog)
    (a := K.scratch) (b := .output) (self := .finish) (next := .done)
    (d := some) (g := id) rfl (by decide) (delimit x).reverse (delimit x).reverse [] false S
    (by simpa using he) (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  refine ⟨v, T, (h₀.trans (h₁.trans h₂)).le ?_, ?_⟩
  · simp only [List.length_reverse, length_delimit]
    omega
  · simpa [wrap, ho .output (by decide) (by decide), st] using ht

private noncomputable abbrev comp : Cslib.Complexity.Host.Comp where
  K := K
  Γ := fun _ => Bool
  L := Lab
  prog := prog
  ks := [.input, .scratch, .output]
  ks_nodup := by decide
  mem_ks k := by cases k <;> decide

private theorem isPolyTime_wrap : ComplexityTheory.IsPolyTime wrap :=
  Cslib.Complexity.Host.isPolyTime_reduction
    (c := comp) (cX := .input) (cO := .output) (gX := id) (start := .start) (done := .done)
    (Equiv.refl Bool) wrap (Polynomial.C 4 * Polynomial.X + Polynomial.C 8) rfl (fun x => by
      have he : update (fun _ : K => ([] : List Bool)) .input x = st x [] [] := by
        funext k
        cases k <;> rfl
      simpa [he] using run x)

end WrapMachine

/-! The following section is adapted from
`CSLibExt/Computability/Complexity/Karp/WeightedTardyJobs.lean`, where these declarations are
private. -/
namespace Tardy

open WeightedTardyJobs

open BitstringEncoding

/-! ### Correctness of the scheduling reduction -/

private def job (due a : ℕ) : ℕ × ℕ × ℕ := (2 * a, due, 2 * a)

private def partitionJobs (as : List ℕ) : WeightedTardyJobsInstance :=
  (as.map (job as.sum), as.sum)

private def addTardy (d : ℕ) (acc : ℕ × ℕ) (a : ℕ) : ℕ × ℕ :=
  (acc.1 + 2 * a, acc.2 + if d < acc.1 + 2 * a then 2 * a else 0)

private theorem map_range_getD {α : Type} (xs : List α) (default : α) :
    (List.range xs.length).map (xs.getD · default) = xs := by
  apply List.ext_getElem
  · simp
  · intro n _ hn
    simp [List.getElem?_eq_getElem hn]

private theorem foldl_indices (d : ℕ) (as order : List ℕ) (acc : ℕ × ℕ) :
    order.foldl (WeightedTardyStep (as.map (job d))) acc =
      (order.map (as.getD · 0)).foldl (addTardy d) acc := by
  rw [List.foldl_map]
  congr 1
  funext s j
  simp only [WeightedTardyStep, addTardy, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : as[j]? with
  | none => simp
  | some a => simp [job, Nat.mul_comm 2 a]

private theorem foldl_tardy_le (d : ℕ) (as : List ℕ) (t w : ℕ) :
    (as.foldl (addTardy d) (t, w)).2 ≤ w + 2 * as.sum := by
  induction as generalizing t w with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl_cons, addTardy, List.sum_cons]
    specialize ih (t + 2 * a) (w + if d < t + 2 * a then 2 * a else 0)
    have hfee : (if d < t + 2 * a then 2 * a else 0) ≤ 2 * a := by split <;> omega
    omega

private theorem foldl_all_tardy (d : ℕ) (as : List ℕ) (t w : ℕ) (h : d < t) :
    (as.foldl (addTardy d) (t, w)).2 = w + 2 * as.sum := by
  induction as generalizing t w with
  | nil => simp
  | cons a as ih =>
    have h' : d < t + 2 * a := by omega
    simp [addTardy, h', ih (t + 2 * a) (w + 2 * a) h']
    omega

private theorem foldl_on_time (d : ℕ) (as : List ℕ) (t w : ℕ)
    (h : t + 2 * as.sum ≤ d) :
    as.foldl (addTardy d) (t, w) = (t + 2 * as.sum, w) := by
  induction as generalizing t w with
  | nil => simp
  | cons a as ih =>
    simp only [List.sum_cons] at h ⊢
    have h₁ : ¬ d < t + 2 * a := by omega
    simp [addTardy, h₁, ih (t + 2 * a) w (by omega : t + 2 * a + 2 * as.sum ≤ d)]
    omega

private theorem find_on_time_prefix (d : ℕ) (as : List ℕ) (t w : ℕ) :
    ∃ early late : List ℕ, as = early ++ late ∧
      (early.sum = 0 ∨ t + 2 * early.sum ≤ d) ∧
      (as.foldl (addTardy d) (t, w)).2 = w + 2 * late.sum := by
  induction as generalizing t w with
  | nil => exact ⟨[], [], rfl, .inl rfl, by simp⟩
  | cons a as ih =>
    by_cases h : d < t + 2 * a
    · refine ⟨[], a :: as, rfl, .inl rfl, ?_⟩
      simp [addTardy, h, foldl_all_tardy d as _ _ h]
      omega
    · obtain ⟨early, late, e, hb, hc⟩ := ih (t + 2 * a) w
      refine ⟨a :: early, late, by simp [e], .inr ?_, ?_⟩
      · simp only [List.sum_cons]
        rcases hb with hb | hb <;> omega
      · simpa [addTardy, h] using hc

private theorem partitionJobs_correct (as : List ℕ) :
    WeightedTardyJobsFeasible (partitionJobs as) ↔ Partition.PartitionFeasible as := by
  constructor
  · rintro ⟨order, hp, hw⟩
    have hm : (order.map (as.getD · 0)).Perm as := by
      simpa only [partitionJobs, List.length_map, map_range_getD] using
        hp.map (as.getD · 0)
    obtain ⟨early, late, hsplit, hbound, hweight⟩ :=
      find_on_time_prefix as.sum (order.map (as.getD · 0)) 0 0
    change WeightedTardy (as.map (job as.sum)) order ≤ as.sum at hw
    rw [WeightedTardy, foldl_indices, hweight] at hw
    rw [hsplit] at hm
    obtain ⟨s, hs, hsub⟩ := List.exists_perm_sublist (List.sublist_append_left early late) hm
    have hsum := hm.sum_eq
    rw [List.sum_append] at hsum
    have hse := hs.sum_eq
    refine ⟨s, hsub, ?_⟩
    rcases hbound with hbound | hbound <;> omega
  · rintro ⟨s, hsub, hsum⟩
    rw [← map_range_getD as 0] at hsub
    obtain ⟨early, hearly, rfl⟩ := List.sublist_map_iff.mp hsub
    obtain ⟨late, hperm⟩ := hearly.exists_perm_append
    refine ⟨early ++ late, by simpa [partitionJobs] using hperm.symm, ?_⟩
    have hmap : ((early ++ late).map (as.getD · 0)).Perm as := by
      simpa only [map_range_getD] using hperm.symm.map (as.getD · 0)
    have htot := hmap.sum_eq
    rw [List.map_append, List.sum_append] at htot
    change WeightedTardy (as.map (job as.sum)) (early ++ late) ≤ as.sum
    have htime := foldl_on_time as.sum (early.map (as.getD · 0)) 0 0 (by omega)
    rw [WeightedTardy, foldl_indices, List.map_append, List.foldl_append, htime]
    have := foldl_tardy_le as.sum (late.map (as.getD · 0))
      (0 + 2 * (early.map (as.getD · 0)).sum) 0
    omega

open Turing Function TM2Program Cslib.Complexity
open Cslib.Complexity.PolynomialEncoding (splitB splitB_run copyB_run)

/-! ### Bitstring framing and stack operations -/

section BitStacks

variable {K Lab : Type} [DecidableEq K]
variable {M : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool}

private def moveBits (a b : K) (self next : Lab) : TM2.Stmt (fun _ : K => Bool) Lab Bool :=
  moveB a b some id self next

private theorem moveBits_run {a b : K} {self next : Lab}
    (hp : M self = moveBits a b self next) (hab : a ≠ b) (v : Bool) (S : K → List Bool) :
    ∃ v', Run M ((S a).length + 1) ⟨some self, v, S⟩
      ⟨some next, v', update (update S a []) b ((S a).reverse ++ S b)⟩ := by
  obtain ⟨v', T, hr, ha, hb, hk⟩ := moveB_run hp hab (S a) (S a) [] v S (by simp)
    (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  refine ⟨v', ?_⟩
  convert hr using 2
  funext k
  by_cases hka : k = a
  · subst k
    simp [ha, hab]
  by_cases hkb : k = b
  · subst k
    simpa using hb.symm
  simp [hka, hkb, hk k hka hkb]

private def readFrame (a b : K) (self next bad : Lab) :
    TM2.Stmt (fun _ : K => Bool) Lab Bool :=
  FramedCNF.Block.read a b some id self next bad

private theorem readFrame_run {a b : K} {self next bad : Lab}
    (hp : M self = readFrame a b self next bad) (hab : a ≠ b)
    (v : Bool) (S : K → List Bool) (p rest : List Bool) (h : S a = delimit p ++ rest) :
    Run M (p.length + 1) ⟨some self, v, S⟩
      ⟨some next, false, update (update S a rest) b (p.reverse ++ S b)⟩ := by
  obtain ⟨T, hr, ha, hb, hk⟩ :=
    FramedCNF.Block.run_delimit hp hab id (fun _ => rfl) p rest v S (by simpa using h)
  convert hr using 2
  funext k
  by_cases hka : k = a
  · subst k
    simp [ha, hab]
  by_cases hkb : k = b
  · subst k
    simpa using hb.symm
  simp [hka, hkb, hk k hka hkb]

private theorem readFrame_bad {a b : K} {self next bad : Lab}
    (hp : M self = readFrame a b self next bad) (hab : a ≠ b)
    (input : List Bool) (v : Bool) (S : K → List Bool) (ha : S a = input)
    (h : undelimit input = none) :
    ∃ v' T, RunLe M (input.length + 1) ⟨some self, v, S⟩ ⟨some bad, v', T⟩ ∧
      ∀ k, k ≠ a → k ≠ b → T k = S k := by
  cases input with
  | nil =>
    refine ⟨false, S, (Run.single ?_).le (by simp), fun _ _ _ => rfl⟩
    simp [hp, readFrame, FramedCNF.Block.read, TM2.stepAux, isBit, ha]
  | cons c input =>
    cases c with
    | false => simp [undelimit] at h
    | true =>
      cases input with
      | nil =>
        refine ⟨false, update S a [], (Run.single ?_).le (by simp), ?_⟩
        · simp [hp, readFrame, FramedCNF.Block.read, TM2.stepAux, isBit, bitOf, ha]
        · intro k hk _
          simp [hk]
      | cons c input =>
        let U := update (update S a input) b (c :: S b)
        have h₁ : Run M 1 ⟨some self, v, S⟩ ⟨some self, c, U⟩ := by
          apply Run.single
          simp [hp, readFrame, FramedCNF.Block.read, TM2.stepAux, isBit, bitOf,
            ha, U, hab.symm]
        obtain ⟨v', T, h₂, hk⟩ := readFrame_bad hp hab input c U
          (by simp [U, hab]) (by simpa [undelimit] using h)
        refine ⟨v', T, (h₁.le le_rfl |>.trans h₂).mono (by simp; omega), ?_⟩
        intro k hka hkb
        simp [hk k hka hkb, U, hka, hkb]
termination_by input.length
decreasing_by grind

private def splitBits (s a b : K) (self next : Lab) :
    TM2.Stmt (fun _ : K => Bool) Lab Bool :=
  splitB s a b some id id self next

private theorem splitBits_run {s a b : K} {self next : Lab}
    (hp : M self = splitBits s a b self next) (hsa : s ≠ a) (hsb : s ≠ b)
    (hab : a ≠ b) (v : Bool) (S : K → List Bool) :
    Run M ((S s).length + 1) ⟨some self, v, S⟩
      ⟨some next, false,
        update (update (update S s []) a ((S s).reverse ++ S a)) b ((S s).reverse ++ S b)⟩ := by
  obtain ⟨T, hr, hs, ha, hb, hk⟩ := splitB_run hp hsa hsb hab id (fun _ => rfl)
    (S s) [] v S (by simp [EndsBitBlock]) (by simp)
  convert hr using 2
  funext k
  by_cases hks : k = s
  · subst k
    simp [hs, hsa, hsb]
  by_cases hka : k = a
  · subst k
    simpa [hab] using ha.symm
  by_cases hkb : k = b
  · subst k
    simpa using hb.symm
  simp [hks, hka, hkb, hk k hks hka hkb]

private def writeBits (a b : K) (chunk : Bool → List Bool) (suffix : List Bool) (self next : Lab) :
    TM2.Stmt (fun _ : K => Bool) Lab Bool :=
  .peek a (fun _ v => v.isSome) <| .branch id
    (.pop a (fun _ v => v.getD false) <| .branch id
      (emit b (chunk true) self) (emit b (chunk false) self))
    (emit b suffix next)

private theorem writeBits_run {a b : K} {self next : Lab}
    {chunk : Bool → List Bool} {suffix : List Bool}
    (hp : M self = writeBits a b chunk suffix self next) (hab : a ≠ b)
    (v : Bool) (S : K → List Bool) :
    Run M ((S a).length + 1) ⟨some self, v, S⟩
      ⟨some next, false,
        update (update S a []) b (((S a).flatMap chunk ++ suffix).reverse ++ S b)⟩ := by
  generalize hx : S a = xs
  induction xs generalizing v S with
  | nil =>
    apply Run.single
    have hu : update S a [] = S := by rw [← hx, Function.update_eq_self]
    simp [hp, writeBits, TM2.stepAux, hx, hu, emit, stepAux_pushList]
  | cons bit xs ih =>
    let T := update (update S a xs) b ((chunk bit).reverse ++ S b)
    have h₁ : Run M 1 ⟨some self, v, S⟩ ⟨some self, bit, T⟩ := by
      apply Run.single
      cases bit <;> simp [hp, writeBits, TM2.stepAux, hx, T, emit, stepAux_pushList, hab.symm]
    have ht : T a = xs := by simp [T, hab]
    have h₂ := ih bit T ht
    have hr := (h₁.trans h₂).of_eq (Nat.add_comm 1 (xs.length + 1))
    convert hr using 2
    funext k
    by_cases hka : k = a
    · subst k
      simp [hab]
    by_cases hkb : k = b
    · subst k
      simp [T, List.reverse_append, List.append_assoc]
    simp [T, hka, hkb]

end BitStacks

/-! ### The polynomial-time PARTITION reduction

The existing PARTITION transducer emits the framed target followed by the
doubled entries. The machine below copies the target into each job and emits
the extra framing required by the scheduling encoding. Empty PARTITION is
handled separately from the malformed-input sentinel.
-/

namespace Reduction

open Computability Cslib.Complexity.Karp

private def liftBit (b : Bool) : List Bool := [true, b]

private def liftBits (xs : List Bool) : List Bool := xs.flatMap liftBit

private theorem delimit_eq (xs : List Bool) : delimit xs = liftBits xs ++ [false] := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [delimit, liftBits, liftBit, ih]

private theorem liftBits_append (xs ys : List Bool) :
    liftBits (xs ++ ys) = liftBits xs ++ liftBits ys := List.flatMap_append

private def lift₂ (b : Bool) : List Bool := liftBits (liftBit b)

private def lift₃ (b : Bool) : List Bool := liftBits (lift₂ b)

private theorem liftBits_flatMap {α : Type} (xs : List α) (f : α → List Bool) :
    liftBits (xs.flatMap f) = xs.flatMap (liftBits ∘ f) := by
  rw [liftBits, List.flatMap_assoc]
  rfl

private def triple (p d : List Bool) : List Bool :=
  (p.flatMap lift₃ ++ lift₂ false) ++ (d.flatMap lift₃ ++ lift₂ false) ++
    (p.flatMap lift₂ ++ liftBit false)

private theorem triple_eq (p d : List Bool) :
    triple p d = liftBits (delimit (delimit p ++ delimit d ++ p)) := by
  simp [triple, delimit_eq, liftBits, lift₂, liftBit, List.flatMap_assoc, List.append_assoc]
  rfl

private theorem length_flatMap_const {α β : Type} (xs : List α) (f : α → List β) (n : ℕ)
    (h : ∀ a, (f a).length = n) : (xs.flatMap f).length = n * xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [h, ih, Nat.mul_succ, Nat.add_comm]

private theorem triple_length (p d : List Bool) :
    (triple p d).length = 12 * p.length + 8 * d.length + 10 := by
  have h₂ (b : Bool) : (lift₂ b).length = 4 := by cases b <;> decide
  have h₃ (b : Bool) : (lift₃ b).length = 8 := by cases b <;> decide
  simp only [triple, List.length_append, length_flatMap_const _ _ _ h₂,
    length_flatMap_const _ _ _ h₃, h₂, liftBit, List.length_cons, List.length_nil]
  omega

private inductive K | input | due | tmp | part | dueCopy | weight | jobs | out
  deriving DecidableEq

private inductive Lab
  | target | moveTarget | loop | readJob | copies | copyDue | restoreDue
  | emitPart | emitDue | emitWeight | endJobs | emitBound | output | done
  deriving DecidableEq

private def prog : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool
  | .target => readFrame .input .tmp .target .moveTarget .done
  | .moveTarget => moveBits .tmp .due .moveTarget .loop
  | .loop => .peek .input (fun _ o => o.isSome) <|
      .branch id (.goto fun _ => .readJob)
        (.peek .due (fun _ o => o.isSome) <| .branch id
          (.peek .jobs (fun _ o => o.isSome) <|
            .branch id (.goto fun _ => .endJobs) (.goto fun _ => .done))
          (.goto fun _ => .endJobs))
  | .readJob => readFrame .input .tmp .readJob .copies .done
  | .copies => splitBits .tmp .part .weight .copies .copyDue
  | .copyDue => moveBits .due .tmp .copyDue .restoreDue
  | .restoreDue => splitBits .tmp .due .dueCopy .restoreDue .emitPart
  | .emitPart => writeBits .part .jobs lift₃ (lift₂ false) .emitPart .emitDue
  | .emitDue => writeBits .dueCopy .jobs lift₃ (lift₂ false) .emitDue .emitWeight
  | .emitWeight => writeBits .weight .jobs lift₂ (liftBit false) .emitWeight .loop
  | .endJobs => emit .jobs [false] .emitBound
  | .emitBound => moveBits .due .jobs .emitBound .output
  | .output => moveBits .jobs .out .output .done
  | .done => .halt


private def st (input due jobs : List Bool) : K → List Bool
  | .input => input
  | .due => due
  | .jobs => jobs
  | _ => []

private theorem round_run (p r d acc : List Bool) (v : Bool) :
    ∃ v', Run prog (4 * p.length + 3 * d.length + 8)
      ⟨some .loop, v, st (delimit p ++ r) d acc⟩
      ⟨some .loop, v', st r d ((triple p d).reverse ++ acc)⟩ := by
  let S := st (delimit p ++ r) d acc
  have h₀ : Run prog 1 ⟨some .loop, v, S⟩ ⟨some .readJob, true, S⟩ := by
    apply Run.single
    cases p <;> rfl
  have h₁ := readFrame_run (M := prog) (self := Lab.readJob)
    (a := K.input) (b := K.tmp) (next := .copies) (bad := .done) rfl
    (by decide) true S p r rfl
  let S₁ := update (update S K.input r) K.tmp (p.reverse ++ S .tmp)
  have h₂ := splitBits_run (M := prog) (self := Lab.copies) (s := K.tmp)
    (a := K.part) (b := K.weight) (next := .copyDue) rfl
    (by decide) (by decide) (by decide) false S₁
  let S₂ := update (update (update S₁ K.tmp []) K.part ((S₁ .tmp).reverse ++ S₁ .part))
    K.weight ((S₁ .tmp).reverse ++ S₁ .weight)
  obtain ⟨v₃, h₃⟩ := moveBits_run (M := prog) (self := Lab.copyDue)
    (a := K.due) (b := K.tmp) (next := .restoreDue) rfl (by decide) false S₂
  let S₃ := update (update S₂ K.due []) K.tmp ((S₂ .due).reverse ++ S₂ .tmp)
  have h₄ := splitBits_run (M := prog) (self := Lab.restoreDue) (s := K.tmp)
    (a := K.due) (b := K.dueCopy) (next := .emitPart) rfl
    (by decide) (by decide) (by decide) v₃ S₃
  let S₄ := update (update (update S₃ K.tmp []) K.due ((S₃ .tmp).reverse ++ S₃ .due))
    K.dueCopy ((S₃ .tmp).reverse ++ S₃ .dueCopy)
  have h₅ := writeBits_run (M := prog) (self := Lab.emitPart) (a := K.part)
    (b := K.jobs) (next := .emitDue) (chunk := lift₃) (suffix := lift₂ false)
    rfl (by decide) false S₄
  let S₅ := update (update S₄ K.part []) K.jobs
    (((S₄ .part).flatMap lift₃ ++ lift₂ false).reverse ++ S₄ .jobs)
  have h₆ := writeBits_run (M := prog) (self := Lab.emitDue) (a := K.dueCopy)
    (b := K.jobs) (next := .emitWeight) (chunk := lift₃) (suffix := lift₂ false)
    rfl (by decide) false S₅
  let S₆ := update (update S₅ K.dueCopy []) K.jobs
    (((S₅ .dueCopy).flatMap lift₃ ++ lift₂ false).reverse ++ S₅ .jobs)
  have h₇ := writeBits_run (M := prog) (self := Lab.emitWeight) (a := K.weight)
    (b := K.jobs) (next := .loop) (chunk := lift₂) (suffix := liftBit false)
    rfl (by decide) false S₆
  refine ⟨false, ?_⟩
  have hr := h₀.trans h₁ |>.trans h₂ |>.trans h₃ |>.trans h₄ |>.trans h₅ |>.trans h₆ |>.trans h₇
  have htime : 1 + (p.length + 1) + ((S₁ .tmp).length + 1) + ((S₂ .due).length + 1) +
      ((S₃ .tmp).length + 1) + ((S₄ .part).length + 1) + ((S₅ .dueCopy).length + 1) +
      ((S₆ .weight).length + 1) = 4 * p.length + 3 * d.length + 8 := by
    simp [S₆, S₅, S₄, S₃, S₂, S₁, S, st]
    omega
  convert hr.of_eq htime using 2
  funext k
  cases k <;> simp [st, S₆, S₅, S₄, S₃, S₂, S₁, S, triple,
    List.reverse_append, List.append_assoc]

private def finish (d acc : List Bool) (ps : List (List Bool)) : List Bool :=
  let pre := acc.reverse ++ ps.flatMap (triple · d)
  if pre = [] ∧ d ≠ [] then [] else pre ++ [false] ++ d

private theorem finish_cons (d acc p : List Bool) (ps : List (List Bool)) :
    finish d acc (p :: ps) = finish d ((triple p d).reverse ++ acc) ps := by
  simp [finish, List.reverse_append, List.append_assoc]

private theorem end_run (d acc : List Bool) (v : Bool) :
    ∃ v' S, RunLe prog (acc.length + 2 * d.length + 5)
      ⟨some .loop, v, st [] d acc⟩ ⟨some .done, v', S⟩ ∧
        S .out = finish d acc [] := by
  by_cases h : acc = [] ∧ d ≠ []
  · rcases h with ⟨rfl, hd⟩
    refine ⟨false, st [] d [], (Run.single ?_).le (by omega), by simp [st, finish, hd]⟩
    obtain ⟨b, ds, rfl⟩ := List.exists_cons_of_ne_nil hd
    rfl
  · let S := st [] d acc
    let S₁ := update S K.jobs (false :: acc)
    have h₁ : ∃ v₁, Run prog 1 ⟨some .loop, v, S⟩ ⟨some .endJobs, v₁, S⟩ := by
      cases d with
      | nil => exact ⟨false, Run.single rfl⟩
      | cons b ds =>
        cases acc with
        | nil => simp at h
        | cons c cs => exact ⟨true, Run.single rfl⟩
    obtain ⟨v₁, h₁⟩ := h₁
    have h₂ : Run prog 1 ⟨some .endJobs, v₁, S⟩ ⟨some .emitBound, v₁, S₁⟩ :=
      Run.single rfl
    obtain ⟨v₃, h₃⟩ := moveBits_run (M := prog) (self := Lab.emitBound)
      (a := K.due) (b := K.jobs) (next := .output) rfl (by decide) v₁ S₁
    let S₃ := update (update S₁ K.due []) K.jobs ((S₁ .due).reverse ++ S₁ .jobs)
    obtain ⟨v₄, h₄⟩ := moveBits_run (M := prog) (self := Lab.output)
      (a := K.jobs) (b := K.out) (next := .done) rfl (by decide) v₃ S₃
    refine ⟨v₄, _, (h₁.trans h₂ |>.trans h₃ |>.trans h₄).le ?_, ?_⟩
    · simp [S₃, S₁, S, st]
      omega
    · simp [S₃, S₁, S, st, finish, List.reverse_append, h]

private def transform (x : List Bool) : List Bool :=
  match undelimit x with
  | none => []
  | some (d, r) =>
    match undelimitBlocks r with
    | none => []
    | some ps => finish d [] ps

private theorem loop_run (d : List Bool) : ∀ (n : ℕ) (r acc : List Bool) (v : Bool),
    r.length ≤ n →
    ∃ v' S, RunLe prog (acc.length + 40 * (r.length + 1) * (d.length + 1))
      ⟨some .loop, v, st r d acc⟩ ⟨some .done, v', S⟩ ∧
        S .out = ((undelimitBlocksAux n r).map (finish d acc)).getD [] := by
  intro n
  induction n with
  | zero =>
    intro r acc v hn
    have hr : r = [] := by simpa using hn
    subst r
    obtain ⟨v', S, hr, hout⟩ := end_run d acc v
    exact ⟨v', S, hr.mono (by simp; omega), by simpa [undelimitBlocksAux] using hout⟩
  | succ n ih =>
    intro r acc v hn
    cases r with
    | nil =>
      obtain ⟨v', S, hr, hout⟩ := end_run d acc v
      exact ⟨v', S, hr.mono (by simp; omega), by simpa [undelimitBlocksAux] using hout⟩
    | cons b bs =>
      generalize hr : b :: bs = r at *
      have h₀ : Run prog 1 ⟨some .loop, v, st r d acc⟩
          ⟨some .readJob, true, st r d acc⟩ := by rw [← hr]; exact Run.single rfl
      have hAux : undelimitBlocksAux (n + 1) r =
          (undelimit r).bind fun p => (undelimitBlocksAux n p.2).map (p.1 :: ·) := by
        rw [← hr]; rfl
      cases hd : undelimit r with
      | none =>
        obtain ⟨v', S, hbad, hk⟩ := readFrame_bad (M := prog) (a := K.input) (b := K.tmp)
          (self := Lab.readJob) (next := .copies) (bad := .done) rfl (by decide) r true
          (st r d acc) rfl hd
        have hout : S .out = [] := hk .out (by decide) (by decide)
        refine ⟨v', S, (h₀.le le_rfl |>.trans hbad).mono ?_, ?_⟩
        · nlinarith
        · simp [hAux, hd, hout]
      | some pair =>
        obtain ⟨p, r'⟩ := pair
        have he := (Cslib.CookLevin.undelimit_eq_some_iff r p r').1 hd
        rw [he] at hn ⊢
        rw [he] at hAux hd
        have hlen : (delimit p ++ r').length = 2 * p.length + 1 + r'.length := by simp
        obtain ⟨v₁, h₁⟩ := round_run p r' d acc v
        obtain ⟨v₂, S, h₂, hout⟩ := ih r' ((triple p d).reverse ++ acc) v₁ (by omega)
        refine ⟨v₂, S, (h₁.le le_rfl |>.trans h₂).mono ?_, ?_⟩
        · rw [hlen]
          simp only [List.length_append, List.length_reverse, triple_length]
          nlinarith
        · rw [hout, hAux, hd]
          cases h : undelimitBlocksAux n r' <;> simp [h, finish_cons]

private theorem run (x : List Bool) :
    ∃ v S, RunLe prog (45 * (x.length + 1) ^ 2)
      ⟨some .target, false, update (fun _ => []) .input x⟩
      ⟨some .done, v, S⟩ ∧ S .out = transform x := by
  have hinit : update (fun _ => []) K.input x = st x [] [] := by
    funext k
    cases k <;> rfl
  rw [hinit]
  cases h : undelimit x with
  | none =>
    obtain ⟨v, S, hr, hk⟩ := readFrame_bad (M := prog) (a := K.input) (b := K.tmp)
      (self := Lab.target) (next := .moveTarget) (bad := .done) rfl (by decide)
      x false (st x [] []) rfl h
    refine ⟨v, S, hr.mono ?_, ?_⟩
    · nlinarith
    · simpa [transform, h, st] using hk .out (by decide) (by decide)
  | some pair =>
    obtain ⟨d, r⟩ := pair
    obtain rfl := (Cslib.CookLevin.undelimit_eq_some_iff x d r).1 h
    let S := st (delimit d ++ r) [] []
    let T := update (update S K.input r) K.tmp (d.reverse ++ S .tmp)
    have h₁ := readFrame_run (M := prog) (a := K.input) (b := K.tmp)
      (self := Lab.target) (next := .moveTarget) (bad := .done) rfl (by decide)
      false S d r rfl
    obtain ⟨v₁, h₂⟩ := moveBits_run (M := prog) (a := K.tmp) (b := K.due)
      (self := Lab.moveTarget) (next := .loop) rfl (by decide) false T
    have he : update (update T K.tmp []) K.due ((T .tmp).reverse ++ T .due) =
        st r d [] := by
      funext k
      cases k <;> simp [T, S, st]
    rw [he] at h₂
    obtain ⟨v₂, U, hr, hout⟩ := loop_run d r.length r [] v₁ le_rfl
    refine ⟨v₂, U, ((h₁.trans h₂).le le_rfl |>.trans hr).mono ?_, ?_⟩
    · simp [length_delimit, T, S, st]
      nlinarith
    · rw [hout, transform, h]
      simp only [undelimitBlocks]
      cases undelimitBlocksAux r.length r <;> rfl

private def ks : List K := [.input, .due, .tmp, .part, .dueCopy, .weight, .jobs, .out]

private noncomputable instance kFintype : Fintype K :=
  Fintype.ofList ks (fun k => by cases k <;> decide)

private noncomputable instance labFintype : Fintype Lab :=
  Fintype.ofList [.target, .moveTarget, .loop, .readJob, .copies, .copyDue, .restoreDue,
    .emitPart, .emitDue, .emitWeight, .endJobs, .emitBound, .output, .done]
    (fun l => by cases l <;> decide)

private noncomputable def comp : Host.Comp where
  K := K
  Γ := fun _ => Bool
  L := Lab
  prog := prog
  ks := ks
  ks_nodup := by decide
  mem_ks := fun k => by cases k <;> decide

private theorem transform_poly : ComplexityTheory.IsPolyTime transform :=
  Host.isPolyTime_reduction (c := comp) (cX := .input) (cO := .out)
    (gX := id) (start := .target) (done := .done) (Equiv.refl Bool)
    transform (Polynomial.C 45 * (Polynomial.X + 1) ^ 2)
    rfl fun x => by
      obtain ⟨v, S, hr, ho⟩ := run x
      refine ⟨v, S, ?_, ?_⟩
      · change RunLe prog _ ⟨some .target, false, update (fun _ => []) .input (x.map id)⟩
          ⟨some .done, v, S⟩
        rw [List.map_id]
        exact hr.mono (by simp)
      · change S .out = (transform x).map id
        rwa [List.map_id]

private theorem transform_encodeSS (as : List ℕ) (t : ℕ) (h : as ≠ [] ∨ t = 0) :
    transform (encodeSS as t) = bitEncode (as.map (fun a => (a, t, a)), t) := by
  have hs : undelimitBlocks
      (as.flatMap (fun a => delimit (encodeNat a))) = some (as.map encodeNat) := by
    simpa only [List.flatMap_def, List.map_map, Function.comp_def]
      using undelimitBlocks_flatten_delimit (as.map encodeNat)
  rw [encodeSS, transform, undelimit_delimit]
  simp only [hs]
  have encode_pair {α β : Type} [BitstringEncoding α] [BitstringEncoding β] (a : α) (b : β) :
      bitEncode (a, b) = delimit (bitEncode a) ++ bitEncode b := rfl
  have encode_list {α : Type} [BitstringEncoding α] (as : List α) :
      bitEncode as = ((as.map bitEncode).map delimit).flatten := rfl
  simp only [finish, List.reverse_nil, List.nil_append, List.flatMap_map, triple_eq,
    encode_pair, encode_list, BinaryNatEncoding.bitEncode_nat, List.map_map, Function.comp_def,
    ← List.flatMap_def, List.append_assoc]
  conv_rhs => rw [delimit_eq, liftBits_flatMap, List.append_assoc]
  have hn : ¬ ((as.flatMap fun a => liftBits (delimit (delimit (encodeNat a) ++
      (delimit (encodeNat t) ++ encodeNat a)))) = [] ∧ encodeNat t ≠ []) := by
    rintro ⟨hnil, hnonzero⟩
    rcases h with has | rfl
    · cases as with
      | nil => simp at has
      | cons a as =>
        have hn₁ := (List.append_eq_nil_iff.mp hnil).1
        rcases he : delimit (delimit (encodeNat a) ++
            (delimit (encodeNat t) ++ encodeNat a)) with _ | ⟨b, bs⟩
        · have hh := length_delimit (delimit (encodeNat a) ++
            (delimit (encodeNat t) ++ encodeNat a))
          simp [he] at hh
        · dsimp only at hn₁
          rw [he] at hn₁
          simp [liftBits, liftBit] at hn₁
    · exact hnonzero rfl
  rw [ite_eq_right hn]
  rfl

private theorem transform_noSS : transform noSS = [] := by decide

end Reduction

end Tardy


/-! ### Correctness of the composed reduction -/

open WeightedTardyJobs (WeightedTardyJobsFeasible WeightedTardy)

private theorem time_foldl (tasks : List (ℕ × ℕ × ℕ)) (S : List ℕ) :
    ∀ (ys : List ℕ) (q : ℕ × ℕ), (ys.foldl (onTimeStep tasks S) q).1 =
      q.1 + (ys.map fun j => (tasks.getD j (0, 0, 0)).1).sum
  | [], q => by simp
  | j :: ys, q => by
    rw [List.foldl_cons, time_foldl tasks S ys]
    simp only [onTimeStep, List.map_cons, List.sum_cons]
    omega

private theorem count_mono (tasks : List (ℕ × ℕ × ℕ)) (S : List ℕ) :
    ∀ (ys : List ℕ) (q : ℕ × ℕ), q.2 ≤ (ys.foldl (onTimeStep tasks S) q).2
  | [], q => le_rfl
  | j :: ys, q => by
    rw [List.foldl_cons]
    refine le_trans ?_ (count_mono tasks S ys _)
    simp only [onTimeStep]
    omega

private theorem len_job (L : List ℕ) (d j : ℕ) :
    ((L.map (Tardy.job d)).getD j (0, 0, 0)).1 = 2 * L.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[j]? <;> rfl

private theorem due_job (L : List ℕ) (d j : ℕ) (hj : j < L.length) :
    ((L.map (Tardy.job d)).getD j (0, 0, 0)).2.1 = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj, Tardy.job]

private theorem lens_eq (L : List ℕ) (d : ℕ) (ys : List ℕ) :
    (ys.map fun j => ((L.map (Tardy.job d)).getD j (0, 0, 0)).1).sum =
      2 * (ys.map (L.getD · 0)).sum := by
  induction ys with
  | nil => rfl
  | cons j ys ih =>
    rw [List.map_cons, List.sum_cons, ih, len_job, List.map_cons, List.sum_cons]
    ring

/-- A split of the positions into an early half containing position `0` and a late half
schedules every early task on time, so task `0` meets its deadline. -/
private theorem build (L E F : List ℕ) (hperm : (E ++ F).Perm (List.range L.length))
    (hE : 2 * (E.map (L.getD · 0)).sum = L.sum) (h0 : 0 ∈ E) (hL : 0 < L.length) :
    ConstrainedSequencingFeasible ((L.map (Tardy.job L.sum), L.sum), [0], 1) := by
  have hmap : ((E ++ F).map (L.getD · 0)).Perm L := by
    simpa only [Tardy.map_range_getD] using hperm.map (L.getD · 0)
  have htot := hmap.sum_eq
  rw [List.map_append, List.sum_append] at htot
  refine ⟨E ++ F, by simpa using hperm, ?_, ?_⟩
  · change WeightedTardy (L.map (Tardy.job L.sum)) (E ++ F) ≤ L.sum
    have htime := Tardy.foldl_on_time L.sum (E.map (L.getD · 0)) 0 0 (by omega)
    rw [WeightedTardy, Tardy.foldl_indices, List.map_append, List.foldl_append, htime]
    have := Tardy.foldl_tardy_le L.sum (F.map (L.getD · 0))
      (0 + 2 * (E.map (L.getD · 0)).sum) 0
    omega
  · obtain ⟨E₁, E₂, rfl⟩ := List.append_of_mem h0
    change 1 ≤ ((E₁ ++ 0 :: E₂ ++ F).foldl
      (onTimeStep (L.map (Tardy.job L.sum)) [0]) (0, 0)).2
    rw [List.append_assoc, List.foldl_append, List.cons_append, List.foldl_cons]
    set q := E₁.foldl (onTimeStep (L.map (Tardy.job L.sum)) [0]) (0, 0)
    have hq : q.1 = 2 * (E₁.map (L.getD · 0)).sum := by
      rw [time_foldl, lens_eq]
      simp
    have hE' : 2 * (E₁.map (L.getD · 0)).sum + 2 * L.getD 0 0 ≤ L.sum := by
      simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons] at hE
      omega
    have hstep : 1 ≤ (onTimeStep (L.map (Tardy.job L.sum)) [0] q 0).2 := by
      simp only [onTimeStep, len_job, due_job L L.sum 0 hL, List.mem_singleton, true_and]
      split <;> omega
    exact hstep.trans (count_mono _ _ _ _)

private theorem feasible_iff (L : List ℕ) (hL : 0 < L.length) :
    ConstrainedSequencingFeasible ((L.map (Tardy.job L.sum), L.sum), [0], 1) ↔
      PartitionFeasible L := by
  constructor
  · rintro ⟨order, hp, hw, -⟩
    exact (Tardy.partitionJobs_correct L).1 ⟨order, hp, hw⟩
  · rintro ⟨s, hsub, hsum⟩
    rw [← Tardy.map_range_getD L 0] at hsub
    obtain ⟨early, hearly, rfl⟩ := List.sublist_map_iff.mp hsub
    obtain ⟨late, hperm⟩ := hearly.exists_perm_append
    have hmap : ((early ++ late).map (L.getD · 0)).Perm L := by
      simpa only [Tardy.map_range_getD] using hperm.symm.map (L.getD · 0)
    have htot := hmap.sum_eq
    rw [List.map_append, List.sum_append] at htot
    have h0 : 0 ∈ early ++ late := hperm.subset (List.mem_range.2 hL)
    by_cases he : 0 ∈ early
    · exact build L early late hperm.symm (by omega) he hL
    · have hl : 0 ∈ late := (List.mem_append.1 h0).resolve_left he
      exact build L late early (List.perm_append_comm.trans hperm.symm) (by omega) hl hL

/-- The reduction: normalize the PARTITION sizes, go to SUBSET-SUM with the existing
PARTITION reduction, build the weighted tardy jobs instance with one job `(2a, Σ, 2a)` per size
`a` and bound `Σ`, and add `S = [0]`, `J = 1`. -/
private def reduce : List Bool → List Bool :=
  wrap ∘ Tardy.Reduction.transform ∘ Partition.reduceToSubsetSum ∘ normalize

private theorem isPolyTime_reduce : ComplexityTheory.IsPolyTime reduce :=
  ((NormMachine.isPolyTime_normalize.comp
    Partition.MembershipMachine.isPolyTime_reduceToSubsetSum).comp
      Tardy.Reduction.transform_poly).comp WrapMachine.isPolyTime_wrap

private theorem reduce_correct (x : List Bool) :
    partitionDec x = constrainedSequencingDec (reduce x) := by
  classical
  have hn : bitDecode (α := List ℕ) (normalize x) = (bitDecode (α := List ℕ) x).map
      (fun as => 1 :: 1 :: (as.filter (· ≠ 0)).map (4 * ·)) := decode_pre_strip x
  cases h : bitDecode (α := List ℕ) x with
  | none =>
    rw [h, Option.map_none] at hn
    have hr : reduce x = wrap [] := by
      simp only [reduce, Function.comp_apply, Partition.reduceToSubsetSum, hn,
        Tardy.Reduction.transform_noSS]
    rw [hr, partitionDec, h]
    rfl
  | some as =>
    rw [h, Option.map_some] at hn
    set L := 1 :: 1 :: (as.filter (· ≠ 0)).map (4 * ·) with hLdef
    have hr : reduce x = bitEncode (((L.map (Tardy.job L.sum), L.sum), [0], 1) :
        ConstrainedSequencingInstance) := by
      simp only [reduce, Function.comp_apply, Partition.reduceToSubsetSum, hn]
      rw [Tardy.Reduction.transform_encodeSS _ _ (Or.inl (by simp [L]))]
      have hj : (L.map (· * 2)).map (fun a => (a, L.sum, a)) = L.map (Tardy.job L.sum) := by
        simp [Tardy.job, List.map_map, Function.comp_def, Nat.mul_comm]
      rw [hj]
      rfl
    have hlen : 0 < L.length := by simp [L]
    have hsum : 0 < L.sum := by simp [L]
    have hw : WellFormed ((L.map (Tardy.job L.sum), L.sum), [0], 1) := by
      refine ⟨?_, hsum, by simpa using hlen, Nat.one_pos⟩
      intro t ht
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 ht
      have hpos : 0 < a := by
        simp only [L, List.mem_cons, List.mem_map, List.mem_filter] at ha
        rcases ha with rfl | rfl | ⟨b, ⟨-, hb⟩, rfl⟩
        · decide
        · decide
        · have : b ≠ 0 := by simpa using hb
          omega
      simp only [Tardy.job]
      omega
    rw [hr, constrainedSequencingDec, bitDecode_bitEncode, partitionDec, h]
    simp only [decide_eq_decide]
    rw [← partition_filter, ← partition_pad, ← feasible_iff L hlen]
    exact ⟨fun hf => ⟨hw, hf⟩, fun hf => hf.2⟩

/-- **CONSTRAINED SEQUENCING TO MINIMIZE TARDY TASK WEIGHT is NP-hard.** -/
theorem constrainedSequencing_npHard : ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
    L ∈ MetaMathlibExt.ComplexityTheory.NP →
      Cslib.CookLevin.PolyManyOneRed L constrainedSequencingDec :=
  Cslib.Complexity.NPHard.of_polyManyOneRed Partition.partition_npComplete.2
    ⟨reduce, isPolyTime_reduce, reduce_correct⟩


end MetaMathlibExt.Complexity.NPComplete.ConstrainedSequencingToMinimizeTardyTaskWeight
