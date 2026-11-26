/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.PolynomialEncoding.PairSplit

/-! # Read one edge and one witness bit from the exact normalized input streams -/

@[expose] public section

namespace Cslib.Complexity.DensestKSubgraph.Internal.MarkedCursor

open Turing Function MetaMathlibExt TM2Program TM2Embedding BitstringEncoding
open Cslib.Complexity.PolynomialEncoding
open Computability (encodeNat)

/- Each endpoint stream uses a separate splitter workspace. -/
inductive K | split (right : Bool) (k : PairSplit.K) | mask
  deriving DecidableEq

instance : Fintype K where
  elems := {K.mask} ∪ Finset.univ.image (K.split false) ∪ Finset.univ.image (K.split true)
  complete k := by cases k with | split b k => cases b <;> simp | mask => simp

/- The mark survives decoding in the finite control. -/
inductive Lab | next | split (right chosen : Bool) (l : PairSplit.Lab)
  | item (chosen : Bool) | finish | bad
  deriving DecidableEq

instance : Fintype Lab where
  elems := {Lab.next, .item false, .item true, .finish, .bad} ∪ Finset.univ.image
    (fun p : Bool × Bool × PairSplit.Lab => .split p.1 p.2.1 p.2.2)
  complete l := by cases l with | item b => cases b <;> simp | _ => simp

/- Both splitters work on Boolean storage. -/
def emb (right : Bool) : SEmb (fun _ : PairSplit.K => Bool) (fun _ : K => Bool) where
  e := K.split right
  inj _ _ h := K.split.inj h |>.2
  ι _ := Equiv.refl _

/- Only after both fields are read is an edge returned. -/
def redirect (right chosen : Bool) : PairSplit.Lab → Lab
  | .good => if right then .item chosen else .split true chosen .read
  | .bad => .bad
  | l => .split right chosen l

/- Check that the witness and the graph advance together. -/
def prog : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool
  | .next => .peek (.split false .input) (fun _ o => o.isSome) <| .branch id
      (.peek .mask (fun _ o => o.isSome) <| .branch id
        (.pop .mask (fun _ o => o.getD false) <| .goto fun b => .split false b .read)
        (.goto fun _ => .bad))
      (.peek .mask (fun _ o => o.isSome) <| .branch id
        (.goto fun _ => .bad) (.goto fun _ => .finish))
  | .split r b l => mapS (emb r) (redirect r b) (PairSplit.prog l)
  | .item _ | .finish | .bad => .halt

private theorem embeds (r b : Bool) : Embeds (emb r) (redirect r b) PairSplit.prog prog := by
  intro l
  cases l with
  | read | copy => exact Or.inl rfl
  | good | bad => exact Or.inr rfl

/- Raw column payloads, current endpoint outputs, and the mask suffix. -/
def st (u v a b w : List Bool) : K → List Bool
  | .mask => w
  | .split false k => PairSplit.st u a [] k
  | .split true k => PairSplit.st v b [] k

private theorem run_split (r b : Bool) (p x y a z w : List Bool) (s : Bool) :
    ∃ t, Run prog (2 * p.length + 2)
      ⟨some (.split r b .read), s,
        if r then st y (delimit p ++ x) z a w else st (delimit p ++ x) y a z w⟩
      ⟨some (redirect r b .good), t,
        if r then st y x z (p ++ a) w else st x y (p ++ a) z w⟩ := by
  let S := if r then st y (delimit p ++ x) z a w else st (delimit p ++ x) y a z w
  obtain ⟨t, hr⟩ := PairSplit.run_delimit p x a s
  obtain ⟨T, hrun, ha, hf⟩ := run_embed (redirect r b) (embeds r b) _
    (some PairSplit.Lab.read) s _ PairSplit.Lab.good t _ S hr (by
      intro k
      cases r <;> exact (List.map_id _).symm)
  have he : T = (if r then st y x z (p ++ a) w else st x y (p ++ a) z w) := by
    funext k
    cases k with
    | mask => cases r <;> exact hf K.mask (by intro l; simp [emb])
    | split u l =>
      have h := (ha l).trans (List.map_id _)
      cases r <;> cases u <;> first | exact h | exact hf _ (by intro j; simp [emb])
  exact ⟨t, he ▸ hrun⟩

/- One nonempty cursor step returns two normalized endpoint words and the selected flag. -/
theorem run_cons (e : ℕ × ℕ) (es : List (ℕ × ℕ)) (b : Bool) (w : List Bool) (v : Bool) :
    ∃ t, Run prog (2 * (e.1.size + e.2.size) + 5)
      ⟨some .next, v, st (bitEncode ((e :: es).map Prod.fst))
        (bitEncode ((e :: es).map Prod.snd)) [] [] (b :: w)⟩
      ⟨some (.item b), t, st (bitEncode (es.map Prod.fst)) (bitEncode (es.map Prod.snd))
        (encodeNat e.1) (encodeNat e.2) w⟩ := by
  let u := bitEncode (es.map Prod.fst)
  let z := bitEncode (es.map Prod.snd)
  let p := encodeNat e.1
  let q := encodeNat e.2
  let A := delimit p ++ u
  let B := delimit q ++ z
  have he : update (st A B [] [] (b :: w)) K.mask w = st A B [] [] w := by
    funext k
    cases k with
    | mask => exact update_self ..
    | split r j => cases r <;> rfl
  have hA : A ≠ [] := by
    dsimp only [A]
    cases p <;> simp [delimit]
  have hr : Run prog 1 ⟨some .next, v, st A B [] [] (b :: w)⟩
      ⟨some (.split false b .read), b, st A B [] [] w⟩ := by
    apply Run.single
    simp [prog, TM2.stepAux, st, PairSplit.st, hA, he]
  obtain ⟨s, h₁⟩ := run_split false b p u B [] [] w b
  obtain ⟨t, h₂⟩ := run_split true b q z u [] p w s
  have h₁' : Run prog (2 * p.length + 2) ⟨some (.split false b .read), b, st A B [] [] w⟩
      ⟨some (.split true b .read), s, st u B p [] w⟩ := by
    simpa [redirect, A] using h₁
  change Run prog (2 * q.length + 2) _ ⟨some (.item b), t, st u z p (q ++ []) w⟩ at h₂
  have h₂' : Run prog (2 * q.length + 2) ⟨some (.split true b .read), s, st u B p [] w⟩
      ⟨some (.item b), t, st u z p q w⟩ := by simpa [B] using h₂
  refine ⟨t, ((hr.trans h₁').trans h₂').of_eq ?_⟩
  simp only [p, q, BinaryNatEncoding.length_encodeNat]
  omega

/- Empty edge and mask streams finish without constructing any vertices. -/
theorem run_empty (v : Bool) :
    Run prog 1 ⟨some .next, v, st [] [] [] [] []⟩ ⟨some .finish, false, st [] [] [] [] []⟩ :=
  Run.single rfl

/- An extra mark is rejected. -/
theorem run_extra (b : Bool) (w : List Bool) (v : Bool) :
    Run prog 1 ⟨some .next, v, st [] [] [] [] (b :: w)⟩
      ⟨some .bad, true, st [] [] [] [] (b :: w)⟩ := Run.single rfl

/- A missing mark at a nonempty left column is rejected. -/
theorem run_missing (b : Bool) (u z : List Bool) (v : Bool) :
    Run prog 1 ⟨some .next, v, st (b :: u) z [] [] []⟩
      ⟨some .bad, false, st (b :: u) z [] [] []⟩ := Run.single rfl

end Cslib.Complexity.DensestKSubgraph.Internal.MarkedCursor
