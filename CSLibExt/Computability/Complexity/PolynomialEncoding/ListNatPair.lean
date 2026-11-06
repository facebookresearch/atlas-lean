/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.PolynomialEncoding.NatPair
public import CSLibExt.Computability.Complexity.PolynomialEncoding.Frame
import CSLibExt.Computability.Complexity.PolynomialEncoding.ListParts
import CSLibExt.Computability.Complexity.PolynomialEncoding.ListNat
import CSLibExt.Computability.CookLevin

/-!
# Canonical projection of lists of binary Nat pairs

KNAPSACK needs separate framed weight and value streams from its raw item
list. Each outer frame is decoded by the concrete Nat-pair component;
noncanonical Nat payloads are normalized, while malformed pair frames fail.
-/

@[expose] public section

namespace Cslib.Complexity.PolynomialEncoding.ListNatPair

open Turing Function MetaMathlibExt.BitstringEncoding
open MetaMathlibExt.TM2Program MetaMathlibExt.TM2Embedding

private theorem blocks_projection_length_le (bs : List (List Bool))
    (as : List (Nat × Nat))
    (h : bitDecode (bs.map delimit).flatten = some as) :
    (bitEncode (as.map Prod.fst)).length +
      (bitEncode (as.map Prod.snd)).length ≤
        4 * ((bs.map delimit).flatten).length := by
  induction bs generalizing as with
  | nil =>
    change some [] = some as at h
    obtain rfl := Option.some.inj h.symm
    rfl
  | cons p bs ih =>
    change bitDecode (delimit p ++ (bs.map delimit).flatten) = some as at h
    rw [decode_list_delimit] at h
    obtain ⟨⟨m, n⟩, hp, hs⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨as, ht, rfl⟩ := Option.map_eq_some_iff.mp hs
    have hb := ih as ht
    have hn := NatPair.decoded_payload_length_le hp
    change (delimit (Computability.encodeNat m) ++
        bitEncode (as.map Prod.fst)).length +
      (delimit (Computability.encodeNat n) ++
        bitEncode (as.map Prod.snd)).length ≤ _
    simp only [List.map_cons, List.flatten_cons, List.length_append,
      length_delimit] at hb ⊢
    omega

/-- **Projected pair lists total at most four times the input length.**
Both projected canonical lists together are bounded by four times
the original raw list length, including noncanonical input payloads. -/
theorem projection_length_le {x : List Bool} {as : List (Nat × Nat)}
    (h : bitDecode x = some as) :
    (bitEncode (as.map Prod.fst)).length +
      (bitEncode (as.map Prod.snd)).length ≤ 4 * x.length := by
  have hp := h
  change (undelimitBlocks x).bind (List.mapM bitDecode) = some as at hp
  obtain ⟨bs, hb, _⟩ := Option.bind_eq_some_iff.mp hp
  rw [blocks_decode_sound hb] at h ⊢
  exact blocks_projection_length_le bs as h

/-- **Stacks of the pair-list projector.**
Raw outer input, two reversed accumulators, two outputs, and the
existing Nat-pair component's workspace. -/
inductive K | input | acc (right : Bool) | output (right : Bool)
  | pair (k : NatPair.K)
  deriving DecidableEq

instance : Fintype K where
  elems := {K.input, .acc false, .acc true, .output false, .output true} ∪
    Finset.univ.image K.pair
  complete k := by
    cases k with
    | input => simp
    | acc b | output b => cases b <;> simp
    | pair k => simp

/-- **Control labels of the pair-list projector.**
Read one outer frame, normalize its pair, emit both fields, repeat. -/
inductive Lab | loop | block | back | pair (l : NatPair.Lab)
  | emit (right : Bool) | finish (right : Bool) | good | bad
  deriving DecidableEq

instance : Fintype Lab where
  elems := {Lab.loop, .block, .back, .emit false, .emit true,
    .finish false, .finish true, .good, .bad} ∪ Finset.univ.image Lab.pair
  complete l := by
    cases l with
    | loop | block | back | good | bad => simp
    | emit b | finish b => cases b <;> simp
    | pair l => simp

/-- **Stack embedding of the pair normalizer in the pair-list projector.**
The Nat-pair component is embedded without changing its alphabets. -/
def pairEmb : SEmb (fun _ : NatPair.K => Bool) (fun _ : K => Bool) where
  e := K.pair
  inj _ _ h := K.pair.inj h
  ι _ := Equiv.refl Bool

/-- **Pair-normalizer halt redirection in the pair-list projector.**
Only the pair component's actual halts are redirected. -/
def pairLabel : NatPair.Lab → Lab
  | .good => .emit false
  | .bad => .bad
  | l => .pair l

/-- **Program of the pair-list projector.**
Concrete outer parsing, pair normalization, and two framed streams. -/
def prog : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool
  | .loop => .peek .input (fun _ o => o.isSome) <| .branch id
      (.goto fun _ => .block) (.goto fun _ => .finish false)
  | .block => FramedCNF.Block.read .input (.pair (.pair .scratch))
      some id .block .back .bad
  | .back => moveB (.pair (.pair .scratch)) (.pair (.pair .input))
      some id .back (.pair (.pair .read))
  | .pair l => mapS pairEmb pairLabel (NatPair.prog l)
  | .emit right => emitFrame
      (if right then .pair .right else .pair .left) (.acc right)
      some id (.emit right) (if right then .loop else .emit true)
  | .finish right => moveB (.acc right) (.output right) some id
      (.finish right) (if right then .good else .finish true)
  | .good | .bad => .halt

/-- **Eleven-stack invariant of the pair-list projector.**
The exact eleven-stack invariant, with caller output suffixes. -/
def st (input aw av ow ov : List Bool) (P : NatPair.K → List Bool) :
    K → List Bool
  | .input => input
  | .acc right => if right then av else aw
  | .output right => if right then ov else ow
  | .pair k => P k

private theorem read_pair_run (p r aw av ow ov : List Bool) (v : Bool) :
    ∃ w, Run prog (2 * p.length + 3)
      ⟨some .loop, v, st (delimit p ++ r) aw av ow ov
        (NatPair.st [] [] [] [] [] [])⟩
      ⟨some (.pair (.pair .read)), w,
        st r aw av ow ov (NatPair.st p [] [] [] [] [])⟩ := by
  let S := st (delimit p ++ r) aw av ow ov (NatPair.st [] [] [] [] [] [])
  have first : Run prog 1 ⟨some .loop, v, S⟩ ⟨some .block, true, S⟩ := by
    apply Run.single
    cases p <;> simp [prog, TM2.stepAux, S, st, delimit]
  obtain ⟨S₁, hr₁, hi, hs, hf₁⟩ := FramedCNF.Block.run_delimit
    (M := prog) (a := K.input) (b := .pair (.pair .scratch))
    (d := some) (g := id) (self := Lab.block) (good := Lab.back)
    (bad := Lab.bad) rfl (by decide) id (fun _ => rfl) p r true S
    (by simp [S, st])
  have hz : S₁ (.pair (.pair .input)) = [] := by
    simpa [S, st, NatPair.st] using
      hf₁ (.pair (.pair .input)) (by decide) (by decide)
  obtain ⟨w, S₂, hr₂, ht, hp, hf₂⟩ := moveB_run
    (M := prog) (a := K.pair (.pair .scratch)) (b := .pair (.pair .input))
    (d := some) (g := id) (self := Lab.back) (next := .pair (.pair .read))
    rfl (by decide) p.reverse p.reverse [] false S₁
    (by simpa [S, st, NatPair.st] using hs) (by simp [IsBitBlock]) rfl
  have other (k : K) (hki : k ≠ .input)
      (hks : k ≠ .pair (.pair .scratch)) (hkp : k ≠ .pair (.pair .input)) :
      S₂ k = S k := (hf₂ k hks hkp).trans (hf₁ k hki hks)
  have he : S₂ = st r aw av ow ov (NatPair.st p [] [] [] [] []) := by
    funext k
    cases k with
    | input => exact (hf₂ .input (by decide) (by decide)).trans hi
    | acc b | output b => exact other _ (by simp) (by simp) (by simp)
    | pair k =>
      cases k with
      | pair k =>
        cases k with
        | input => simpa [st, NatPair.st, hz] using hp
        | scratch => exact ht
        | left => exact other _ (by decide) (by decide) (by decide)
      | buffer | left | right =>
        exact other _ (by decide) (by decide) (by decide)
  refine ⟨w, ?_⟩
  rw [he] at hr₂
  exact ((first.trans hr₁).trans hr₂).of_eq (by simp; omega)

private theorem embeds_pair : Embeds pairEmb pairLabel NatPair.prog prog := by
  intro l
  cases l with
  | pair l | norm b l => exact Or.inl rfl
  | good | bad => exact Or.inr rfl

private theorem normalize_pair_run {p : List Bool} {m n : Nat}
    (h : bitDecode p = some (m, n)) (r aw av ow ov : List Bool) (v : Bool) :
    ∃ w, RunLe prog (2 * p.length + 6)
      ⟨some (.pair (.pair .read)), v,
        st r aw av ow ov (NatPair.st p [] [] [] [] [])⟩
      ⟨some (.emit false), w, st r aw av ow ov
        (NatPair.st [] [] [] [] (Computability.encodeNat m)
          (Computability.encodeNat n))⟩ := by
  obtain ⟨w, hr⟩ := NatPair.run_some h [] [] v
  have ha : Agree pairEmb (NatPair.st p [] [] [] [] [])
      (st r aw av ow ov (NatPair.st p [] [] [] [] [])) := by
    intro k
    simp [pairEmb, st]
  obtain ⟨V, hv, he, hf⟩ := runLe_embed pairLabel embeds_pair hr ha
  have hV : V = st r aw av ow ov
      (NatPair.st [] [] [] [] (Computability.encodeNat m)
        (Computability.encodeNat n)) := by
    funext k
    cases k with
    | input | acc b | output b =>
      exact hf _ (by intro j; simp [pairEmb])
    | pair k => simpa [st, pairEmb] using he k
  refine ⟨w, ?_⟩
  rw [hV] at hv
  simpa [pairLabel] using hv

private theorem emit_pair_run (left right r aw av ow ov : List Bool)
    (v : Bool) :
    Run prog (left.length + right.length + 2)
      ⟨some (.emit false), v, st r aw av ow ov
        (NatPair.st [] [] [] [] left right)⟩
      ⟨some .loop, false,
        st r ((delimit left).reverse ++ aw) ((delimit right).reverse ++ av)
          ow ov (NatPair.st [] [] [] [] [] [])⟩ := by
  let S := st r aw av ow ov (NatPair.st [] [] [] [] left right)
  obtain ⟨S₁, hr₁, hl, haw, hf₁⟩ := emitFrame_run
    (M := prog) (a := K.pair .left) (b := .acc false) (d := some)
    (g := id) (self := Lab.emit false) (next := .emit true)
    rfl (by decide) id (fun _ => rfl) left [] v S rfl
    (by simp [S, st, NatPair.st])
  have hright : S₁ (.pair .right) = right :=
    hf₁ _ (by decide) (by decide)
  have hav : S₁ (.acc true) = av := hf₁ _ (by decide) (by decide)
  obtain ⟨S₂, hr₂, hr, hav₂, hf₂⟩ := emitFrame_run
    (M := prog) (a := K.pair .right) (b := .acc true) (d := some)
    (g := id) (self := Lab.emit true) (next := Lab.loop)
    rfl (by decide) id (fun _ => rfl) right [] false S₁ rfl
    (by simpa using hright)
  have other (k : K) (hl : k ≠ .pair .left) (ha : k ≠ .acc false)
      (hr : k ≠ .pair .right) (hb : k ≠ .acc true) : S₂ k = S k :=
    (hf₂ k hr hb).trans (hf₁ k hl ha)
  have he : S₂ = st r ((delimit left).reverse ++ aw)
      ((delimit right).reverse ++ av) ow ov (NatPair.st [] [] [] [] [] []) := by
    funext k
    cases k with
    | input | output b => exact other _ (by simp) (by simp) (by simp) (by simp)
    | acc b =>
      cases b with
      | false =>
        simpa [S, st] using (hf₂ (.acc false) (by decide) (by decide)).trans haw
      | true => simpa [st, hav] using hav₂
    | pair k =>
      cases k with
      | left => exact (hf₂ (.pair .left) (by decide) (by decide)).trans hl
      | right => exact hr
      | pair k =>
        cases k <;>
          exact other _ (by decide) (by decide) (by decide) (by decide)
      | buffer => exact other _ (by decide) (by decide) (by decide) (by decide)
  rw [he] at hr₂
  exact (hr₁.trans hr₂).of_eq (by omega)

/-- **Pair-list projector emits one weight and one value frame per item.**
One successfully decoded item contributes one canonical weight
frame and one canonical value frame, with pair scratch emptied again. -/
theorem element_run {p : List Bool} {m n : Nat}
    (h : bitDecode p = some (m, n)) (r aw av ow ov : List Bool) (v : Bool) :
    RunLe prog (12 * (delimit p).length)
      ⟨some .loop, v, st (delimit p ++ r) aw av ow ov
        (NatPair.st [] [] [] [] [] [])⟩
      ⟨some .loop, false,
        st r ((delimit (Computability.encodeNat m)).reverse ++ aw)
          ((delimit (Computability.encodeNat n)).reverse ++ av) ow ov
          (NatPair.st [] [] [] [] [] [])⟩ := by
  obtain ⟨w, hr₁⟩ := read_pair_run p r aw av ow ov v
  obtain ⟨z, hr₂⟩ := normalize_pair_run h r aw av ow ov w
  have hr₃ := emit_pair_run (Computability.encodeNat m)
    (Computability.encodeNat n) r aw av ow ov z
  have hn := NatPair.decoded_payload_length_le h
  exact (((hr₁.le le_rfl).trans hr₂).trans (hr₃.le le_rfl)).mono
    (by simp only [length_delimit]; omega)

/-- **Pair-list projector main loop emits both lists in reverse.**
The main loop emits both lists in reverse, ready for the two
final stack reversals. Order and multiplicity follow the decoded input. -/
theorem blocks_run (bs : List (List Bool)) (as : List (Nat × Nat))
    (h : bitDecode (bs.map delimit).flatten = some as)
    (aw av ow ov : List Bool) (v : Bool) :
    RunLe prog (12 * ((bs.map delimit).flatten).length + 1)
      ⟨some .loop, v, st (bs.map delimit).flatten aw av ow ov
        (NatPair.st [] [] [] [] [] [])⟩
      ⟨some (.finish false), false,
        st [] ((bitEncode (as.map Prod.fst)).reverse ++ aw)
          ((bitEncode (as.map Prod.snd)).reverse ++ av) ow ov
          (NatPair.st [] [] [] [] [] [])⟩ := by
  induction bs generalizing as aw av v with
  | nil =>
    change some [] = some as at h
    obtain rfl := Option.some.inj h.symm
    have he : bitEncode ([] : List Nat) = [] := rfl
    exact (Run.single (by simp [prog, TM2.stepAux, st, he])).le le_rfl
  | cons p bs ih =>
    change bitDecode (delimit p ++ (bs.map delimit).flatten) = some as at h
    rw [decode_list_delimit] at h
    obtain ⟨⟨m, n⟩, hp, hs⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨as, ht, rfl⟩ := Option.map_eq_some_iff.mp hs
    have tail := ih (as := as)
      (aw := (delimit (Computability.encodeNat m)).reverse ++ aw)
      (av := (delimit (Computability.encodeNat n)).reverse ++ av)
      (v := false) ht
    have hr :=
      (element_run hp (bs.map delimit).flatten aw av ow ov v).trans tail
    have hf : bitEncode (((m, n) :: as).map Prod.fst) =
        delimit (Computability.encodeNat m) ++
          bitEncode (as.map Prod.fst) := rfl
    have hv : bitEncode (((m, n) :: as).map Prod.snd) =
        delimit (Computability.encodeNat n) ++
          bitEncode (as.map Prod.snd) := rfl
    have htime : 12 * (delimit p).length +
        (12 * ((bs.map delimit).flatten).length + 1) ≤
        12 * ((((p :: bs).map delimit).flatten).length) + 1 := by
      simp only [List.map_cons, List.flatten_cons, List.length_append]
      omega
    rw [hf, hv, List.reverse_append, List.reverse_append]
    simpa only [List.append_assoc, List.map_cons, List.flatten_cons]
      using hr.mono htime

private theorem finish_run (weights values ow ov : List Bool) (v : Bool) :
    ∃ w, Run prog (weights.length + values.length + 2)
      ⟨some (.finish false), v, st [] weights.reverse values.reverse ow ov
        (NatPair.st [] [] [] [] [] [])⟩
      ⟨some .good, w, st [] [] [] (weights ++ ow) (values ++ ov)
        (NatPair.st [] [] [] [] [] [])⟩ := by
  let S := st [] weights.reverse values.reverse ow ov
    (NatPair.st [] [] [] [] [] [])
  obtain ⟨v₁, S₁, hr₁, ha, ho, hf₁⟩ := moveB_run
    (M := prog) (a := K.acc false) (b := .output false) (d := some)
    (g := id) (self := Lab.finish false) (next := .finish true)
    rfl (by decide) weights.reverse weights.reverse [] v S
    (by simp [S, st]) (by simp [IsBitBlock]) rfl
  have hav : S₁ (.acc true) = values.reverse := hf₁ _ (by decide) (by decide)
  have hov : S₁ (.output true) = ov := hf₁ _ (by decide) (by decide)
  obtain ⟨v₂, S₂, hr₂, ha₂, ho₂, hf₂⟩ := moveB_run
    (M := prog) (a := K.acc true) (b := .output true) (d := some)
    (g := id) (self := Lab.finish true) (next := Lab.good)
    rfl (by decide) values.reverse values.reverse [] v₁ S₁
    (by simpa using hav) (by simp [IsBitBlock]) rfl
  have other (k : K) (ha : k ≠ .acc false) (ho : k ≠ .output false)
      (hb : k ≠ .acc true) (hp : k ≠ .output true) : S₂ k = S k :=
    (hf₂ k hb hp).trans (hf₁ k ha ho)
  have he : S₂ = st [] [] [] (weights ++ ow) (values ++ ov)
      (NatPair.st [] [] [] [] [] []) := by
    funext k
    cases k with
    | input | pair k => exact other _ (by simp) (by simp) (by simp) (by simp)
    | acc b =>
      cases b with
      | false => exact (hf₂ (.acc false) (by decide) (by decide)).trans ha
      | true => exact ha₂
    | output b =>
      cases b with
      | false =>
        simpa [S, st] using
          (hf₂ (.output false) (by decide) (by decide)).trans ho
      | true => simpa [st, hov] using ho₂
  refine ⟨v₂, ?_⟩
  rw [he] at hr₂
  exact (hr₁.trans hr₂).of_eq (by simp; omega)

/-- **Pair-list projector yields canonical weight and value lists.**
Successful generic decoding yields the canonical weight and value
lists on separate stacks. All input and scratch stacks are emptied. -/
theorem run_some {x : List Bool} {as : List (Nat × Nat)}
    (h : bitDecode x = some as) (ow ov : List Bool) (v : Bool) :
    ∃ w, RunLe prog (16 * x.length + 3)
      ⟨some .loop, v, st x [] [] ow ov (NatPair.st [] [] [] [] [] [])⟩
      ⟨some .good, w, st [] [] [] (bitEncode (as.map Prod.fst) ++ ow)
        (bitEncode (as.map Prod.snd) ++ ov)
        (NatPair.st [] [] [] [] [] [])⟩ := by
  have hp := h
  change (undelimitBlocks x).bind (List.mapM bitDecode) = some as at hp
  obtain ⟨bs, hb, _⟩ := Option.bind_eq_some_iff.mp hp
  have hx := blocks_decode_sound hb
  have hbs : bitDecode (bs.map delimit).flatten = some as := by
    simpa only [hx] using h
  have hr₁ := blocks_run bs as hbs [] [] ow ov v
  rw [← hx] at hr₁
  simp only [List.append_nil] at hr₁
  obtain ⟨w, hr₂⟩ := finish_run (bitEncode (as.map Prod.fst))
    (bitEncode (as.map Prod.snd)) ow ov false
  have hs := projection_length_le h
  exact ⟨w, (hr₁.trans (hr₂.le le_rfl)).mono (by omega)⟩

private theorem bad_pair_run {p : List Bool}
    (h : bitDecode (α := Nat × Nat) p = none)
    (r aw av ow ov : List Bool) (v : Bool) :
    ∃ w S, RunLe prog (3 * p.length + 4)
      ⟨some .loop, v, st (delimit p ++ r) aw av ow ov
        (NatPair.st [] [] [] [] [] [])⟩ ⟨some .bad, w, S⟩ := by
  obtain ⟨w, first⟩ := read_pair_run p r aw av ow ov v
  obtain ⟨z, S, hr⟩ := NatPair.run_none h [] [] w
  have ha : Agree pairEmb (NatPair.st p [] [] [] [] [])
      (st r aw av ow ov (NatPair.st p [] [] [] [] [])) := by
    intro k
    simp [pairEmb, st]
  obtain ⟨T, ht, _, _⟩ := runLe_embed pairLabel embeds_pair hr ha
  have last : RunLe prog (p.length + 1)
      ⟨some (.pair (.pair .read)), w,
        st r aw av ow ov (NatPair.st p [] [] [] [] [])⟩
      ⟨some .bad, z, T⟩ := ht
  exact ⟨z, T, ((first.le le_rfl).trans last).mono (by omega)⟩

private theorem run_none_aux (fuel : Nat) :
    ∀ (x aw av ow ov : List Bool) (v : Bool), x.length ≤ fuel →
    bitDecode (α := List (Nat × Nat)) x = none →
    ∃ w S, RunLe prog (12 * x.length + 2)
      ⟨some .loop, v, st x aw av ow ov (NatPair.st [] [] [] [] [] [])⟩
      ⟨some .bad, w, S⟩ := by
  induction fuel with
  | zero =>
    intro x aw av ow ov v hx hn
    have he : x = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst x
    contradiction
  | succ fuel ih =>
    intro x aw av ow ov v hx hn
    cases x with
    | nil => contradiction
    | cons b xs =>
      cases hu : undelimit (b :: xs) with
      | none =>
        let S := st (b :: xs) aw av ow ov (NatPair.st [] [] [] [] [] [])
        have first : Run prog 1 ⟨some .loop, v, S⟩
            ⟨some .block, true, S⟩ :=
          Run.single (by simp [prog, TM2.stepAux, S, st])
        obtain ⟨w, T, hr⟩ := FramedCNF.Block.run_none (M := prog)
          (a := K.input) (b := .pair (.pair .scratch)) (d := some) (g := id)
          (self := Lab.block) (good := Lab.back) (bad := Lab.bad)
          rfl (by decide) id (fun _ => rfl) (b :: xs) true S
          (by simp [S, st]) hu
        exact ⟨w, T, ((first.le le_rfl).trans hr).mono (by simp; omega)⟩
      | some pr =>
        obtain ⟨p, r⟩ := pr
        have he := (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp hu
        have hlen := congrArg List.length he
        simp only [List.length_cons, List.length_append,
          length_delimit] at hlen hx
        rw [he, decode_list_delimit] at hn
        cases hp : bitDecode (α := Nat × Nat) p with
        | none =>
          obtain ⟨w, S, hr⟩ := bad_pair_run hp r aw av ow ov v
          rw [he]
          refine ⟨w, S, hr.mono ?_⟩
          simp only [List.length_append, length_delimit]
          omega
        | some mn =>
          obtain ⟨m, n⟩ := mn
          have ht : bitDecode (α := List (Nat × Nat)) r = none := by
            simpa [hp] using hn
          obtain ⟨w, S, rest⟩ := ih r
            ((delimit (Computability.encodeNat m)).reverse ++ aw)
            ((delimit (Computability.encodeNat n)).reverse ++ av)
            ow ov false (by omega) ht
          rw [he]
          exact ⟨w, S, ((element_run hp r aw av ow ov v).trans rest).mono
            (by simp only [List.length_append]; omega)⟩

/-- **Pair-list projector fails on malformed input in linear time.**
Malformed outer framing or any malformed pair reaches `bad` in
linear time. Failed workspaces may contain partial data and need clearing. -/
theorem run_none {x : List Bool}
    (h : bitDecode (α := List (Nat × Nat)) x = none)
    (aw av ow ov : List Bool) (v : Bool) :
    ∃ w S, RunLe prog (12 * x.length + 2)
      ⟨some .loop, v, st x aw av ow ov (NatPair.st [] [] [] [] [] [])⟩
      ⟨some .bad, w, S⟩ :=
  run_none_aux x.length x aw av ow ov v le_rfl h

/-- **Pair-list projector as a host component.**
The concrete eleven-stack projector uses the existing Host model. -/
abbrev component : Host.Comp where
  K := K
  Γ := fun _ => Bool
  L := Lab
  prog := prog
  ks := [.input, .acc false, .acc true, .output false, .output true,
    .pair (.pair .input), .pair (.pair .left), .pair (.pair .scratch),
    .pair .buffer, .pair .left, .pair .right]
  ks_nodup := by decide
  mem_ks k := by
    cases k with
    | input => decide
    | acc b | output b => cases b <;> decide
    | pair k =>
      cases k with
      | pair k => cases k <;> decide
      | buffer | left | right => decide

/-- **Pair-list projector always terminates at the decoding outcome.**
Total decoder outcome. Success projects canonical lists with empty
scratch; failure promises termination, not reusable workspace contents. -/
theorem run (x : List Bool) (v : Bool) :
    ∃ w S, RunLe prog (16 * x.length + 3)
      ⟨some .loop, v, st x [] [] [] [] (NatPair.st [] [] [] [] [] [])⟩
      ⟨some (if (bitDecode (α := List (Nat × Nat)) x).isSome
        then .good else .bad), w, S⟩ ∧
      ∀ as : List (Nat × Nat), bitDecode x = some as →
        S = st [] [] [] (bitEncode (as.map Prod.fst))
          (bitEncode (as.map Prod.snd)) (NatPair.st [] [] [] [] [] []) := by
  cases h : bitDecode (α := List (Nat × Nat)) x with
  | none =>
    obtain ⟨w, S, hr⟩ := run_none h [] [] [] [] v
    refine ⟨w, S, hr.mono (by omega), ?_⟩
    intro as ha
    simp at ha
  | some as =>
    obtain ⟨w, hr⟩ := run_some h [] [] v
    refine ⟨w, st [] [] [] (bitEncode (as.map Prod.fst))
      (bitEncode (as.map Prod.snd)) (NatPair.st [] [] [] [] [] []),
      by simpa using hr, ?_⟩
    intro bs hb
    obtain rfl := Option.some.inj hb
    rfl

/-- **Embedded pair-list projector preserves outside stacks.**
Any stack embedding preserves the external frame on both outcomes.
Only mapped-label reachability is promised: callers establish their own
continuation-label separation. Failed private workspace needs clearing. -/
theorem run_embedded {J L : Type} [DecidableEq J] {Γ : J → Type}
    (E : SEmb (fun _ : K => Bool) Γ) (φ : Lab → L)
    {M : L → TM2.Stmt Γ L Bool} (hm : Embeds E φ prog M)
    (x : List Bool) (v : Bool) (S : ∀ j, List (Γ j))
    (hs : Agree E (st x [] [] [] [] (NatPair.st [] [] [] [] [] [])) S) :
    ∃ w T, RunLe M (16 * x.length + 3)
      ⟨some (φ .loop), v, S⟩
      ⟨some (φ (if (bitDecode (α := List (Nat × Nat)) x).isSome
        then .good else .bad)), w, T⟩ ∧ Frame E S T ∧
      ∀ as : List (Nat × Nat), bitDecode x = some as →
        Agree E (st [] [] [] (bitEncode (as.map Prod.fst))
          (bitEncode (as.map Prod.snd)) (NatPair.st [] [] [] [] [] [])) T := by
  obtain ⟨w, U, hr, hu⟩ := run x v
  obtain ⟨T, ht, ha, hf⟩ := runLe_embed φ hm hr hs
  refine ⟨w, T, ht, hf, ?_⟩
  intro as h
  rw [hu as h] at ha
  exact ha

end Cslib.Complexity.PolynomialEncoding.ListNatPair
