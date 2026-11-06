/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.FramedCNF.Block
public import CSLibExt.Computability.Complexity.PolynomialEncoding.Bounds
public import CSLibExt.Computability.Complexity.Host
import CSLibExt.Computability.CookLevin

/-!
# Raw projection of the canonical pair frame

The first field of a canonical pair is delimiter-framed; the rest of the
input is the second field. This finite component extracts both raw fields
without changing or interpreting their payloads. Concrete callers compose
Nat and ListNat normalization and validation afterward.
-/

@[expose] public section

namespace Cslib.Complexity.PolynomialEncoding.PairSplit

open Turing Function MetaMathlibExt.TM2Program
open MetaMathlibExt.BitstringEncoding FramedCNF

/-- **Stacks of the raw pair-frame splitter.**
The original input becomes the second field; `left` holds the first. -/
inductive K | input | left | scratch
  deriving DecidableEq

instance : Fintype K where
  elems := ⟨↑[K.input, .left, .scratch], by decide⟩
  complete k := by cases k <;> decide

/-- **Control labels of the raw pair-frame splitter.**
Read one frame, restore its order, then report success or failure. -/
inductive Lab | read | copy | good | bad
  deriving DecidableEq

instance : Fintype Lab where
  elems := ⟨↑[Lab.read, .copy, .good, .bad], by decide⟩
  complete l := by cases l <;> decide

/-- **Program of the raw pair-frame splitter.**
Pair framing is split using the existing delimiter and move kernels. -/
def prog : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool
  | .read => Block.read .input .scratch some id .read .copy .bad
  | .copy => moveB .scratch .left some id .copy .good
  | .good | .bad => .halt

/-- **Stack layout of the raw pair-frame splitter.**
Explicit stack layout of the projection invariant. -/
def st (input left scratch : List Bool) : K → List Bool
  | .input => input
  | .left => left
  | .scratch => scratch

/-- **Pair-frame splitter extracts both raw fields.**
Extract both raw fields, restore first-field order, and clear
scratch in exactly two steps per first-field bit plus two. -/
theorem run_delimit (p r out : List Bool) (v : Bool) :
    ∃ v', Run prog (2 * p.length + 2)
      ⟨some .read, v, st (delimit p ++ r) out []⟩
      ⟨some .good, v', st r (p ++ out) []⟩ := by
  obtain ⟨S, hr, hi, hs, hk⟩ := Block.run_delimit
    (M := prog) (a := K.input) (b := K.scratch)
    (d := some) (g := id) (self := Lab.read) (good := Lab.copy)
    (bad := Lab.bad) rfl (by decide) id (fun _ => rfl) p r v
    (st (delimit p ++ r) out []) (by simp [st])
  have he : S = st r out p.reverse := by
    funext k
    cases k with
    | input => exact hi
    | left => exact hk K.left (by decide) (by decide)
    | scratch => simpa [st] using hs
  rw [he] at hr
  obtain ⟨v', T, hc, ht, hl, hj⟩ := moveB_run
    (M := prog) (a := K.scratch) (b := K.left)
    (d := some) (g := id) (self := Lab.copy) (next := Lab.good)
    rfl (by decide) p.reverse p.reverse [] false (st r out p.reverse)
    (by simp [st]) rfl rfl
  have hf : T = st r (p ++ out) [] := by
    funext k
    cases k with
    | input => exact hj K.input (by decide) (by decide)
    | left => simpa [st] using hl
    | scratch => exact ht
  refine ⟨v', ?_⟩
  rw [hf] at hc
  exact (hr.trans hc).of_eq (by simp; omega)

/-- **Pair-frame splitter projects every well-framed input in linear time.**
Every successful raw pair frame is projected within input length
plus one; its two payloads are left unnormalized. -/
theorem run_some {x p r : List Bool}
    (h : undelimit x = some (p, r)) (out : List Bool) (v : Bool) :
    ∃ v', RunLe prog (x.length + 1)
      ⟨some .read, v, st x out []⟩
      ⟨some .good, v', st r (p ++ out) []⟩ := by
  rw [(Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp h]
  obtain ⟨v', hr⟩ := run_delimit p r out v
  refine ⟨v', hr.le ?_⟩
  simp only [List.length_append, length_delimit]
  omega

/-- **Pair-frame splitter fails on malformed first-field framing.**
Malformed first-field framing reaches the actual failure label.
Scratch may contain a partial field and must be cleared before reuse. -/
theorem run_none {x : List Bool} (h : undelimit x = none)
    (out : List Bool) (v : Bool) :
    ∃ v' S, RunLe prog (x.length + 1)
      ⟨some .read, v, st x out []⟩ ⟨some .bad, v', S⟩ := by
  exact Block.run_none (M := prog) (a := K.input) (b := K.scratch)
    (d := some) (g := id) (self := Lab.read) (good := Lab.copy)
    (bad := Lab.bad) rfl (by decide) id (fun _ => rfl) x v
    (st x out []) (by simp [st]) h

/-- **Raw pair-frame splitter as a host component.**
The finite component interface used by fixed nested-codec callers. -/
abbrev component : Host.Comp where
  K := K
  Γ := fun _ => Bool
  L := Lab
  prog := prog
  ks := [.input, .left, .scratch]
  ks_nodup := by decide
  mem_ks k := by cases k <;> decide

/-- **Raw field projection agrees with the pair decoder.**
Raw field projection agrees with the existing pair decoder. This
is not a runtime assumption or implementation of either element codec. -/
theorem run_decoded {α β : Type}
    [MetaMathlibExt.BitstringEncoding α] [MetaMathlibExt.BitstringEncoding β]
    {x : List Bool} {a : α} {b : β} (h : bitDecode x = some (a, b))
    (v : Bool) :
    ∃ p r v', RunLe prog (x.length + 1)
      ⟨some .read, v, st x [] []⟩ ⟨some .good, v', st r p []⟩ ∧
      bitDecode p = some a ∧ bitDecode r = some b := by
  obtain ⟨p, r, hx, hp, hr⟩ := decoded_pair_parts h
  obtain ⟨v', run⟩ := run_some
    ((Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mpr hx) [] v
  exact ⟨p, r, v', by simpa using run, hp, hr⟩

/-- **Pair-frame splitter reaches the framing outcome.**
Total framing outcome, without prematurely accepting either field
as a value of its eventual element type. -/
theorem run (x : List Bool) (v : Bool) :
    ∃ v' S, RunLe prog (x.length + 1)
      ⟨some .read, v, st x [] []⟩
      ⟨some (if (undelimit x).isSome then .good else .bad), v', S⟩ ∧
      ∀ p r, undelimit x = some (p, r) → S = st r p [] := by
  cases h : undelimit x with
  | none =>
    obtain ⟨v', S, hr⟩ := run_none h [] v
    refine ⟨v', S, hr, ?_⟩
    intro p r hp
    simp at hp
  | some pr =>
    obtain ⟨p, r⟩ := pr
    obtain ⟨v', hr⟩ := run_some h [] v
    refine ⟨v', st r p [], by simpa using hr, ?_⟩
    intro p' r' hh
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh)
    rfl

/-- **Embedded pair-frame splitter preserves caller stacks.**
Embedded projection preserves all caller stacks outside the
three-stack workspace, even when framing fails. -/
theorem run_embedded {J L : Type} [DecidableEq J] {Γ : J → Type}
    (E : MetaMathlibExt.TM2Embedding.SEmb (fun _ : K => Bool) Γ)
    (φ : Lab → L) {M : L → TM2.Stmt Γ L Bool}
    (hm : MetaMathlibExt.TM2Embedding.Embeds E φ prog M)
    (x : List Bool) (v : Bool) (S : ∀ j, List (Γ j))
    (hs : MetaMathlibExt.TM2Embedding.Agree E (st x [] []) S) :
    ∃ v' T, RunLe M (x.length + 1)
      ⟨some (φ .read), v, S⟩
      ⟨some (φ (if (undelimit x).isSome then .good else .bad)), v', T⟩ ∧
      MetaMathlibExt.TM2Embedding.Frame E S T ∧
      ∀ p r, undelimit x = some (p, r) →
        MetaMathlibExt.TM2Embedding.Agree E (st r p []) T := by
  obtain ⟨v', U, hr, hu⟩ := run x v
  obtain ⟨T, ht, ha, hf⟩ := MetaMathlibExt.TM2Embedding.runLe_embed φ hm hr hs
  refine ⟨v', T, ht, hf, ?_⟩
  intro p r h
  rw [hu p r h] at ha
  exact ha

end Cslib.Complexity.PolynomialEncoding.PairSplit
