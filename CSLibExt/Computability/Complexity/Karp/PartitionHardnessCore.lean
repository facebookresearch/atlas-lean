/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Host
public import CSLibExt.Computability.Complexity.Karp.PartitionSizes
public import CSLibExt.Computability.Complexity.SSVerifierSum

/-!
# The SUBSET-SUM to PARTITION padding machine

On a canonical source `encodeSS as t`, preserve the numbers, sum them
with the existing verifier, and prepend the blocks for `2*t` and `as.sum`.
Malformed-input rejection is supplied by the outer normalization wrapper.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Partition.HardnessCore

open Turing Function TM2Program TM2Embedding BitstringEncoding Computability
open Cslib.Complexity.Karp Cslib.Complexity.SatVerifier

/-- **Stacks of the SUBSET-SUM to PARTITION padding machine.**
Input, reverse buffer, target, output, and unchanged sum-machine stacks. -/
inductive K | X | R | T | O | sum (k : SSVerify.K)
  deriving DecidableEq

@[reducible] def Γ : K → Type
  | .sum _ => Sym
  | _ => Bool

/-- **Control labels of the SUBSET-SUM to PARTITION padding machine.**
Parse target, preserve numbers, sum, then emit the two padding blocks. -/
inductive Lab
  | target | copy | distribute | sum (l : SSVerify.Lab)
  | targetStart | targetBits | prefix | bits | done
  deriving DecidableEq

/-- **Summation-machine stack embedding in the padding machine.**
The original sum component's stacks are not reimplemented. -/
def sumEmb : SEmb (fun _ : SSVerify.K => Sym) Γ where
  e := K.sum
  inj _ _ h := K.sum.inj h
  ι _ := Equiv.refl _

/-- **Label map from summation halts to target emission.**
Both genuine sum-machine halts resume at target emission. -/
def sumLabel : SSVerify.Lab → Lab
  | .yes | .no => .targetStart
  | l => .sum l

/-- **Program of the SUBSET-SUM to PARTITION padding machine.**
Padding construction by binary stack operations. -/
def prog : Lab → TM2.Stmt Γ Lab Bool
  | .target =>
    .pop .X (fun _ o => o.getD false) <| .branch id
      (.pop .X (fun _ o => o.getD false) <| .push .T id <|
        .goto fun _ => .target)
      (.goto fun _ => .copy)
  | .copy => moveB .X .R some id .copy .distribute
  | .distribute =>
    .peek .R (fun _ o => o.isNone) <| .branch id
      (.goto fun _ => .sum .next)
      (.pop .R (fun _ o => o.getD false) <|
        .push (.sum .X) Sym.bit <| .push .O id <|
        .push (.sum .W) (fun _ => .bit true) <|
        .goto fun _ => .distribute)
  | .sum l => mapS sumEmb sumLabel (SSVerify.prog l)
  | .targetStart =>
    .push .O (fun _ => false) <| .peek .T (fun _ o => o.isNone) <|
      .branch id (.goto fun _ => .prefix) (.goto fun _ => .targetBits)
  | .targetBits =>
    .peek .T (fun _ o => o.isNone) <| .branch id
      (.push .O (fun _ => false) <| .push .O (fun _ => true) <|
        .goto fun _ => .prefix)
      (.pop .T (fun _ o => o.getD false) <|
        .push .O id <| .push .O (fun _ => true) <|
        .goto fun _ => .targetBits)
  | .prefix => .push .O (fun _ => false) <| .goto fun _ => .bits
  | .bits =>
    .peek (.sum .B) (fun _ o => o.isNone) <| .branch id
      (.goto fun _ => .done)
      (.pop (.sum .B) (fun _ o => bitOf Sym.bit? o) <|
        .push .O id <| .push .O (fun _ => true) <| .goto fun _ => .bits)
  | .done => .halt

/-- **Padding machine embeds the summation machine.**
The host changes only the two original halting continuations. -/
theorem embeds_sum : Embeds sumEmb sumLabel SSVerify.prog prog := by
  intro l
  cases l <;> simp [sumLabel, prog, SSVerify.prog]

private theorem target_run (p : List Bool) :
    ∀ (rest : List Bool) (v : Bool) (S : ∀ k, List (Γ k)),
      S .X = delimit p ++ rest →
      ∃ S', Run prog (p.length + 1)
        ⟨some .target, v, S⟩ ⟨some .copy, false, S'⟩ ∧
        S' .X = rest ∧ S' .T = p.reverse ++ S .T ∧
        ∀ k, k ≠ .X → k ≠ .T → S' k = S k := by
  induction p with
  | nil =>
    intro rest v S hX
    refine ⟨update S .X rest, Run.single ?_, by simp, by simp, ?_⟩
    · simp [prog, TM2.stepAux, delimit, hX]
    · intro k hx _
      simp [hx]
  | cons b p ih =>
    intro rest v S hX
    let S₁ := update (update S .X (delimit p ++ rest)) .T (b :: S .T)
    obtain ⟨S', hr, hx, ht, hf⟩ := ih rest b S₁ (by simp [S₁])
    refine ⟨S', Run.head ?_ hr, hx, ?_, ?_⟩
    · cases b <;> simp [TM2.step, prog, TM2.stepAux, hX, delimit, S₁]
    · simpa [S₁, List.reverse_cons, List.append_assoc] using ht
    · intro k hkX hkT
      simpa [S₁, hkX, hkT] using hf k hkX hkT

private def prepared (x r t sx o w : List Bool) : ∀ k, List (Γ k)
  | .X => x | .R => r | .T => t | .O => o
  | .sum .X => sx.map Sym.bit
  | .sum .W => w.map Sym.bit
  | .sum _ => []

private theorem distribute_step (b : Bool) (r t sx o w : List Bool)
    (v : Bool) :
    TM2.step prog ⟨some .distribute, v, prepared [] (b :: r) t sx o w⟩ =
      some ⟨some .distribute, b,
        prepared [] r t (b :: sx) (b :: o) (true :: w)⟩ := by
  simp only [TM2.step, prog, TM2.stepAux, prepared,
    List.head?_cons, Option.isNone_some, id_eq, Bool.cond_false,
    Option.getD_some, List.tail_cons]
  congr 2
  funext k
  cases k with
  | X => rfl
  | R => rfl
  | T => rfl
  | O => rfl
  | sum k => cases k <;> rfl

private theorem distribute_run (r : List Bool) :
    ∀ (t sx o w : List Bool) (v : Bool),
      Run prog (r.length + 1)
        ⟨some .distribute, v, prepared [] r t sx o w⟩
        ⟨some (.sum .next), true, prepared [] [] t (r.reverse ++ sx)
          (r.reverse ++ o) (List.replicate r.length true ++ w)⟩ := by
  induction r with
  | nil =>
    intro t sx o w v
    exact Run.single (by simp [prog, TM2.stepAux, prepared])
  | cons b r ih =>
    intro t sx o w v
    have h := Run.head (distribute_step b r t sx o w v)
      (ih t (b :: sx) (b :: o) (true :: w) b)
    simpa only [List.length_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.replicate_add, List.replicate_one] using h

private theorem copy_run (r t : List Bool) (v : Bool) :
    Run prog (2 * r.length + 2)
      ⟨some .copy, v, prepared r [] t [] [] []⟩
      ⟨some (.sum .next), true,
        prepared [] [] t r r (List.replicate r.length true)⟩ := by
  obtain ⟨v', S, hr, hx, hR, hk⟩ := moveB_run
    (M := prog) (a := K.X) (b := K.R) (self := .copy)
    (next := .distribute) (d := some) (g := id) rfl (by decide)
    r r [] v (prepared r [] t [] [] [])
    (by simp [prepared]) (by simp [IsBitBlock])
    (by simp [EndsBitBlock])
  have hs : S = prepared [] r.reverse t [] [] [] := by
    funext k
    cases k with
    | X => exact hx
    | R => simpa [prepared] using hR
    | T => exact hk .T (by decide) (by decide)
    | O => exact hk .O (by decide) (by decide)
    | sum k =>
      have h := hk (.sum k) (by simp) (by simp)
      cases k <;> simpa [prepared] using h
  rw [hs] at hr
  have hd := distribute_run r.reverse t [] [] [] v'
  simp only [List.reverse_reverse, List.length_reverse,
    List.append_nil] at hd
  exact (hr.trans hd).of_eq (by omega)

private theorem target_bits_run (p : List Bool) :
    ∀ (v : Bool) (S : ∀ k, List (Γ k)), S .T = p →
      ∃ v' S', Run prog (p.length + 1)
        ⟨some .targetBits, v, S⟩ ⟨some .prefix, v', S'⟩ ∧
        S' .O = true :: false ::
          ((p.reverse.flatMap fun b => [true, b]) ++ S .O) ∧
        S' (.sum .B) = S (.sum .B) := by
  induction p with
  | nil =>
    intro v S hT
    refine ⟨true, update S .O (true :: false :: S .O),
      Run.single ?_, by simp, by simp⟩
    simp [prog, TM2.stepAux, hT]
  | cons b p ih =>
    intro v S hT
    let S₁ := update (update S .T p) .O (true :: b :: S .O)
    obtain ⟨v', S', hr, ho, hb⟩ := ih b S₁ (by simp [S₁])
    refine ⟨v', S', Run.head ?_ hr, ?_, ?_⟩
    · cases b <;> simp [TM2.step, prog, TM2.stepAux, hT, S₁]
    · simpa [S₁, List.reverse_cons, List.flatMap_append,
        List.append_assoc] using ho
    · simpa [S₁] using hb

private theorem delimit_payload (p : List Bool) :
    delimit p = (p.flatMap fun b => [true, b]) ++ [false] := by
  induction p with
  | nil => rfl
  | cons b p ih => simp [delimit, ih]

private theorem target_prefix_run (t : ℕ) (v : Bool)
    (S : ∀ k, List (Γ k)) (hT : S .T = (encodeNat t).reverse) :
    ∃ v' S', RunLe prog ((encodeNat t).length + 2)
      ⟨some .targetStart, v, S⟩ ⟨some .prefix, v', S'⟩ ∧
      S' .O = delimit (encodeNat (2 * t)) ++ S .O ∧
      S' (.sum .B) = S (.sum .B) := by
  by_cases ht : t = 0
  · subst t
    change S .T = [] at hT
    refine ⟨true, update S .O (false :: S .O),
      (Run.single ?_).le (by decide), rfl, by simp⟩
    simp [prog, TM2.stepAux, hT]
  · have hn : (encodeNat t).reverse ≠ [] := by
      intro h
      have he := decode_encodeNat t
      rw [List.reverse_eq_nil_iff.mp h] at he
      exact ht he.symm
    let S₁ := update S .O (false :: S .O)
    obtain ⟨v', S', hr, ho, hb⟩ := target_bits_run
      (encodeNat t).reverse false S₁ (by simp [S₁, hT])
    have hp : (S .T).head?.isNone = false := by
      rw [hT]
      cases h : (encodeNat t).reverse <;> simp_all
    refine ⟨v', S', (Run.head ?_ hr).le (by simp), ?_, ?_⟩
    · simp [TM2.step, prog, TM2.stepAux, S₁, hp]
    · have he : encodeNat (2 * t) = false :: encodeNat t := by
        rw [TM2Recursive.encodeNat_eq_cons (by omega : 2 * t ≠ 0)]
        simp [Nat.mul_comm]
      rw [ho, he, delimit, delimit_payload]
      simp [S₁, List.append_assoc]
    · simpa [S₁] using hb

private theorem bits_run (bs : List Bool) :
    ∀ (v : Bool) (S : ∀ k, List (Γ k)),
      S (.sum .B) = bs.map Sym.bit →
      ∃ v' S', Run prog (bs.length + 1)
        ⟨some .bits, v, S⟩ ⟨some .done, v', S'⟩ ∧
        S' .O = (bs.reverse.flatMap fun b => [true, b]) ++ S .O := by
  induction bs with
  | nil =>
    intro v S hB
    exact ⟨true, S, Run.single (by simp [prog, TM2.stepAux, hB]), rfl⟩
  | cons b bs ih =>
    intro v S hB
    let S₁ := update (update S (.sum .B) (bs.map Sym.bit))
      .O (true :: b :: S .O)
    obtain ⟨v', S', hr, ho⟩ := ih b S₁ (by simp [S₁])
    refine ⟨v', S', Run.head ?_ hr, ?_⟩
    · cases b <;>
        simp [TM2.step, prog, TM2.stepAux, hB, bitOf, Sym.bit?, S₁]
    · simpa [S₁, List.reverse_cons, List.flatMap_append,
        List.append_assoc] using ho

private theorem prefix_run (bs : List Bool) (v : Bool)
    (S : ∀ k, List (Γ k)) (hB : S (.sum .B) = bs.map Sym.bit) :
    ∃ v' S', Run prog (bs.length + 2)
      ⟨some .prefix, v, S⟩ ⟨some .done, v', S'⟩ ∧
      S' .O = delimit bs.reverse ++ S .O := by
  obtain ⟨v', S', hr, ho⟩ := bits_run bs v
    (update S .O (false :: S .O)) (by simp [hB])
  refine ⟨v', S', Run.head (by simp [TM2.step, prog, TM2.stepAux]) hr, ?_⟩
  rw [ho, update_self, delimit_payload, List.append_assoc]
  rfl

private theorem sum_ready (as : List ℕ) (t : ℕ) :
    let r := as.flatMap fun a => delimit (encodeNat a)
    ∃ v S, RunLe prog
      (r.length * (2 * r.length + 9) + (encodeNat t).length + 6)
      ⟨some .target, false, update (fun _ => []) .X (encodeSS as t)⟩
      ⟨some .targetStart, v, S⟩ ∧
      S (.sum .B) = ((encodeNat as.sum).map Sym.bit).reverse ∧
      S .T = (encodeNat t).reverse ∧ S .O = r := by
  intro r
  obtain ⟨S₀, h₀, hx, ht, hf⟩ := target_run (encodeNat t) r false
    (update (fun _ => []) .X (encodeSS as t)) (by simp [encodeSS, r])
  have hs₀ : S₀ = prepared r [] (encodeNat t).reverse [] [] [] := by
    funext k
    cases k with
    | X => exact hx
    | T => simpa [prepared] using ht
    | R => exact hf .R (by decide) (by decide)
    | O => exact hf .O (by decide) (by decide)
    | sum k =>
      have h := hf (.sum k) (by simp) (by simp)
      cases k <;> simpa [prepared] using h
  rw [hs₀] at h₀
  have h₁ := copy_run r (encodeNat t).reverse false
  obtain ⟨v, w, S, h₂, ha, hf₂⟩ := Cslib.Complexity.SSVerifierSum.sum_embed
    sumEmb sumLabel prog embeds_sum rfl as (List.replicate r.length true)
    true (prepared [] [] (encodeNat t).reverse r r
      (List.replicate r.length true)) (by
      intro k
      change prepared [] [] (encodeNat t).reverse r r
        (List.replicate r.length true) (.sum k) =
        (SSVerify.st (r.map Sym.bit)
          ((List.replicate r.length true).map Sym.bit) [] [] [] k).map id
      rw [List.map_id]
      cases k <;> rfl)
  rw [Cslib.Complexity.SSVerifierSum.pick_all as r.length
    (SSVerify.length_le_flatMap as)] at ha
  refine ⟨v, S, ((h₀.trans h₁).le le_rfl |>.trans h₂).mono ?_, ?_, ?_, ?_⟩
  · nlinarith
  · have h := ha SSVerify.K.B
    change S (.sum .B) = (((encodeNat as.sum).map Sym.bit).reverse).map id at h
    simpa only [List.map_id] using h
  · exact hf₂ .T (fun k => by simp [sumEmb])
  · exact hf₂ .O (fun k => by simp [sumEmb])

/-- **Quadratic run of the padding machine on canonical instances.**
The subtraction-free padding map is computed by a quadratic binary
machine on every canonical SUBSET-SUM instance, including `t > as.sum`. -/
theorem run (as : List ℕ) (t : ℕ) :
    ∃ v S, RunLe prog (20 * ((encodeSS as t).length + 1) ^ 2)
      ⟨some .target, false, update (fun _ => []) .X (encodeSS as t)⟩
      ⟨some .done, v, S⟩ ∧ S .O = bitEncode (fromSubsetSum as t) := by
  let r := as.flatMap fun a => delimit (encodeNat a)
  obtain ⟨v₁, S₁, h₁, hb₁, ht₁, ho₁⟩ := sum_ready as t
  obtain ⟨v₂, S₂, h₂, ho₂, hb₂⟩ := target_prefix_run t v₁ S₁ ht₁
  obtain ⟨v₃, S₃, h₃, ho₃⟩ := prefix_run (encodeNat as.sum).reverse v₂ S₂
    (by rw [hb₂, hb₁, List.map_reverse])
  have he (l : List ℕ) :
      bitEncode l = l.flatMap (fun a => delimit (encodeNat a)) := by
    change ((l.map encodeNat).map delimit).flatten = _
    simp only [List.map_map, List.flatMap_def, Function.comp_def]
  have hlen := sum_encoding_length_le as
  rw [he] at hlen
  refine ⟨v₃, S₃, ((h₁.trans h₂).trans (h₃.le le_rfl)).mono ?_, ?_⟩
  · simp only [encodeSS, List.length_append, length_delimit,
      List.length_reverse]
    nlinarith [Nat.zero_le (r.length ^ 2),
      Nat.zero_le ((encodeNat t).length ^ 2)]
  · rw [ho₃, List.reverse_reverse, ho₂, ho₁, he, fromSubsetSum]
    simp only [List.flatMap_cons]

instance : Fintype K := Fintype.ofList
  [.X, .R, .T, .O, .sum .X, .sum .W, .sum .T, .sum .A,
    .sum .B, .sum .P, .sum .Q] (by
    intro k
    cases k with
    | X => decide
    | R => decide
    | T => decide
    | O => decide
    | sum k => cases k <;> decide)

noncomputable instance : Fintype Lab := Fintype.ofList
  ([.target, .copy, .distribute, .targetStart, .targetBits,
    .prefix, .bits, .done] ++ Finset.univ.toList.map Lab.sum)
  (by intro l; cases l <;> simp)

/-- **SUBSET-SUM to PARTITION padding machine as a host component.**
Finite padding component for the strict source-decoding wrapper. -/
noncomputable abbrev comp : Cslib.Complexity.Host.Comp where
  K := K
  Γ := Γ
  finΓ k := by cases k <;> infer_instance
  L := Lab
  prog := prog
  ks := Finset.univ.toList
  ks_nodup := Finset.nodup_toList _
  mem_ks k := by simp

end MetaMathlibExt.Complexity.NPComplete.Partition.HardnessCore
