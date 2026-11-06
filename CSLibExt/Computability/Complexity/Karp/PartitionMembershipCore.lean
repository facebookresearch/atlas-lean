/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.PartitionDouble
public import CSLibExt.Computability.Complexity.Karp.PartitionSizes
public import CSLibExt.Computability.Complexity.SSVerifierSum

/-!
# PARTITION membership transducer on canonical number streams

Sum with the existing SUBSET-SUM machine, double the saved stream, and
prepend the sum as the target. The input-normalization layer is separate.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Partition.MembershipCore

open Turing Function TM2Program TM2Embedding
open Cslib.Complexity.Karp Cslib.Complexity.SatVerifier

/-- **Stacks of the canonical PARTITION membership transducer.**
Input, reversal buffer, and the two embedded components' stacks. -/
inductive K | X | R | sum (k : SSVerify.K) | double (k : DoubleStream.K)
  deriving DecidableEq

/-- **Stack alphabets of the canonical PARTITION membership transducer.**
The summation stacks use the existing verifier alphabet. -/
@[reducible] def Γ : K → Type
  | .sum _ => Sym
  | _ => Bool

/-- **Control labels of the canonical PARTITION membership transducer.**
Component phases and the final sum-prefix emitter. -/
inductive Lab
  | copy | distribute | sum (l : SSVerify.Lab)
  | double (l : DoubleStream.Lab) | prefix | bits | done
  deriving DecidableEq

/-- **Summation-machine stack embedding in the membership transducer.**
Stack embedding of the existing sum component. -/
def sumEmb : SEmb (fun _ : SSVerify.K => Sym) Γ where
  e := K.sum
  inj _ _ h := K.sum.inj h
  ι _ := Equiv.refl _

/-- **Doubling-machine stack embedding in the membership transducer.**
Stack embedding of the doubling component. -/
def doubleEmb : SEmb (fun _ : DoubleStream.K => Bool) Γ where
  e := K.double
  inj _ _ h := K.double.inj h
  ι _ := Equiv.refl _

/-- **Label map from summation halts to the doubling pass.**
Both sum halts resume at the doubling pass. -/
def sumLabel : SSVerify.Lab → Lab
  | .yes | .no => .double (.scan .start)
  | l => .sum l

/-- **Label map from the doubling halt to the prefix emitter.**
The doubling halt resumes at the prefix emitter. -/
def doubleLabel : DoubleStream.Lab → Lab
  | .done => .prefix
  | l => .double l

/-- **Program of the canonical PARTITION membership transducer.**
Copy, sum, double, and prepend the sum, using finite-stack operations. -/
def prog : Lab → TM2.Stmt Γ Lab Bool
  | .copy => moveB .X .R some id .copy .distribute
  | .distribute =>
    .peek .R (fun _ o => o.isNone) <| .branch id
      (.goto fun _ => .sum .next)
      (.pop .R (fun _ o => o.getD false) <|
        .push (.sum .X) Sym.bit <| .push (.double .X) id <|
        .push (.sum .W) (fun _ => .bit true) <|
        .goto fun _ => .distribute)
  | .sum l => mapS sumEmb sumLabel (SSVerify.prog l)
  | .double l => mapS doubleEmb doubleLabel (DoubleStream.prog l)
  | .prefix =>
    .push (.double .O) (fun _ => false) <| .goto fun _ => .bits
  | .bits =>
    .peek (.sum .B) (fun _ o => o.isNone) <| .branch id
      (.goto fun _ => .done)
      (.pop (.sum .B) (fun _ o => bitOf Sym.bit? o) <|
        .push (.double .O) id <| .push (.double .O) (fun _ => true) <|
        .goto fun _ => .bits)
  | .done => .halt

/-- **Membership transducer embeds the summation machine.**
Only genuine halts are replaced when embedding the sum machine. -/
theorem embeds_sum : Embeds sumEmb sumLabel SSVerify.prog prog := by
  intro l
  cases l <;> simp [sumLabel, prog, SSVerify.prog]

/-- **Membership transducer embeds the doubling machine.**
Only the doubling halt is replaced by the prefix-emitter continuation. -/
theorem embeds_double :
    Embeds doubleEmb doubleLabel DoubleStream.prog prog := by
  intro l
  cases l <;> simp [doubleLabel, prog, DoubleStream.prog]

private def prepared (r sx dx w : List Bool) : ∀ k, List (Γ k)
  | .R => r
  | .sum .X => sx.map Sym.bit
  | .sum .W => w.map Sym.bit
  | .double .X => dx
  | .X | .sum _ | .double _ => []

private theorem distribute_step (b : Bool) (r sx dx w : List Bool)
    (v : Bool) :
    TM2.step prog ⟨some .distribute, v, prepared (b :: r) sx dx w⟩ =
      some ⟨some .distribute, b,
        prepared r (b :: sx) (b :: dx) (true :: w)⟩ := by
  simp only [TM2.step, prog, TM2.stepAux, prepared,
    List.head?_cons, Option.isNone_some, id_eq, Bool.cond_false,
    Option.getD_some, List.tail_cons]
  congr 2
  funext k
  cases k with
  | X => rfl
  | R => rfl
  | sum k => cases k <;> rfl
  | double k => cases k <;> rfl

private theorem distribute_run (r : List Bool) :
    ∀ (sx dx w : List Bool) (v : Bool),
      Run prog (r.length + 1) ⟨some .distribute, v, prepared r sx dx w⟩
        ⟨some (.sum .next), true, prepared [] (r.reverse ++ sx)
          (r.reverse ++ dx) (List.replicate r.length true ++ w)⟩ := by
  induction r with
  | nil =>
    intro sx dx w v
    exact Run.single (by simp [prog, TM2.stepAux, prepared])
  | cons b r ih =>
    intro sx dx w v
    have h := Run.head (distribute_step b r sx dx w v)
      (ih (b :: sx) (b :: dx) (true :: w) b)
    simpa only [List.length_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.replicate_add, List.replicate_one] using h

private theorem prepare_run (x : List Bool) :
    Run prog (2 * x.length + 2)
      ⟨some .copy, false, update (fun _ => []) .X x⟩
      ⟨some (.sum .next), true,
        prepared [] x x (List.replicate x.length true)⟩ := by
  obtain ⟨v, S, hr, hx, hR, hk⟩ := moveB_run
    (M := prog) (a := K.X) (b := K.R) (self := .copy)
    (next := .distribute) (d := some) (g := id) rfl (by decide)
    x x [] false (update (fun _ => []) .X x)
    (by simp) (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  have hs : S = prepared x.reverse [] [] [] := by
    funext k
    cases k with
    | X => exact hx
    | R => simpa [prepared] using hR
    | sum k =>
      have h := hk (.sum k) (by simp) (by simp)
      cases k <;> simpa [prepared] using h
    | double k =>
      have h := hk (.double k) (by simp) (by simp)
      cases k <;> simpa [prepared] using h
  rw [hs] at hr
  have hd := distribute_run x.reverse [] [] [] v
  simp only [List.reverse_reverse, List.length_reverse,
    List.append_nil] at hd
  exact (hr.trans hd).of_eq (by omega)

private theorem bits_run (bs : List Bool) :
    ∀ (v : Bool) (S : ∀ k, List (Γ k)),
      S (.sum .B) = bs.map Sym.bit →
      ∃ v' S', Run prog (bs.length + 1)
        ⟨some .bits, v, S⟩ ⟨some .done, v', S'⟩ ∧
        S' (.double .O) =
          (bs.reverse.flatMap fun b => [true, b]) ++ S (.double .O) := by
  induction bs with
  | nil =>
    intro v S hB
    exact ⟨true, S, Run.single (by simp [prog, TM2.stepAux, hB]), rfl⟩
  | cons b bs ih =>
    intro v S hB
    let S₁ := update (update S (.sum .B) (bs.map Sym.bit))
      (.double .O) (true :: b :: S (.double .O))
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
      S' (.double .O) =
        BitstringEncoding.delimit bs.reverse ++ S (.double .O) := by
  obtain ⟨v', S', hr, ho⟩ := bits_run bs v
    (update S (.double .O) (false :: S (.double .O))) (by simp [hB])
  refine ⟨v', S', Run.head (by simp [TM2.step, prog, TM2.stepAux]) hr, ?_⟩
  rw [ho, update_self]
  have hd (p : List Bool) : BitstringEncoding.delimit p =
      (p.flatMap fun b => [true, b]) ++ [false] := by
    induction p with
    | nil => rfl
    | cons b p ih => simp [BitstringEncoding.delimit, ih]
  rw [hd, List.append_assoc]
  rfl

private theorem sum_ready (as : List ℕ) :
    let r := as.flatMap fun a =>
      BitstringEncoding.delimit (Computability.encodeNat a)
    ∃ v S, RunLe prog (r.length * (2 * r.length + 9) + 5)
      ⟨some .copy, false, update (fun _ => []) .X r⟩
      ⟨some (.double (.scan .start)), v, S⟩ ∧
      S (.sum .B) = ((Computability.encodeNat as.sum).map Sym.bit).reverse ∧
      ∀ k, S (.double k) = update (fun _ => []) .X r k := by
  intro r
  have hlen : as.length ≤ r.length := SSVerify.length_le_flatMap as
  obtain ⟨v, w, S, hr, ha, hf⟩ := Cslib.Complexity.SSVerifierSum.sum_embed
    sumEmb sumLabel prog embeds_sum rfl as (List.replicate r.length true)
    true (prepared [] r r (List.replicate r.length true)) (by
      intro k
      change prepared [] r r (List.replicate r.length true) (.sum k) =
        (SSVerify.st (r.map Sym.bit)
          ((List.replicate r.length true).map Sym.bit) [] [] [] k).map id
      rw [List.map_id]
      cases k <;> rfl)
  rw [Cslib.Complexity.SSVerifierSum.pick_all as r.length hlen] at ha
  refine ⟨v, S, ?_, ?_, ?_⟩
  · exact ((prepare_run r).le le_rfl |>.trans hr).mono (by nlinarith)
  · have h := ha SSVerify.K.B
    change S (.sum .B) =
      (((Computability.encodeNat as.sum).map Sym.bit).reverse).map id at h
    simpa only [List.map_id] using h
  · intro k
    have h := hf (.double k) (fun j => by simp [sumEmb])
    cases k <;> simpa [prepared] using h

/-- **Canonical PARTITION membership transducer runs in quadratic time.**
The canonical PARTITION membership map is computed in quadratic time
by summing, doubling, and prefixing, with no value-sized loop. -/
theorem run (as : List ℕ) :
    let r := as.flatMap fun a =>
      BitstringEncoding.delimit (Computability.encodeNat a)
    ∃ v S, RunLe prog (r.length * (2 * r.length + 14) + 9)
      ⟨some .copy, false, update (fun _ => []) .X r⟩
      ⟨some .done, v, S⟩ ∧
      S (.double .O) = encodeSS (as.map (· * 2)) as.sum := by
  intro r
  obtain ⟨v₁, S₁, h₁, hb₁, hd₁⟩ := sum_ready as
  obtain ⟨v₂, D₂, hD, hoD⟩ := DoubleStream.run r v₁
  obtain ⟨S₂, h₂, ha₂, hf₂⟩ := runLe_embed doubleLabel embeds_double hD (by
    intro k
    change S₁ (.double k) = (update (fun _ => []) .X r k).map id
    rw [List.map_id]
    exact hd₁ k)
  have ho₂ : S₂ (.double .O) = DoubleStream.transform .start r := by
    have h := ha₂ DoubleStream.K.O
    change S₂ (.double .O) = (D₂ .O).map id at h
    simpa only [List.map_id, hoD] using h
  have hb₂ : S₂ (.sum .B) =
      (Computability.encodeNat as.sum).reverse.map Sym.bit := by
    rw [hf₂ (.sum .B) (fun k => by simp [doubleEmb]), hb₁,
      List.map_reverse]
  obtain ⟨v₃, S₃, h₃, ho₃⟩ := prefix_run
    (Computability.encodeNat as.sum).reverse v₂ S₂ hb₂
  have he : BitstringEncoding.bitEncode as = r := by
    change ((as.map Computability.encodeNat).map
      BitstringEncoding.delimit).flatten = _
    simp only [List.map_map, List.flatMap_def, Function.comp_def, r]
  have hlen := sum_encoding_length_le as
  rw [he] at hlen
  refine ⟨v₃, S₃, ((h₁.trans h₂).trans (h₃.le le_rfl)).mono ?_, ?_⟩
  · simp only [List.length_reverse]
    nlinarith
  · rw [ho₃, List.reverse_reverse, ho₂]
    exact congrArg (BitstringEncoding.delimit
      (Computability.encodeNat as.sum) ++ ·) (DoubleStream.transform_nums as)

instance : Fintype K := Fintype.ofList
  [.X, .R, .sum .X, .sum .W, .sum .T, .sum .A, .sum .B,
    .sum .P, .sum .Q, .double .X, .double .R, .double .O] (by
    intro k
    cases k with
    | X => decide
    | R => decide
    | sum k => cases k <;> decide
    | double k => cases k <;> decide)

noncomputable instance : Fintype Lab := Fintype.ofList
  ([.copy, .distribute, .prefix, .bits, .done] ++
    (Finset.univ.toList.map Lab.sum) ++
    (Finset.univ.toList.map Lab.double)) (by
    intro l
    cases l <;> simp)

/-- **Canonical PARTITION membership transducer as a host component.**
Finite component for normalization followed by the membership map. -/
noncomputable abbrev comp : Cslib.Complexity.Host.Comp where
  K := K
  Γ := Γ
  finΓ k := by cases k <;> infer_instance
  L := Lab
  prog := prog
  ks := Finset.univ.toList
  ks_nodup := Finset.nodup_toList _
  mem_ks k := by simp

end MetaMathlibExt.Complexity.NPComplete.Partition.MembershipCore
