/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.PartitionMembershipCore
public import
  CSLibExt.Computability.Complexity.PolynomialEncoding.ListNatMachine
public import CSLibExt.Computability.Complexity.Preimage
public import CSLibExt.Computability.Complexity.Karp.SubsetSumComplete

/-!
# Polynomial-time PARTITION membership reduction on all raw bitstrings

The shared exact List Nat normalizer rejects malformed framing and accepts
Mathlib's noncanonical payload values before the canonical numeric core runs.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Partition.MembershipMachine

open Turing Function TM2Program TM2Embedding BitstringEncoding
open Cslib.Complexity.Karp Cslib.Complexity.PolynomialEncoding

/-- **Stacks of the raw-input PARTITION membership machine.**
Disjoint normalizer and numeric-core workspaces and a transfer buffer. -/
inductive K | norm (k : ListNatMachine.K) | core (k : MembershipCore.K) | buffer
  deriving DecidableEq

@[reducible] def Γ : K → Type
  | .core k => MembershipCore.Γ k
  | _ => Bool

/-- **Control labels of the raw-input PARTITION membership machine.**
Normalization, transfer, canonical computation, and rejection. -/
inductive Lab
  | norm (l : ListNatMachine.Lab) | move1 | move2 | start
  | core (l : MembershipCore.Lab) | bad | done
  deriving DecidableEq

/-- **Normalizer workspace of the raw-input PARTITION membership machine.**
The exact canonicalizer's workspace. -/
def normEmb : SEmb (fun _ : ListNatMachine.K => Bool) Γ where
  e := K.norm
  inj _ _ h := K.norm.inj h
  ι _ := Equiv.refl _

/-- **Numeric-core workspace of the raw-input PARTITION membership machine.**
The canonical numeric core's workspace. -/
def coreEmb : SEmb MembershipCore.Γ Γ where
  e := K.core
  inj _ _ h := K.core.inj h
  ι _ := Equiv.refl _

def normLabel : ListNatMachine.Lab → Lab
  | .good => .move1
  | .bad => .bad
  | l => .norm l

def coreLabel : MembershipCore.Lab → Lab
  | .done => .done
  | l => .core l

/-- **Program of the raw-input PARTITION membership machine.**
Normalize exactly, then run the polynomial numeric core. -/
def prog : Lab → TM2.Stmt Γ Lab Bool
  | .norm l => mapS normEmb normLabel (ListNatMachine.prog l)
  | .move1 => moveB (.norm .output) .buffer some id .move1 .move2
  | .move2 => moveB .buffer (.core .X) some id .move2 .start
  | .start => .load (fun _ => false) <| .goto fun _ => .core .copy
  | .core l => mapS coreEmb coreLabel (MembershipCore.prog l)
  | .bad => emitR (.core (.double .O)) noSS .done
  | .done => .halt

private theorem embeds_norm :
    Embeds normEmb normLabel ListNatMachine.prog prog := by
  intro l
  cases l <;> simp [normLabel, prog, ListNatMachine.prog]

private theorem embeds_core :
    Embeds coreEmb coreLabel MembershipCore.prog prog := by
  intro l
  cases l <;> simp [coreLabel, prog, MembershipCore.prog]

private theorem core_run (as : List ℕ) (v : Bool) (S : ∀ k, List (Γ k))
    (hout : S (.norm .output) = bitEncode as) (hb : S .buffer = [])
    (hc : ∀ k, S (.core k) = []) :
    ∃ v' S', RunLe prog
      ((bitEncode as).length * (2 * (bitEncode as).length + 16) + 12)
      ⟨some .move1, v, S⟩ ⟨some .done, v', S'⟩ ∧
      S' (.core (.double .O)) = encodeSS (as.map (· * 2)) as.sum := by
  obtain ⟨v₁, S₁, h₁, _, _, hx, hk⟩ := Cslib.Complexity.Host.move2_run
    (M := prog) (a := K.norm .output) (t := K.buffer) (b := K.core .X)
    (d := some) (gt := id) (dt := some) (g := id)
    (l₁ := .move1) (l₂ := .move2) (l₃ := .start) rfl rfl
    (by decide) (by decide) (by decide) (fun _ => rfl)
    (bitEncode as) (bitEncode as) [] v S (by simpa using hout)
    (by simp [IsBitBlock]) (by simp [EndsBitBlock]) hb
  have hstart : Run prog 1 ⟨some .start, v₁, S₁⟩
      ⟨some (.core .copy), false, S₁⟩ := Run.single rfl
  have he : bitEncode as = as.flatMap
      (fun a => delimit (Computability.encodeNat a)) := by
    change ((as.map Computability.encodeNat).map delimit).flatten = _
    simp only [List.map_map, List.flatMap_def, Function.comp_def]
  obtain ⟨v₂, C₂, h₂, ho₂⟩ := MembershipCore.run as
  rw [← he] at h₂
  obtain ⟨S₂, hrun, ha, _⟩ := runLe_embed coreLabel embeds_core h₂ (by
    intro k
    change S₁ (.core k) = (update
      (fun j : MembershipCore.K => ([] : List (MembershipCore.Γ j)))
      .X (bitEncode as) k).map id
    rw [List.map_id]
    by_cases h : k = .X
    · subst k
      simpa [hc] using hx
    · rw [hk (.core k) (by simp) (by simp) (by simpa), hc]
      simp [h])
  refine ⟨v₂, S₂, ((h₁.trans hstart).le le_rfl |>.trans hrun).mono ?_, ?_⟩
  · nlinarith
  · have h := ha (MembershipCore.K.double .O)
    change S₂ (.core (.double .O)) = (C₂ (.double .O)).map id at h
    simpa only [List.map_id, ho₂] using h

/-- **Raw-input PARTITION membership machine runs in quadratic time.**
The exact all-string membership reduction has a quadratic machine
bound, including malformed inputs and noncanonical binary payloads. -/
theorem run (x : List Bool) :
    ∃ v S, RunLe prog (100 * (x.length + 1) ^ 2)
      ⟨some (.norm .loop), false,
        update (fun _ => []) (.norm .input) x⟩
      ⟨some .done, v, S⟩ ∧
      S (.core (.double .O)) = reduceToSubsetSum x := by
  obtain ⟨v₁, S₁, hn, hf, ha⟩ := ListNatMachine.run_embedded
    normEmb normLabel embeds_norm x false
    (update (fun _ => []) (.norm .input) x) (by
      intro k
      change update (fun j : K => ([] : List (Γ j)))
        (.norm .input) x (.norm k) =
        (ListNatMachine.st x [] []
          (Cslib.Complexity.FramedCNF.NormalizeMachine.st [] [] []) k).map id
      rw [List.map_id]
      cases k with
      | input | acc | output => simp [ListNatMachine.st]
      | nat k => cases k <;>
        simp [ListNatMachine.st,
          Cslib.Complexity.FramedCNF.NormalizeMachine.st])
  have hc : ∀ k, S₁ (.core k) = [] := by
    intro k
    simpa using hf (.core k) (fun j => by simp [normEmb])
  have hb : S₁ .buffer = [] := by
    simpa using hf .buffer (fun j => by simp [normEmb])
  cases hd : bitDecode (α := List ℕ) x with
  | none =>
    simp only [hd, Option.isSome_none, Bool.false_eq_true,
      ↓reduceIte, normLabel] at hn
    have hr := emitR_run (M := prog) (self := Lab.bad) (next := .done)
      (k := K.core (.double .O)) (ys := noSS) rfl v₁ S₁
    refine ⟨v₁, update S₁ (.core (.double .O))
      (noSS ++ S₁ (.core (.double .O))),
      (hn.trans (hr.le le_rfl)).mono (by nlinarith), ?_⟩
    simp [reduceToSubsetSum, hd, hc]
  | some as =>
    simp only [hd, Option.isSome_some, ↓reduceIte, normLabel] at hn
    have hout := ha as hd ListNatMachine.K.output
    change S₁ (.norm .output) = (bitEncode as).map id at hout
    rw [List.map_id] at hout
    obtain ⟨v₂, S₂, hr, ho⟩ := core_run as v₁ S₁ hout hb hc
    refine ⟨v₂, S₂, (hn.trans hr).mono ?_, ?_⟩
    · have hl := decoded_list_nat_encode_length_le hd
      have hs := Nat.mul_self_le_mul_self hl
      nlinarith
    · simpa only [reduceToSubsetSum, hd] using ho

noncomputable instance : Fintype K := Fintype.ofList
  ([.buffer] ++ Finset.univ.toList.map K.norm ++
    Finset.univ.toList.map K.core) (by intro k; cases k <;> simp)

noncomputable instance : Fintype Lab := Fintype.ofList
  ([.move1, .move2, .start, .bad, .done] ++
    Finset.univ.toList.map Lab.norm ++ Finset.univ.toList.map Lab.core)
  (by intro l; cases l <;> simp)

/-- **Raw-input PARTITION membership machine as a host component.**
The total membership reduction in the existing finite host. -/
noncomputable abbrev comp : Cslib.Complexity.Host.Comp where
  K := K
  Γ := Γ
  finΓ k := by
    cases k with
    | norm _ | buffer => infer_instance
    | core k => exact MembershipCore.comp.finΓ k
  L := Lab
  prog := prog
  ks := Finset.univ.toList
  ks_nodup := Finset.nodup_toList _
  mem_ks k := by simp

/-- **PARTITION to SUBSET-SUM map is polynomial-time.**
The total PARTITION-to-SUBSET-SUM map is polynomial-time. -/
theorem isPolyTime_reduceToSubsetSum : ComplexityTheory.IsPolyTime
    reduceToSubsetSum :=
  Cslib.Complexity.Host.isPolyTime_reduction
    (c := comp) (cX := .norm .input) (cO := .core (.double .O))
    (gX := id) (start := .norm .loop) (done := .done) (Equiv.refl Bool)
    reduceToSubsetSum (Polynomial.C 100 * (Polynomial.X + 1) ^ 2)
    rfl fun x => by simpa using run x

end MetaMathlibExt.Complexity.NPComplete.Partition.MembershipMachine

namespace MetaMathlibExt.Complexity.NPComplete.Partition

/-- **Binary-coded PARTITION is in NP.** Exact binary-coded PARTITION belongs to canonical NP. -/
theorem partitionDec_mem_NP : partitionDec ∈ ComplexityTheory.NP :=
  ComplexityTheory.mem_NP_of_polyManyOneRed
    Cslib.Complexity.Karp.subsetSumDec_mem_NP
    ⟨reduceToSubsetSum, MembershipMachine.isPolyTime_reduceToSubsetSum,
      reduceToSubsetSum_correct⟩

end MetaMathlibExt.Complexity.NPComplete.Partition
