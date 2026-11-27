/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Parameterized.FPT
public import CSLibExt.Computability.Complexity.MapFirst
import CSLibExt.Computability.Complexity.PolynomialEncoding.BitScan
import CSLibExt.Computability.Complexity.PairEncodingConverter

/-!
# Polynomial-time transformations that preserve the parameter

The second field of a canonical product can have any bitstring encoding.
To reuse the bit-list pair machine, frame the bits of the second field as a
list and remove that additional layer afterward. Neither pass interprets or
enumerates the parameter.
-/

@[expose] public section

open MetaMathlibExt MetaMathlibExt.BitstringEncoding MetaMathlibExt.ComplexityTheory
open Cslib.Complexity.Preimage Cslib.Complexity.PolynomialEncoding.BitScan

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized

private inductive ReframeState | marker | payload | suffix | readBit | skipEnd
  deriving DecidableEq

private instance : Fintype ReframeState where
  elems := ⟨↑[ReframeState.marker, .payload, .suffix, .readBit, .skipEnd], by decide⟩
  complete q := by cases q <;> decide

private def reframeStep (encode : Bool) :
    ReframeState → Bool → ReframeState × List Bool
  | .marker, b => (if b then .payload else .suffix, [b])
  | .payload, b => (.marker, [b])
  | .suffix, b => if encode then (.suffix, [true, b, false]) else (.readBit, [])
  | .readBit, b => (.skipEnd, [b])
  | .skipEnd, _ => (.suffix, [])

private abbrev reframe (encode : Bool) (q : ReframeState) :=
  scan (reframeStep encode) (fun _ => []) q

private theorem reframe_prefix (encode : Bool) (word suffix : List Bool) :
    reframe encode .marker (delimit word ++ suffix) =
      delimit word ++ reframe encode .suffix suffix := by
  induction word with
  | nil => rfl
  | cons b word ih => simpa [reframe, delimit, scan, reframeStep] using ih

private theorem reframe_embed (s : List Bool) :
    reframe true .suffix s = bitEncode s := by
  rw [Cslib.Complexity.DenseSAT.Converter.bitEncode_list]
  induction s with
  | nil => rfl
  | cons b s ih =>
    simpa [reframe, scan, reframeStep, Cslib.Complexity.DenseSAT.Converter.encSnd] using ih

private theorem reframe_strip (s : List Bool) :
    reframe false .suffix (bitEncode s) = s := by
  rw [Cslib.Complexity.DenseSAT.Converter.bitEncode_list]
  induction s with
  | nil => rfl
  | cons b s ih =>
    simpa [reframe, scan, reframeStep, Cslib.Complexity.DenseSAT.Converter.encSnd] using ih

private def framedPair {β : Type} [BitstringEncoding β] (p : List Bool × β) :=
  bitEncode (p.1, bitEncode p.2)

private noncomputable def stripSecondFrame {β : Type} [BitstringEncoding β] :
    Turing.TM2ComputableInPolyTime (framedPair (β := β)) bitEncode id := by
  let m := (raw_computable (polyScan (reframeStep false) (fun _ => []) .marker)).some
  refine { m with outputsFun := fun p => ?_ }
  have strip : reframe false .marker (framedPair p) = bitEncode p := by
    change reframe false .marker (delimit (bitEncode p.1) ++ bitEncode (bitEncode p.2)) =
      delimit (bitEncode p.1) ++ bitEncode p.2
    rw [reframe_prefix, reframe_strip]
  exact strip ▸ m.outputsFun (framedPair p)

/-- When a program produces the second component as a canonically encoded list of bits,
remove that framing in polynomial time to obtain the typed pair. -/
theorem isPolyTime_of_encodedSnd {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (f : α → List Bool × β) (hf : IsPolyTime (fun x => ((f x).1, bitEncode (f x).2))) :
    IsPolyTime f := by
  obtain ⟨m⟩ := hf
  let before : Turing.TM2ComputableInPolyTime bitEncode framedPair f :=
    { m with outputsFun := fun x => m.outputsFun x }
  exact tm2ComputableInPolyTime_comp (f := f) (g := id) before stripSecondFrame

/-- Apply a polynomial-time map to the bit-list component of a canonical product.
The second component keeps its original encoding, including when it is a binary natural. -/
theorem isPolyTime_mapFirst {β : Type} [BitstringEncoding β] {g : List Bool → List Bool}
    (hg : IsPolyTime g) : IsPolyTime (fun p : List Bool × β => (g p.1, p.2)) := by
  have frame (p : List Bool × β) : reframe true .marker (bitEncode p) = framedPair p := by
    change reframe true .marker (delimit (bitEncode p.1) ++ bitEncode p.2) =
      delimit (bitEncode p.1) ++ bitEncode (bitEncode p.2)
    rw [reframe_prefix, reframe_embed]
  obtain ⟨before⟩ := raw_computable (polyScan (reframeStep true) (fun _ => []) .marker)
  obtain ⟨middle⟩ := hg.map_fst
  let pre : Turing.TM2ComputableInPolyTime bitEncode (framedPair (β := β)) id :=
    { before with outputsFun := fun p => (frame p) ▸ before.outputsFun (bitEncode p) }
  let convert (p : List Bool × β) := (g p.1, p.2)
  let mid : Turing.TM2ComputableInPolyTime framedPair framedPair convert :=
    { middle with outputsFun := fun p => middle.outputsFun (p.1, bitEncode p.2) }
  obtain ⟨firstTwo⟩ := tm2ComputableInPolyTime_comp pre mid
  exact tm2ComputableInPolyTime_comp firstTwo stripSecondFrame

/-- Postcompose an FPT reduction with a polynomial-time transformation of the instance
that leaves the target parameter unchanged. Its original parameter bound can be reused. -/
theorem FPTReduces.postcomp_instance {P Q S : ParamProblem} (h : FPTReduces P Q)
    {g : List Bool → List Bool} (hg : IsPolyTime g)
    (hcorrect : ∀ x k, Q x k ↔ S (g x) k) : FPTReduces P S := by
  obtain ⟨R, hR, bound, hb, h⟩ := h
  let post (p : List Bool × ℕ) := (g p.1, p.2)
  refine ⟨post ∘ R, hR.comp_poly (isPolyTime_mapFirst hg), bound, hb, ?_⟩
  intro x k
  exact ⟨(h x k).1, (h x k).2.trans (hcorrect _ _)⟩

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized
