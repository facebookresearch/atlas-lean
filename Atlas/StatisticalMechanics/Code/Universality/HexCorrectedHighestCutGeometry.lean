/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.Universality.HexCorrectedHighestCut
import Code.Universality.HexLiteralHWDepth

namespace StatMech.Universality

open HexWalk

noncomputable section




theorem hexCS_endpoint_dropLast_isLegalSAW
    (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hne : ts ≠ [])
    (hlegal : (ofTurns a h0 ts).EndpointIsLegalSAW) :
    (ofTurns a h0 ts.dropLast).IsLegalSAW := by
  induction ts using List.reverseRecOn with
  | nil => exact (hne rfl).elim
  | append_singleton base t ih =>
      simpa using (endpointIsLegalSAW_append_one_iff a h0 base t).mp hlegal |>.1






def hexCSCutPrefixOutput
    (pre : List ℤ) (cutTurn : ℤ) : List ℤ :=
  pre ++ [-cutTurn]




def hexCSCutSuffixOutput
    (entryTurn : ℤ) (suffix : List ℤ) (finalTurn : ℤ) : List ℤ :=
  (entryTurn :: suffix) ++ [finalTurn]




def hexCSDecodeCutPair (out : List ℤ × List ℤ) : List ℤ :=
  out.1.dropLast ++ [-out.1.getLastD 0] ++
    out.2.dropLast.tail ++ [out.2.getLastD 0]

@[simp] theorem hexCSCutPrefixOutput_ne_nil
    (pre : List ℤ) (cutTurn : ℤ) :
    hexCSCutPrefixOutput pre cutTurn ≠ [] := by
  simp [hexCSCutPrefixOutput]

@[simp] theorem hexCSCutSuffixOutput_ne_nil
    (entryTurn : ℤ) (suffix : List ℤ) (finalTurn : ℤ) :
    hexCSCutSuffixOutput entryTurn suffix finalTurn ≠ [] := by
  simp [hexCSCutSuffixOutput]


@[simp] theorem hexCSDecodeCutPair_encode
    (pre : List ℤ) (cutTurn entryTurn : ℤ)
    (suffix : List ℤ) (finalTurn : ℤ) :
    hexCSDecodeCutPair
        (hexCSCutPrefixOutput pre cutTurn,
          hexCSCutSuffixOutput entryTurn suffix finalTurn) =
      pre ++ [cutTurn] ++ suffix ++ [finalTurn] := by
  unfold hexCSDecodeCutPair hexCSCutPrefixOutput hexCSCutSuffixOutput
  rw [List.dropLast_concat, List.getLastD_concat,
    List.dropLast_concat, List.getLastD_concat]
  simp



theorem hexCSCutPair_source_eq
    {pre pre' : List ℤ} {cutTurn cutTurn' : ℤ}
    {entryTurn entryTurn' : ℤ} {suffix suffix' : List ℤ}
    {finalTurn finalTurn' : ℤ}
    (hpair :
      (hexCSCutPrefixOutput pre cutTurn,
          hexCSCutSuffixOutput entryTurn suffix finalTurn) =
        (hexCSCutPrefixOutput pre' cutTurn',
          hexCSCutSuffixOutput entryTurn' suffix' finalTurn')) :
    pre ++ [cutTurn] ++ suffix ++ [finalTurn] =
      pre' ++ [cutTurn'] ++ suffix' ++ [finalTurn'] := by
  have hdecode := congrArg hexCSDecodeCutPair hpair
  simpa using hdecode


theorem hexCSCutPair_length_add_one
    (pre : List ℤ) (cutTurn entryTurn : ℤ)
    (suffix : List ℤ) (finalTurn : ℤ) :
    (hexCSCutPrefixOutput pre cutTurn).length +
        (hexCSCutSuffixOutput entryTurn suffix finalTurn).length =
      (pre ++ [cutTurn] ++ suffix ++ [finalTurn]).length + 1 := by
  simp only [hexCSCutPrefixOutput, hexCSCutSuffixOutput,
    List.length_append, List.length_cons]
  omega






structure HexCSCutData
    (W : ℕ) (hW : 0 < W) (source : List ℤ) where
  pre : List ℤ
  cutTurn : ℤ
  entryTurn : ℤ
  suffix : List ℤ
  finalTurn : ℤ
  source_eq :
    source = pre ++ [cutTurn] ++ suffix ++ [finalTurn]
  prefix_top :
    HexCSTopWalkAtWidth W hW
      (hexCSCutPrefixOutput pre cutTurn)
  suffix_top :
    HexCSTopWalkAtWidth W hW
      (hexCSCutSuffixOutput entryTurn suffix finalTurn)

namespace HexCSCutData

variable {W : ℕ} {hW : 0 < W} {source : List ℤ}

def outputPair (D : HexCSCutData W hW source) : List ℤ × List ℤ :=
  (hexCSCutPrefixOutput D.pre D.cutTurn,
    hexCSCutSuffixOutput D.entryTurn D.suffix D.finalTurn)

@[simp] theorem decode_outputPair (D : HexCSCutData W hW source) :
    hexCSDecodeCutPair D.outputPair = source := by
  rw [outputPair, hexCSDecodeCutPair_encode, ← D.source_eq]

@[simp] theorem output_length_add_one (D : HexCSCutData W hW source) :
    D.outputPair.1.length + D.outputPair.2.length = source.length + 1 := by
  rw [outputPair, hexCSCutPair_length_add_one, ← D.source_eq]

end HexCSCutData

set_option maxHeartbeats 800000 in



structure HexCSHighestCutGeometry (T : ℕ) (hT : 1 ≤ T) where
  cut : ∀ d : {ts : List ℤ // HexCSNewSideWalk T hT ts},
    HexCSCutData (T + 1) (by omega) d.1

namespace HexCSHighestCutGeometry

variable {T : ℕ} {hT : 1 ≤ T}


noncomputable def toHighestCut
    (G : HexCSHighestCutGeometry T hT) : HexCSHighestCut T hT where
  split := fun d =>
    (⟨(G.cut d).outputPair.1, (G.cut d).prefix_top⟩,
      ⟨(G.cut d).outputPair.2, (G.cut d).suffix_top⟩)
  split_injective := by
    intro d e hde
    apply Subtype.ext
    have hpairs : (G.cut d).outputPair = (G.cut e).outputPair := by
      exact Prod.ext
        (congrArg (fun p => p.1.1) hde)
        (congrArg (fun p => p.2.1) hde)
    calc
      d.1 = hexCSDecodeCutPair (G.cut d).outputPair :=
        (G.cut d).decode_outputPair.symm
      _ = hexCSDecodeCutPair (G.cut e).outputPair := congrArg _ hpairs
      _ = e.1 := (G.cut e).decode_outputPair
  length_add_one := by
    intro d
    change (G.cut d).outputPair.1.length +
        (G.cut d).outputPair.2.length = d.1.length + 1
    exact (G.cut d).output_length_add_one

end HexCSHighestCutGeometry



noncomputable def hexCS_highestCuts_of_geometry
    (G : ∀ T (hT : 1 ≤ T), HexCSHighestCutGeometry T hT) :
    ∀ T (hT : 1 ≤ T), HexCSHighestCut T hT :=
  fun T hT => (G T hT).toHighestCut

end

end StatMech.Universality
