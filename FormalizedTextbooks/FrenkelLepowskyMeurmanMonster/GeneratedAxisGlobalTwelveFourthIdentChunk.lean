/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentLetterQ

/-! # Chunked short transport checks

For dense source vectors the fast short transport check `shortCheckF` over tens of thousands of
terms is split into chunks, each checked by its own kernel evaluation: the check of a
concatenation is the conjunction of the checks of the parts (when the parts have equal lengths).
`fourthDecodeChunks` unpacks a short list stored as a list of packed chunk tables. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The check of a concatenation is the conjunction of the checks of the parts. -/
theorem shortCheckF_append (d : QMaskP) :
    ∀ (A B C E : List (ℕ × ℤ)), A.length = C.length →
      shortCheckF d (A ++ B) (C ++ E) = (shortCheckF d A C && shortCheckF d B E)
  | [], B, [], E, _ => by simp [shortCheckF]
  | a :: A, B, c :: C, E, h => by
    have h' : A.length = C.length := by simpa using h
    simp only [List.cons_append, shortCheckF, shortCheckF_append d A B C E h', Bool.and_assoc]
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h

/-- Chunkwise checks of equal-length chunk lists give the check of the concatenations. -/
theorem shortCheckF_flatten (d : QMaskP) :
    ∀ (As Cs : List (List (ℕ × ℤ))), As.length = Cs.length →
      (∀ i < As.length, (As.getD i []).length = (Cs.getD i []).length) →
      (∀ i < As.length, shortCheckF d (As.getD i []) (Cs.getD i []) = true) →
      shortCheckF d As.flatten Cs.flatten = true
  | [], [], _, _, _ => rfl
  | A :: As, C :: Cs, hl, hlen, hc => by
    have hl' : As.length = Cs.length := by simpa using hl
    have h0 : A.length = C.length := hlen 0 (by simp)
    have c0 : shortCheckF d A C = true := hc 0 (by simp)
    rw [List.flatten_cons, List.flatten_cons, shortCheckF_append d A _ C _ h0, c0, Bool.true_and]
    exact shortCheckF_flatten d As Cs hl' (fun i hi => hlen (i + 1) (by simpa using hi))
      (fun i hi => hc (i + 1) (by simpa using hi))
  | [], _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl

/-- Unpack a short list stored as packed chunk tables (each with its term count). -/
def fourthDecodeChunks (ts : List (ℕ × ℕ)) : List (List (ℕ × ℤ)) :=
  ts.map (fun p => fourthDecode p.1 p.2)

/-- Unpack `n` short terms from `32`-bit fields (`17`-bit label, `15`-bit coefficient with offset
`16384`). -/
def fourthDecode32 (t n : ℕ) : List (ℕ × ℤ) :=
  (List.range n).map (fun q => ((t >>> (32 * q)) % 131072,
    (((t >>> (32 * q + 17)) % 32768 : ℕ) : ℤ) - 16384))

/-- Unpack a short list stored as packed `32`-bit chunk tables (each with its term count). -/
def fourthDecodeChunks32 (ts : List (ℕ × ℕ)) : List (List (ℕ × ℤ)) :=
  ts.map (fun p => fourthDecode32 p.1 p.2)

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
