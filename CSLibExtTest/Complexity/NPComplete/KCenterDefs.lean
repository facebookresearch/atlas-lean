/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.KCenterDefs

namespace MetaMathlibExt.Complexity.NPComplete.KCenter

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : KCenterInstance) :
    kCenterDec (bitEncode i) = true ↔ WellFormed i ∧ KCenterFeasible i := by
  simp [kCenterDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := KCenterInstance) bits = none) :
    kCenterDec bits = false := by
  simp [kCenterDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : kCenterDec [true] = false :=
  rejects_undecodable [true] rfl

/-- Opening locations `0` and `1` serves all three clients within radius `1`. -/
example :
    kCenterDec (bitEncode (([[1, 5], [5, 1], [1, 4]], 2, 1) : KCenterInstance)) = true := by
  apply (accepts_encoding _).2
  exact ⟨by unfold WellFormed; decide, [0, 1], by decide, by decide, by decide,
    [0, 1, 0], rfl, by decide⟩

/-- With one location, clients `0` and `1` need different locations within radius `1`. -/
example :
    kCenterDec (bitEncode (([[1, 5], [5, 1], [1, 4]], 1, 1) : KCenterInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, fs, -, hlen, hlt, assign, -, hassign⟩
  obtain ⟨h0m, h0c⟩ := hassign 0 (by decide)
  obtain ⟨h1m, h1c⟩ := hassign 1 (by decide)
  have h0lt := hlt _ h0m
  have h1lt := hlt _ h1m
  simp only [List.getD_cons_zero, List.getD_cons_succ, List.length_cons,
    List.length_nil] at h0c h1c h0lt h1lt
  generalize assign.getD 0 0 = a at h0m h0c h0lt
  generalize assign.getD 1 0 = b at h1m h1c h1lt
  rcases a with _ | _ | a <;> rcases b with _ | _ | b <;> simp at h0c h1c <;> try omega
  rcases fs with _ | ⟨x, _ | ⟨y, fs⟩⟩
  · simp at h0m
  · simp at h0m h1m; omega
  · simp at hlen

/-- Rows of different lengths are malformed. -/
example :
    kCenterDec (bitEncode (([[0], [0, 0]], 1, 0) : KCenterInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨h, -⟩
  exact absurd (h [0] (by simp) [0, 0] (by simp)) (by decide)

end MetaMathlibExt.Complexity.NPComplete.KCenter
