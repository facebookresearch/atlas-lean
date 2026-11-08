/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.LinearCode
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

/-!
# The Hamming (7,4) code

Hamming's single-error-correcting code: 4 message bits, 3 parity bits, length 7. Positions are
numbered `1, …, 7`; the parity bits sit at the powers of two `1, 2, 4` and the message bits at
`3, 5, 6, 7`. The column of the parity-check matrix `H` for position `p` is the binary expansion
of `p`, so the syndrome of a word with one flipped bit is the binary expansion of that bit's
position.

* `encode`: the encoder `m ↦ m ᵥ* G`, which writes the message into positions `3, 5, 6, 7`
  (`message_encode`).
* `decode`: compute the syndrome, read it as a position, and flip that bit.
  * `decode_encode_add_single`: it corrects every single-bit error;
  * `decode_add`: more generally, `decode (c + e) = c` for every codeword `c` and every error `e`
    of weight at most 1.
  The decoder is syndrome decoding with a correct table (`decode_eq_syndromeDecode`,
  `isSyndromeTable_table`), so correctness is an instance of the general theorem.
* `ofGenerator_G_eq_code`: `G` and `H` present the same code, of dimension 4 (`finrank_code`).
* `minDist_code`: the minimum distance is 3.
* **Perfect**: every word lies within distance 1 of exactly one codeword
  (`existsUnique_hammingDist_le_one`), the decoder returns a nearest codeword
  (`hammingDist_decode_le`), and the Hamming bound for one error, instantiated from the general
  bound in `LinearCode.lean` (`pow_finrank_mul_sum_le`), holds with equality,
  `2^4 · (1 + 7) = 2^7` (`pow_finrank_mul_sum_eq`).

## References

* R. W. Hamming, "Error Detecting and Error Correcting Codes", *Bell System Technical Journal*
  29 (1950), 147–160.
* F. J. MacWilliams, N. J. A. Sloane, *The Theory of Error-Correcting Codes*, North-Holland,
  1977, Ch. 1.
-/

namespace Cslib.CodingTheory.Hamming74

open Matrix LinearCode

/-- The generator matrix. Row `k` encodes message bit `k`: it sets that bit's position
(`3, 5, 6, 7`) and the parity bits whose positions occur in its binary expansion. -/
def G : Matrix (Fin 4) (Fin 7) (ZMod 2) :=
  !![1, 1, 1, 0, 0, 0, 0;
     1, 0, 0, 1, 1, 0, 0;
     0, 1, 0, 1, 0, 1, 0;
     1, 1, 0, 1, 0, 0, 1]

/-- The parity-check matrix. The column for position `p` (index `p - 1`) is the binary expansion
of `p`, least significant bit first. -/
def H : Matrix (Fin 3) (Fin 7) (ZMod 2) :=
  !![1, 0, 1, 0, 1, 0, 1;
     0, 1, 1, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1, 1]

theorem H_apply (i : Fin 3) (j : Fin 7) : H i j = if (j.val + 1).testBit i then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> rfl

/-- The Hamming code. -/
def code : LinearCode (ZMod 2) (Fin 7) := ofParityCheck H

/-- The encoder. -/
def encode (m : Fin 4 → ZMod 2) : Fin 7 → ZMod 2 := LinearCode.encode G m

/-- The message bits of a word: positions `3, 5, 6, 7`. -/
def message (y : Fin 7 → ZMod 2) : Fin 4 → ZMod 2 := ![y 2, y 4, y 5, y 6]

theorem message_encode (m : Fin 4 → ZMod 2) : message (encode m) = m := by
  revert m
  decide +kernel

/-- The position (`0, …, 6`) that a nonzero syndrome names, read as a binary number. -/
def errorPos (s : Fin 3 → ZMod 2) : Option (Fin 7) :=
  let p := (s 0).val + 2 * (s 1).val + 4 * (s 2).val
  have hp : p - 1 < 7 := by
    have := ZMod.val_lt (s 0)
    have := ZMod.val_lt (s 1)
    have := ZMod.val_lt (s 2)
    omega
  if p = 0 then none else some ⟨p - 1, hp⟩

/-- The decoder's syndrome table: flip the bit the syndrome names. -/
def table (s : Fin 3 → ZMod 2) : Fin 7 → ZMod 2 :=
  match errorPos s with
  | none => 0
  | some p => Pi.single p 1

/-- The **decoder**: compute the syndrome and flip the bit it names. -/
def decode (y : Fin 7 → ZMod 2) : Fin 7 → ZMod 2 := y - table (syndrome H y)

theorem decode_eq_syndromeDecode : decode = syndromeDecode H table := rfl

/-- The syndrome of a single flipped bit names its position. -/
theorem errorPos_syndrome_single (i : Fin 7) :
    errorPos (syndrome H (Pi.single i 1)) = some i := by
  revert i
  decide +kernel

/-- The table is a correct syndrome table for one error. -/
theorem isSyndromeTable_table : IsSyndromeTable H 1 table := by
  intro e he
  have key : ∀ e : Fin 7 → ZMod 2, hammingNorm e ≤ 1 →
      syndrome H (table (syndrome H e)) = syndrome H e ∧
        hammingNorm (table (syndrome H e)) ≤ 1 := by
    decide +kernel
  exact key e he

/-! ### The code -/

theorem G_mul_H_transpose : G * Hᵀ = 0 := by decide +kernel

theorem encode_injective : Function.Injective encode := by
  intro m m' h
  rw [← message_encode m, ← message_encode m', h]

theorem rank_G : G.rank = 4 := by
  rw [← finrank_ofGenerator, ofGenerator, LinearMap.finrank_range_of_inj encode_injective,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

theorem rank_H : H.rank = 3 := by
  have hinj : Function.Injective (LinearCode.encode H) := by
    have key : ∀ m m' : Fin 3 → ZMod 2,
        LinearCode.encode H m = LinearCode.encode H m' → m = m' := by
      decide +kernel
    exact fun m m' h ↦ key m m' h
  rw [← finrank_ofGenerator, ofGenerator, LinearMap.finrank_range_of_inj hinj,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-- `G` generates the code with parity checks `H`. -/
theorem ofGenerator_G_eq_code : ofGenerator G = code :=
  ofGenerator_eq_ofParityCheck_iff.mpr ⟨G_mul_H_transpose, by rw [rank_G, rank_H]; rfl⟩

theorem encode_mem_code (m : Fin 4 → ZMod 2) : encode m ∈ code :=
  ofGenerator_G_eq_code ▸ encode_mem_ofGenerator G m

theorem finrank_code : Module.finrank (ZMod 2) code = 4 := by
  rw [← ofGenerator_G_eq_code, finrank_ofGenerator, rank_G]

/-- Every nonzero codeword has weight at least 3. -/
theorem three_le_minWeight_code : 3 ≤ code.minWeight := by
  rw [le_minWeight_iff]
  intro c hc hne
  have key : ∀ c : Fin 7 → ZMod 2, syndrome H c = 0 → c ≠ 0 → 3 ≤ hammingNorm c := by
    decide +kernel
  exact_mod_cast key c hc hne

/-- The minimum distance of the Hamming code is 3. -/
theorem minDist_code : code.minDist = 3 := by
  refine le_antisymm ?_ (minDist_eq_minWeight code ▸ three_le_minWeight_code)
  have h1 : encode ![1, 0, 0, 0] ∈ code := encode_mem_code _
  have hne : encode ![1, 0, 0, 0] ≠ 0 := by decide
  have h := minDist_le h1 code.zero_mem hne
  have hd : hammingDist (encode ![1, 0, 0, 0]) 0 = 3 := by decide
  rw [hd] at h
  exact_mod_cast h

/-! ### Decoding -/

/-- **The decoder corrects every error of weight at most 1** in every codeword. -/
theorem decode_add {c e : Fin 7 → ZMod 2} (hc : c ∈ code) (he : hammingNorm e ≤ 1) :
    decode (c + e) = c :=
  syndromeDecode_add_of_minDist_eq (d := 3) minDist_code isSyndromeTable_table hc he

/-- **Every single-bit error is corrected**, and the message is recovered. -/
theorem decode_encode_add_single (m : Fin 4 → ZMod 2) (i : Fin 7) :
    decode (encode m + Pi.single i 1) = encode m :=
  decode_add (encode_mem_code m) (by
    have key : ∀ i : Fin 7, hammingNorm (Pi.single i (1 : ZMod 2) : Fin 7 → ZMod 2) ≤ 1 := by
      decide +kernel
    exact key i)

theorem message_decode_encode_add_single (m : Fin 4 → ZMod 2) (i : Fin 7) :
    message (decode (encode m + Pi.single i 1)) = m := by
  rw [decode_encode_add_single, message_encode]

theorem decode_encode (m : Fin 4 → ZMod 2) : decode (encode m) = encode m := by
  simpa using decode_add (encode_mem_code m) (e := 0) (by simp)

/-! ### The code is perfect -/

/-- The decoder always outputs a codeword. -/
theorem decode_mem_code (y : Fin 7 → ZMod 2) : decode y ∈ code := by
  have key : ∀ y : Fin 7 → ZMod 2, syndrome H (decode y) = 0 := by decide +kernel
  exact key y

/-- The decoder changes at most one bit. -/
theorem hammingDist_decode_le_one (y : Fin 7 → ZMod 2) : hammingDist y (decode y) ≤ 1 := by
  revert y
  decide +kernel

/-- **The Hamming code is perfect**: every word lies within distance 1 of exactly one codeword. -/
theorem existsUnique_hammingDist_le_one (y : Fin 7 → ZMod 2) :
    ∃! c, c ∈ code ∧ hammingDist y c ≤ 1 := by
  refine ⟨decode y, ⟨decode_mem_code y, hammingDist_decode_le_one y⟩, ?_⟩
  rintro c ⟨hc, hdist⟩
  by_contra hne
  have h3 := minDist_le hc (decode_mem_code y) hne
  rw [minDist_code] at h3
  have htri := hammingDist_triangle c y (decode y)
  rw [hammingDist_comm c y] at htri
  have : 3 ≤ hammingDist c (decode y) := by exact_mod_cast h3
  have := hammingDist_decode_le_one y
  omega

/-- The decoder returns a nearest codeword. -/
theorem hammingDist_decode_le (y : Fin 7 → ZMod 2) {c : Fin 7 → ZMod 2} (hc : c ∈ code) :
    hammingDist y (decode y) ≤ hammingDist y c := by
  have h1 := hammingDist_decode_le_one y
  by_cases hce : c = decode y
  · rw [hce]
  have h3 := minDist_le hc (decode_mem_code y) hce
  rw [minDist_code] at h3
  have : 3 ≤ hammingDist c (decode y) := by exact_mod_cast h3
  have htri := hammingDist_triangle c y (decode y)
  rw [hammingDist_comm c y] at htri
  omega

/-- The Hamming bound for one error, from the general bound for linear codes
(`pow_finrank_mul_sum_le_of_lt_minDist`, which rests on MathlibExt's sphere-packing bound). -/
theorem pow_finrank_mul_sum_le :
    Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) code *
        ∑ i ∈ Finset.range (1 + 1), (7 : ℕ).choose i * (Fintype.card (ZMod 2) - 1) ^ i ≤
      Fintype.card (ZMod 2) ^ 7 :=
  pow_finrank_mul_sum_le_of_lt_minDist (by rw [minDist_code]; norm_num)

/-- **The Hamming bound is attained**: the inequality `pow_finrank_mul_sum_le` is an equality,
`2^4 · (1 + 7) = 2^7`, so the radius-1 balls around the codewords fill the space. -/
theorem pow_finrank_mul_sum_eq :
    Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) code *
        ∑ i ∈ Finset.range (1 + 1), (7 : ℕ).choose i * (Fintype.card (ZMod 2) - 1) ^ i =
      Fintype.card (ZMod 2) ^ 7 := by
  rw [finrank_code, ZMod.card]
  decide

end Cslib.CodingTheory.Hamming74
