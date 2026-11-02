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

/-- **Generator matrix of the Hamming (7,4) code.** $G$ is the $4 \times 7$ matrix over
$\mathbb{F}_2$, with columns indexed by the positions $1, \dots, 7$, whose $k$-th row encodes the
$k$-th message bit: if $p$ is the $k$-th of the message positions $3, 5, 6, 7$, the row has
entry $1$ at position $p$ and at each of the parity positions $1, 2, 4$ that occurs in the
binary expansion of $p$, and entry $0$ elsewhere.

Explicitly, its rows are $1110000$, $1001100$, $0101010$ and $1101001$. -/
def G : Matrix (Fin 4) (Fin 7) (ZMod 2) :=
  !![1, 1, 1, 0, 0, 0, 0;
     1, 0, 0, 1, 1, 0, 0;
     0, 1, 0, 1, 0, 1, 0;
     1, 1, 0, 1, 0, 0, 1]

/-- **Parity-check matrix of the Hamming (7,4) code.** $H$ is the $3 \times 7$ matrix over
$\mathbb{F}_2$, with columns indexed by the positions $1, \dots, 7$, whose column at position $p$
is the binary expansion of $p$, least significant bit first: its entry in row $i$, for
$i = 0, 1, 2$, is the $i$-th binary digit of $p$. -/
def H : Matrix (Fin 3) (Fin 7) (ZMod 2) :=
  !![1, 0, 1, 0, 1, 0, 1;
     0, 1, 1, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1, 1]

theorem H_apply (i : Fin 3) (j : Fin 7) : H i j = if (j.val + 1).testBit i then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> rfl

/-- **The Hamming (7,4) code.** Let $H$ be the $3 \times 7$ matrix over $\mathbb{F}_2$ whose
column $j$, for $j = 1, \dots, 7$, is the binary expansion of $j$, least significant bit first.
The Hamming code is the binary linear code of length $7$ with parity-check matrix $H$: the words
$c \in \mathbb{F}_2^7$ with $Hc = 0$. -/
def code : LinearCode (ZMod 2) (Fin 7) := ofParityCheck H

/-- **Encoder of the Hamming code.** Let $G$ be the $4 \times 7$ generator matrix over
$\mathbb{F}_2$ with rows $(1,1,1,0,0,0,0)$, $(1,0,0,1,1,0,0)$, $(0,1,0,1,0,1,0)$ and
$(1,1,0,1,0,0,1)$. A message $m \in \mathbb{F}_2^4$ is encoded as the word
$mG \in \mathbb{F}_2^7$, the combination of the rows of $G$ with coefficients $m$. -/
def encode (m : Fin 4 → ZMod 2) : Fin 7 → ZMod 2 := LinearCode.encode G m

/-- **Message bits of a word.** The message of a word $y = (y_1, \dots, y_7) \in \mathbb{F}_2^7$ is
$(y_3, y_5, y_6, y_7) \in \mathbb{F}_2^4$, its bits at the positions that are not powers of two. -/
def message (y : Fin 7 → ZMod 2) : Fin 4 → ZMod 2 := ![y 2, y 4, y 5, y 6]

theorem message_encode (m : Fin 4 → ZMod 2) : message (encode m) = m := by
  revert m
  decide +kernel

/-- **Error position of a syndrome.** For a syndrome $s = (s_0, s_1, s_2) \in \mathbb{F}_2^3$,
read its entries as bits of the number $p = s_0 + 2s_1 + 4s_2 \in \{0, \dots, 7\}$. If $p = 0$
there is no error position; otherwise the error position is $p - 1 \in \{0, \dots, 6\}$. -/
def errorPos (s : Fin 3 → ZMod 2) : Option (Fin 7) :=
  let p := (s 0).val + 2 * (s 1).val + 4 * (s 2).val
  have hp : p - 1 < 7 := by
    have := ZMod.val_lt (s 0)
    have := ZMod.val_lt (s 1)
    have := ZMod.val_lt (s 2)
    omega
  if p = 0 then none else some ⟨p - 1, hp⟩

/-- **Syndrome table of the Hamming (7,4) code.** Number the positions of a word in
$\mathbb{F}_2^7$ as $1, \dots, 7$. For a syndrome $s = (s_0, s_1, s_2) \in \mathbb{F}_2^3$,
read each $s_i$ as $0$ or $1$ and let $p = s_0 + 2 s_1 + 4 s_2$. The table sends $s$ to the zero
word if $p = 0$, and otherwise to the word whose only nonzero entry is a $1$ at position $p$.

The Hamming decoder subtracts from a received word the table entry of its syndrome; over
$\mathbb{F}_2$ this flips the bit at the position the syndrome names. -/
def table (s : Fin 3 → ZMod 2) : Fin 7 → ZMod 2 :=
  match errorPos s with
  | none => 0
  | some p => Pi.single p 1

/-- **Syndrome decoder of the Hamming code.** Let $H$ be the $3 \times 7$ parity-check matrix of
the Hamming code over $\mathbb{F}_2$, whose column $j$, for $j = 1, \dots, 7$, is the binary
expansion of $j$, least significant bit first. Given a word $y \in \mathbb{F}_2^7$, compute its
syndrome $s = (s_0, s_1, s_2) = Hy \in \mathbb{F}_2^3$. If $s = 0$, return $y$. Otherwise read
the entries of $s$ as bits of the number $p = s_0 + 2s_1 + 4s_2 \in \{1, \dots, 7\}$ and return
$y$ with its $p$-th bit flipped, counting positions from $1$. -/
def decode (y : Fin 7 → ZMod 2) : Fin 7 → ZMod 2 := y - table (syndrome H y)

theorem decode_eq_syndromeDecode : decode = syndromeDecode H table := rfl

/-- **The syndrome of a single-bit error locates it.** Let $H$ be the parity-check matrix of the
Hamming (7,4) code, and index the coordinates of words in $\mathbb{F}_2^7$ by $0, \dots, 6$, so
that index $i$ is position $i + 1$. For each index $i$, let $e_i \in \mathbb{F}_2^7$ be the word
with entry $1$ at index $i$ and $0$ elsewhere. Then the error position of the syndrome $He_i$ is
defined and equals $i$. -/
theorem errorPos_syndrome_single (i : Fin 7) :
    errorPos (syndrome H (Pi.single i 1)) = some i := by
  revert i
  decide +kernel

/-- **The Hamming decoder's syndrome table is correct.** Let $H$ be the parity-check matrix of the
Hamming (7,4) code and $T$ the syndrome table of its decoder. Then $T$ is a correct syndrome
table up to radius $1$ for $H$: for every word $e \in \mathbb{F}_2^7$ of Hamming weight at most
$1$, the word $T(He)$ has Hamming weight at most $1$ and the same syndrome as $e$, that is,
$H \, T(He) = He$. -/
theorem isSyndromeTable_table : IsSyndromeTable H 1 table := by
  intro e he
  have key : ∀ e : Fin 7 → ZMod 2, hammingNorm e ≤ 1 →
      syndrome H (table (syndrome H e)) = syndrome H e ∧
        hammingNorm (table (syndrome H e)) ≤ 1 := by
    decide +kernel
  exact key e he

/-! ### The code -/

/-- **The generator matrix is orthogonal to the parity-check matrix.** Let $G$ be the generator
matrix and $H$ the parity-check matrix of the Hamming (7,4) code over $\mathbb{F}_2$. Then
$G H^{\mathsf{T}} = 0$, the $4 \times 3$ zero matrix: every row of $G$ is orthogonal to every
row of $H$, so every row of $G$ satisfies the parity checks given by $H$. -/
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

/-- **The Hamming generator matrix generates the Hamming code.** The code generated by the
generator matrix $G$, that is, the set of words $mG$ for $m \in \mathbb{F}_2^4$, equals the
Hamming (7,4) code, the set of words $c \in \mathbb{F}_2^7$ with $Hc = 0$ for the parity-check
matrix $H$. -/
theorem ofGenerator_G_eq_code : ofGenerator G = code :=
  ofGenerator_eq_ofParityCheck_iff.mpr ⟨G_mul_H_transpose, by rw [rank_G, rank_H]; rfl⟩

theorem encode_mem_code (m : Fin 4 → ZMod 2) : encode m ∈ code :=
  ofGenerator_G_eq_code ▸ encode_mem_ofGenerator G m

theorem finrank_code : Module.finrank (ZMod 2) code = 4 := by
  rw [← ofGenerator_G_eq_code, finrank_ofGenerator, rank_G]

/-- **The Hamming (7,4) code has minimum weight at least 3.** Every nonzero codeword of the
Hamming (7,4) code over $\mathbb{F}_2$ has at least $3$ nonzero coordinates; that is, the minimum
weight of the code is at least $3$. -/
theorem three_le_minWeight_code : 3 ≤ code.minWeight := by
  rw [le_minWeight_iff]
  intro c hc hne
  have key : ∀ c : Fin 7 → ZMod 2, syndrome H c = 0 → c ≠ 0 → 3 ≤ hammingNorm c := by
    decide +kernel
  exact_mod_cast key c hc hne

/-- **Minimum distance of the Hamming (7,4) code.** The minimum distance of the Hamming (7,4)
code is $3$. -/
theorem minDist_code : code.minDist = 3 := by
  refine le_antisymm ?_ (minDist_eq_minWeight code ▸ three_le_minWeight_code)
  have h1 : encode ![1, 0, 0, 0] ∈ code := encode_mem_code _
  have hne : encode ![1, 0, 0, 0] ≠ 0 := by decide
  have h := minDist_le h1 code.zero_mem hne
  have hd : hammingDist (encode ![1, 0, 0, 0]) 0 = 3 := by decide
  rw [hd] at h
  exact_mod_cast h

/-! ### Decoding -/

/-- **The decoder corrects every error of weight at most 1.** For every codeword $c$ of the
Hamming code and every word $e \in \mathbb{F}_2^7$ of Hamming weight at most $1$, decoding
$c + e$ returns $c$. -/
theorem decode_add {c e : Fin 7 → ZMod 2} (hc : c ∈ code) (he : hammingNorm e ≤ 1) :
    decode (c + e) = c :=
  syndromeDecode_add_of_minDist_eq (d := 3) minDist_code isSyndromeTable_table hc he

/-- **Every single-bit error is corrected.** For every message $m \in \mathbb{F}_2^4$ and every
position $i$ among the $7$, flipping bit $i$ of the encoding of $m$ and then decoding returns
the encoding of $m$. -/
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

/-- **The decoder always outputs a codeword.** For every word $y \in \mathbb{F}_2^7$, the
decoding of $y$ belongs to the Hamming code. -/
theorem decode_mem_code (y : Fin 7 → ZMod 2) : decode y ∈ code := by
  have key : ∀ y : Fin 7 → ZMod 2, syndrome H (decode y) = 0 := by decide +kernel
  exact key y

/-- **The Hamming decoder changes at most one bit.** Let $D$ be the Hamming (7,4) decoder. For
every word $y \in \mathbb{F}_2^7$, the Hamming distance between $y$ and $D(y)$ is at most $1$. -/
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

/-- **No codeword is closer than the Hamming decoder's output.** Let $D$ be the Hamming (7,4)
decoder and $C \subseteq \mathbb{F}_2^7$ the Hamming code. For every word $y \in \mathbb{F}_2^7$
and every codeword $c \in C$, the Hamming distance between $y$ and $D(y)$ is at most the
Hamming distance between $y$ and $c$.

Since $D(y)$ is itself a codeword, the decoder returns a nearest codeword. -/
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

/-- **Hamming bound for the Hamming (7,4) code.** Let $k$ be the dimension of the Hamming (7,4)
code over $\mathbb{F}_2$. Then $2^k \cdot \sum_{i=0}^{1} \binom{7}{i} (2 - 1)^i \le 2^7$.

This is the Hamming bound for codes correcting one error, obtained from the general Hamming
bound for linear codes, which applies because the minimum distance $3$ exceeds $2$. -/
theorem pow_finrank_mul_sum_le :
    Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) code *
        ∑ i ∈ Finset.range (1 + 1), (7 : ℕ).choose i * (Fintype.card (ZMod 2) - 1) ^ i ≤
      Fintype.card (ZMod 2) ^ 7 :=
  pow_finrank_mul_sum_le_of_lt_minDist (by rw [minDist_code]; norm_num)

/-- **The Hamming bound is attained.** Let $k$ be the dimension of the Hamming (7,4) code over
$\mathbb{F}_2$. Then $2^k \cdot \sum_{i=0}^{1} \binom{7}{i} (2 - 1)^i = 2^7$: the Hamming bound
for one error holds with equality.

Since $k = 4$, this reads $2^4 \cdot (1 + 7) = 2^7$, so the radius-$1$ Hamming balls around the
codewords fill $\mathbb{F}_2^7$. -/
theorem pow_finrank_mul_sum_eq :
    Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) code *
        ∑ i ∈ Finset.range (1 + 1), (7 : ℕ).choose i * (Fintype.card (ZMod 2) - 1) ^ i =
      Fintype.card (ZMod 2) ^ 7 := by
  rw [finrank_code, ZMod.card]
  decide

end Cslib.CodingTheory.Hamming74
