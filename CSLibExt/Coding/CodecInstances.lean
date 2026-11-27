/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.Hamming74
public import CSLibExt.Coding.CRC
public import CSLibExt.Coding.ReedSolomon
public import Mathlib.Computability.Encoding
public import Mathlib.Algebra.Polynomial.CoeffList

/-!
# Hamming, CRC and Reed-Solomon codec instances

The Hamming(7,4), CRC and Reed-Solomon instances of the codec contract (`Computability.Encoding`), with their error guarantees over the existing Atlas coding declarations.
-/

@[expose] public section

open Polynomial
namespace Cslib.CodingTheory

set_option autoImplicit false

/-- Codec wrapping the Hamming(7,4) encoder; decode rejects inputs whose length differs from 7. -/
def Hamming74.encoding : Computability.Encoding (Fin 4 → ZMod 2) (ZMod 2) :=
  { encode := fun m => List.ofFn (Hamming74.encode m),
    decode := fun l =>
      if h : l.length = 7 then
        some (Hamming74.message (Hamming74.decode fun i => l[i.val]'(by omega)))
      else
        none,
    decode_encode := fun m => by
      have hl : (List.ofFn (Hamming74.encode m)).length = 7 := List.length_ofFn
      rw [dite_eq_left hl]
      congr 1
      have : (fun i : Fin 7 => (List.ofFn (Hamming74.encode m))[i.val]'(by omega)) =
          Hamming74.encode m := by
        funext i
        exact List.getElem_ofFn ..
      rw [this, Hamming74.decode_encode, Hamming74.message_encode]
  }

/-- Hamming(7,4) codewords always have length 7. -/
theorem Hamming74.encoding_encode_length (m : Fin 4 → ZMod 2) : (Hamming74.encoding.encode m).length = 7 := by
  show (List.ofFn (Hamming74.encode m)).length = 7
  exact List.length_ofFn

/-- Decoding any 7-bit vector returns its corrected message. -/
theorem Hamming74.encoding_decode_ofFn (y : Fin 7 → ZMod 2) : Hamming74.encoding.decode (List.ofFn y) = some (Hamming74.message (Hamming74.decode y)) := by
  show (if h : (List.ofFn y).length = 7 then _ else none) = _
  rw [dite_eq_left List.length_ofFn]
  congr 2

/-- Decoding a codeword with at most one corrupted bit recovers the message. -/
theorem Hamming74.encoding_decode_ofFn_encode_add (m : Fin 4 → ZMod 2) {e : Fin 7 → ZMod 2} (he : hammingNorm e ≤ 1) : Hamming74.encoding.decode (List.ofFn (Hamming74.encode m + e)) = some m := by
  rw [Hamming74.encoding_decode_ofFn, Hamming74.decode_add (Hamming74.encode_mem_code m) he,
    Hamming74.message_encode]

open Classical in
/-- Codec wrapping CRC encoding; decode rejects words not divisible by the generator. -/
noncomputable def CRC.encoding {F : Type*} [Field F] (g : F[X]) (hg : g ≠ 0) : Computability.Encoding F[X] F :=
  { encode := fun m => (CRC.encode g m).coeffList.reverse,
    decode := fun l =>
      if g ∣ Polynomial.ofCoeffList l then
        some (Polynomial.ofCoeffList (l.drop g.natDegree))
      else
        none,
    decode_encode := fun m => by
      rw [ofCoeffList_reverse_coeffList, ite_eq_left (CRC.dvd_encode g m)]
      congr 1
      ext i
      rw [coeff_ofCoeffList, List.getD_eq_getElem?_getD, List.getElem?_drop,
        ← List.getD_eq_getElem?_getD, ← coeff_ofCoeffList, ofCoeffList_reverse_coeffList,
        Nat.add_comm, CRC.coeff_encode_add hg]
  }

/-- Decoding fails exactly when the error is not divisible by the generator. -/
theorem CRC.encoding_decode_encode_add_eq_none_iff {F : Type*} [Field F] {g : F[X]} (hg : g ≠ 0) (m e : F[X]) : (CRC.encoding g hg).decode (CRC.encode g m + e).coeffList.reverse = none ↔ ¬ g ∣ e := by
  classical
  show (if g ∣ ofCoeffList (CRC.encode g m + e).coeffList.reverse then _ else none) = none ↔ _
  rw [ofCoeffList_reverse_coeffList, CRC.dvd_encode_add_iff]
  by_cases h : g ∣ e <;> simp [h]

/-- Burst errors within the degree bound are always detected. -/
theorem CRC.encoding_decode_eq_none_of_isBurstLE {F : Type*} [Field F] {g : F[X]} (hg : g ≠ 0) (hX : ¬ X ∣ g) (m : F[X]) {e : F[X]} (he : CRC.IsBurstLE e g.natDegree) : (CRC.encoding g hg).decode (CRC.encode g m + e).coeffList.reverse = none := by
  exact (CRC.encoding_decode_encode_add_eq_none_iff hg m e).2
    (CRC.not_dvd_of_isBurstLE hX he le_rfl)

/-- Single-symbol errors are always detected when the generator has at least two terms. -/
theorem CRC.encoding_decode_eq_none_of_single {F : Type*} [Field F] {g : F[X]} (hg : g ≠ 0) (h2 : 2 ≤ g.support.card) (m : F[X]) {a : F} (ha : a ≠ 0) (i : ℕ) : (CRC.encoding g hg).decode (CRC.encode g m + C a * X ^ i).coeffList.reverse = none := by
  exact (CRC.encoding_decode_encode_add_eq_none_iff hg m _).2
    (CRC.not_dvd_C_mul_X_pow h2 ha i)

open Classical in
/-- Codec wrapping Reed-Solomon encoding; decode rejects inputs whose length differs from n. -/
noncomputable def ReedSolomon.encoding {F : Type*} [Field F] [DecidableEq F] {n k : ℕ} {α : Fin n → F} (hα : Function.Injective α) (hkn : k ≤ n) (S : ReedSolomon.KeySolver α k ((n - k) / 2)) : Computability.Encoding {p : F[X] // p.degree < k} F :=
  { encode := fun p => List.ofFn (ReedSolomon.encode α p.1),
    decode := fun l =>
      if h : l.length = n then
        (ReedSolomon.decode S fun i => l[i.val]'(by omega)).bind
          (fun p => if hp : p.degree < k then some ⟨p, hp⟩ else none)
      else
        none,
    decode_encode := fun p => by
      have hl : (List.ofFn (ReedSolomon.encode α p.1)).length = n := List.length_ofFn
      rw [dite_eq_left hl]
      have : (fun i : Fin n => (List.ofFn (ReedSolomon.encode α p.1))[i.val]'(by omega)) =
          ReedSolomon.encode α p.1 + 0 := by
        funext i
        simp
      rw [this, ReedSolomon.decode_encode_add hα hkn S p.2 (by simp)]
      simp [p.2]
  }

/-- Reed-Solomon codewords always have length n. -/
theorem ReedSolomon.encoding_encode_length {F : Type*} [Field F] [DecidableEq F] {n k : ℕ} {α : Fin n → F} (hα : Function.Injective α) (hkn : k ≤ n) (S : ReedSolomon.KeySolver α k ((n - k) / 2)) (p : {p : F[X] // p.degree < k}) : ((ReedSolomon.encoding hα hkn S).encode p).length = n := by
  show (List.ofFn (ReedSolomon.encode α p.1)).length = n
  exact List.length_ofFn

/-- Decoding corrects any error affecting at most half the redundancy symbols. -/
theorem ReedSolomon.encoding_decode_ofFn_encode_add {F : Type*} [Field F] [DecidableEq F] {n k : ℕ} {α : Fin n → F} (hα : Function.Injective α) (hkn : k ≤ n) (S : ReedSolomon.KeySolver α k ((n - k) / 2)) (p : {p : F[X] // p.degree < k}) {err : Fin n → F} (herr : hammingNorm err ≤ (n - k) / 2) : (ReedSolomon.encoding hα hkn S).decode (List.ofFn (ReedSolomon.encode α p.1 + err)) = some p := by
  classical
  show (if h : (List.ofFn (ReedSolomon.encode α p.1 + err)).length = n then _ else none) = _
  rw [dite_eq_left List.length_ofFn]
  have : (fun i : Fin n => (List.ofFn (ReedSolomon.encode α p.1 + err))[i.val]'(by simp)) =
      ReedSolomon.encode α p.1 + err := by
    funext i
    simp
  simp only [this, ReedSolomon.decode_encode_add hα hkn S p.2 herr, Option.bind_some, p.2, dite_true]

/-- Decoding fails exactly when every codeword lies beyond the error radius. -/
theorem ReedSolomon.encoding_decode_ofFn_eq_none_iff {F : Type*} [Field F] [DecidableEq F] {n k : ℕ} {α : Fin n → F} (hα : Function.Injective α) (hkn : k ≤ n) (S : ReedSolomon.KeySolver α k ((n - k) / 2)) (y : Fin n → F) : (ReedSolomon.encoding hα hkn S).decode (List.ofFn y) = none ↔ ∀ p : F[X], p.degree < k → (n - k) / 2 < hammingDist y (ReedSolomon.encode α p) := by
  classical
  have h2e : 2 * ((n - k) / 2) + k ≤ n := by
    have h := Nat.div_mul_le_self (n - k) 2
    omega
  show (if h : (List.ofFn y).length = n then _ else none) = none ↔ _
  rw [dite_eq_left List.length_ofFn]
  have hfun : (fun i : Fin n => (List.ofFn y)[i.val]'(by simp)) = y := by
    funext i
    exact List.getElem_ofFn ..
  simp only [hfun]
  cases hS : ReedSolomon.decode S y with
  | none =>
    have hrhs := (ReedSolomon.decode_eq_none_iff hα h2e S).mp hS
    show (none : Option { p : F[X] // p.degree < k }) = none ↔ _
    exact iff_of_true rfl hrhs
  | some p =>
    obtain ⟨hp, hle⟩ := (ReedSolomon.decode_eq_some_iff hα h2e S).mp hS
    have hcon : ¬ ∀ q : F[X], q.degree < k → (n - k) / 2 < hammingDist y (ReedSolomon.encode α q) :=
      fun h => not_lt_of_ge hle (h p hp)
    show (if hp : p.degree < k then some (⟨p, hp⟩ : { p : F[X] // p.degree < k }) else none) = none ↔ _
    rw [dite_eq_left hp]
    simp [hcon]

end Cslib.CodingTheory
