/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Logic.Function.Iterate
public import PhyslibExt.Numerical.PhysicalErrorBudgets
import Mathlib.Tactic.Ring

/-!
# Rational thermal trace certificate: checker, soundness and bounded decoding

A lumped body cooling in a fixed bath (`PhysicalErrorBudgets`, sections F-H) from the temperature
`T_0 = T_amb + Δ` reaches, after `j` explicit Euler steps of size `τ / 10`, the temperature
`T_j = T_amb + Δ y_j` with the coefficient `y_j = (9 / 10) ^ j`, `j = 0, …, 10`: each step
multiplies the excess `T - T_amb` by `9 / 10`. For `Δ ≠ 0` the coefficient is the normalized excess
`(T_j - T_amb) / Δ`. At `Δ = 0` every `T_j` is `T_amb`, the coefficient form holds for every trace,
and the quotient, Lean's `0 / 0 = 0`, does not recover `y_j`. This file checks a trace of
coefficients as data and binds an accepted trace to the proved analytic bound, for every `Δ`. It
also reads the trace from text in a bounded ASCII format, with a decoder that the kernel evaluates.

## i. Overview

The checker `checkThermalTrace` reads a list of rationals and returns a `Bool`. It accepts exactly
when the list has eleven entries `y_0, …, y_10`, the first is the initial coefficient `y_0 = 1`,
and all ten identities `y_(j+1) = (9 / 10) y_j` hold. The certificate is that
eleven-element list, its last entry `y_10` included and checked by the last identity; there is no
separately supplied expected terminal value or error bound, and floating-point behavior does not
enter. Acceptance is decided by kernel reduction (`decide +kernel`), and how the list or its text
was produced (a file, a program, a floating-point computation) is outside the claim.

Soundness: an accepted list satisfies `y_j = (9 / 10) ^ j` after the cast to the reals, by
induction on the ten identities in `ℚ` and the cast homomorphism; in particular the terminal value
is `(9 / 10) ^ 10`. The physical endpoint `T_amb + Δ y_10` reconstructed from an accepted trace is
the tenth Euler iterate from `T_amb + Δ` (`PhysicalErrorBudgets.bathEuler_closed_form`), so the
proved ten-step bound `PhysicalErrorBudgets.bathEuler_tenStep_error` applies to it:
`|T_amb + Δ y_10 - T(τ)| ≤ |Δ| / 10` for `C, G > 0` and every real `Δ`; at `Δ = 0` the endpoint
and `T(τ)` are both `T_amb`.

Bounded decoding: an encoded trace is exactly eleven tokens separated by `,`, with no spaces,
exponents or `+` signs. A token is `numerator/denominator`: the numerator is an optional `-` and one
to eleven decimal digits, of absolute value at most `10 ^ 10`, and the denominator is one to eleven
decimal digits denoting an integer in `[1, 10 ^ 10]`. Leading zeros and `-0` are accepted with their
ordinary integer values, so a trace has several encodings; decoding fixes the value, not the
spelling. The decoder `decodeTrace` first rejects an input of more than 300 characters. This is the
explicit first check of the format; eleven admissible tokens and ten commas have at most 274
characters, so it rejects nothing the token clauses accept. The decoder then returns `none` for a
token count other than eleven or a malformed or out-of-bounds token, and otherwise the list of the
token values `numerator / denominator`, each denominator checked positive before the division.

A digit run decodes to the integer `Nat.ofDigits` assigns it, and an input decodes exactly when it
is the comma-joined encoding of eleven admissible tokens with at most 300 characters, to the list of
their values; it is rejected otherwise. `checkEncodedTrace` decodes and passes the decoded list to
`checkThermalTrace`: an encoding is accepted exactly when it decodes to the trace `(9 / 10) ^ j`,
and the soundness above then holds for the decoded list. On a concrete encoding acceptance is a
closed Boolean computation, checked by `decide +kernel`. The encoding carries coefficients only, no
temperature and no `Δ`: one accepted encoding certifies the same coefficients for every `Δ`,
including `Δ = 0`.

Model inputs: those of the bath model (constant `C > 0`, `G > 0`, `T_amb`, the linear bath law).
Non-goals: no floating-point or compiled-code refinement; no parser beyond the bounded decoder of
sections D and E, so no runtime or compiled parser refinement and no byte-level input; no general
Euler convergence theorem; and no empirical adequacy or system safety claim.

## ii. Key results

- `ThermalTraceCertificate.checkThermalTrace`: the eleven-value Boolean checker.
- `ThermalTraceCertificate.checkThermalTrace_sound`,
  `ThermalTraceCertificate.checkThermalTrace_terminal`: acceptance gives `y_j = (9 / 10) ^ j` in
  the reals, and the terminal value.
- `ThermalTraceCertificate.traceEndpoint`,
  `ThermalTraceCertificate.traceEndpoint_eq_iterate`,
  `ThermalTraceCertificate.traceEndpoint_error`: the reconstructed endpoint is the tenth Euler
  iterate and lies within `|Δ| / 10` of `T(τ)`.
- `ThermalTraceCertificate.decodeTrace`, `ThermalTraceCertificate.decodeDecimal_eq_some_iff`,
  `ThermalTraceCertificate.decodeToken_eq_some_iff`: the bounded decoder; a digit run and a token
  decode exactly when well formed and within bounds, to their positional and rational values.
- `ThermalTraceCertificate.decodeTrace_eq_some_iff`,
  `ThermalTraceCertificate.decodeTrace_eq_none_iff`: an input decodes exactly when it is the
  comma-joined encoding of eleven admissible tokens with at most 300 characters, to the list of
  their values, and is rejected otherwise.
- `ThermalTraceCertificate.checkEncodedTrace`,
  `ThermalTraceCertificate.checkEncodedTrace_eq_true_iff`,
  `ThermalTraceCertificate.checkEncodedTrace_eq_true_iff_decodeTrace_eq`,
  `ThermalTraceCertificate.checkEncodedTrace_sound`: decode, then check; an encoding is accepted
  exactly when it decodes to the trace `(9 / 10) ^ j`, and soundness holds for the decoded list.
- The accepted exact trace, four rejected traces, the endpoint of a body at `350` in a bath at
  `300`, the same body started at the bath temperature (`Δ = 0`), the accepted reduced encoding of
  the trace with rejected encodings and token boundaries, and the decoded trace read as
  coefficients are in `PhyslibExtTest.Numerical.ThermalTraceCertificateTest`.

## iii. Table of contents

- A. The trace checker
- B. Soundness
- C. The physical endpoint and its analytic bound
- D. Bounded decoding of an encoded trace
- E. The proof-replay boundary

## iv. References

- E. Hairer, S. P. Nørsett and G. Wanner, *Solving Ordinary Differential Equations I*, 2nd ed.,
  Springer (1993), Section I.7 (the explicit Euler method).
- F. P. Incropera, D. P. DeWitt, T. L. Bergman and A. S. Lavine, *Fundamentals of Heat and Mass
  Transfer*, 7th ed., Wiley (2011), Section 5.1 (the lumped capacitance method).
- Y. Bertot and P. Castéran, *Interactive Theorem Proving and Program Development*, Springer
  (2004), Chapter 16 (proof by reflection: a Boolean checker evaluated by the kernel).
- ISO/IEC 646:1991, *ISO 7-bit coded character set for information interchange* (the ASCII
  digits and separators of the encoding).
- D. E. Knuth, *The Art of Computer Programming, Vol. 2: Seminumerical Algorithms*, 3rd ed.,
  Addison-Wesley (1997), Sections 4.1 (positional number systems) and 4.4 (radix conversion).
- `PhysicalErrorBudgets.bathEuler_closed_form` and `PhysicalErrorBudgets.bathEuler_tenStep_error`.
-/

@[expose] public section

namespace ThermalTraceCertificate

open PhysicalErrorBudgets

/-! ## A. The trace checker -/

/-- **The trace checker.** Accept a list `y` of rationals exactly when it has eleven entries
`y_0, …, y_10`, the first is the initial coefficient `y_0 = 1`, and all ten identities
`y_(j+1) = (9 / 10) y_j`, `j = 0, …, 9`, hold. The entries are the coefficients of
`T_j = T_amb + Δ y_j`, the normalized excesses `(T_j - T_amb) / Δ` only for `Δ ≠ 0`. Entries are
read with the default `0`, which an accepted list never uses. The certificate is the
eleven-element list itself, `y_10` included; there is no separately supplied expected terminal
value or error bound. -/
def checkThermalTrace (y : List ℚ) : Bool :=
  y.length == 11 && y.getD 0 0 == 1 &&
    (List.range 10).all fun j => y.getD (j + 1) 0 == 9 / 10 * y.getD j 0

/-! ## B. Soundness -/

private lemma checkThermalTrace_rat {y : List ℚ} (h : checkThermalTrace y = true) :
    y.length = 11 ∧ ∀ j ≤ 10, y.getD j 0 = (9 / 10 : ℚ) ^ j := by
  unfold checkThermalTrace at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hlen, h0⟩, hstep⟩ := h
  refine ⟨hlen, fun j hj => ?_⟩
  induction j with
  | zero => simpa using h0
  | succ j ih =>
    rw [hstep j (by omega), ih (by omega), pow_succ]
    ring

/-- **Soundness.** An accepted list has eleven entries, and `y_j = (9 / 10) ^ j` for
`j = 0, …, 10` after the cast to the reals. -/
lemma checkThermalTrace_sound {y : List ℚ} (h : checkThermalTrace y = true) :
    y.length = 11 ∧ ∀ j ≤ 10, ((y.getD j 0 : ℚ) : ℝ) = (9 / 10 : ℝ) ^ j := by
  obtain ⟨hlen, hy⟩ := checkThermalTrace_rat h
  refine ⟨hlen, fun j hj => ?_⟩
  rw [hy j hj]
  push_cast
  ring

/-- **Terminal value.** An accepted trace ends at `y_10 = (9 / 10) ^ 10` in the reals. -/
lemma checkThermalTrace_terminal {y : List ℚ} (h : checkThermalTrace y = true) :
    ((y.getD 10 0 : ℚ) : ℝ) = (9 / 10 : ℝ) ^ 10 := by
  exact (checkThermalTrace_sound h).2 10 le_rfl

/-! ## C. The physical endpoint and its analytic bound -/

/-- The physical endpoint `T_amb + Δ y_10` reconstructed from a trace `y` of coefficients,
`T_j = T_amb + Δ y_j`, for the bath temperature `T_amb` and the initial excess `Δ = T_0 - T_amb`.
`Δ` may be `0`; the endpoint is then `T_amb` for every trace. -/
noncomputable def traceEndpoint (Tamb Δ : ℝ) (y : List ℚ) : ℝ :=
  Tamb + Δ * (y.getD 10 0 : ℝ)

private lemma bathEuler_iterate_succ (C G Tamb dt x : ℝ) (j : ℕ) :
    (bathEulerStep C G Tamb dt)^[j + 1] x = bathEulerStep C G Tamb dt
      ((bathEulerStep C G Tamb dt)^[j] x) :=
  Function.iterate_succ_apply' _ _ _

/-- **The certified endpoint is the tenth Euler iterate.** For `C, G > 0` and an accepted trace,
`T_amb + Δ y_10` is the result of ten explicit Euler steps of size `τ / 10`, `τ = C / G`, started
at `T_amb + Δ`. -/
lemma traceEndpoint_eq_iterate {C G : ℝ} (hC : 0 < C) (hG : 0 < G) (Tamb Δ : ℝ) {y : List ℚ}
    (h : checkThermalTrace y = true) :
    traceEndpoint Tamb Δ y =
      (bathEulerStep C G Tamb (thermalTimeConstant C G / 10))^[10] (Tamb + Δ) := by
  have hcf := bathEuler_closed_form hC hG (Tamb := Tamb) (Δ := Δ)
    (X := fun j => (bathEulerStep C G Tamb (thermalTimeConstant C G / 10))^[j] (Tamb + Δ))
    rfl (fun j => bathEuler_iterate_succ C G Tamb _ (Tamb + Δ) j) 10
  rw [traceEndpoint, checkThermalTrace_terminal h]
  exact hcf.symm

/-- **Analytic bound for the certified endpoint.** For `C, G > 0` and an accepted trace, the
reconstructed endpoint lies within `|Δ| / 10` of the exact bath trajectory at `t = τ`. -/
lemma traceEndpoint_error {C G : ℝ} (hC : 0 < C) (hG : 0 < G) (Tamb Δ : ℝ) {y : List ℚ}
    (h : checkThermalTrace y = true) :
    |traceEndpoint Tamb Δ y - bathTrajectory C G Tamb Δ (thermalTimeConstant C G)| ≤ |Δ| / 10 := by
  rw [traceEndpoint_eq_iterate hC hG Tamb Δ h]
  exact bathEuler_tenStep_error hC hG
    (X := fun j => (bathEulerStep C G Tamb (thermalTimeConstant C G / 10))^[j] (Tamb + Δ))
    rfl (fun j => bathEuler_iterate_succ C G Tamb _ (Tamb + Δ) j)

/-! ## D. Bounded decoding of an encoded trace -/

/-- The value `0, …, 9` of the ASCII decimal digit characters `'0', …, '9'`. -/
def digitValue (c : Char) : ℕ := c.toNat - '0'.toNat

/-- **Positional value.** The natural number a run of decimal digits denotes, most significant
digit first: `Nat.ofDigits 10` of the digit values in reverse order. Leading zeros add nothing. -/
def decimalValue (ds : List Char) : ℕ := Nat.ofDigits 10 (ds.reverse.map digitValue)

/-- A digit run of the format: one to eleven ASCII decimal digits `'0', …, '9'`. -/
def IsDecimalDigits (ds : List Char) : Prop :=
  1 ≤ ds.length ∧ ds.length ≤ 11 ∧ ∀ c ∈ ds, c.isDigit = true

/-- **Bounded decimal decoding.** Read one to eleven decimal digits, most significant first, by
Horner's rule; `none` for an empty run, more than eleven characters or any character other than
`'0', …, '9'`. -/
def decodeDecimal (ds : List Char) : Option ℕ :=
  if 1 ≤ ds.length ∧ ds.length ≤ 11 ∧ ds.all Char.isDigit = true then
    some (ds.foldl (fun n c => 10 * n + digitValue c) 0)
  else none

/-- Decode a numerator: an optional `-` and one to eleven decimal digits, of absolute value at most
`10 ^ 10`; `none` otherwise. `-0` decodes to `0`. -/
def decodeNumerator (cs : List Char) : Option ℤ :=
  if cs.head? = some '-' then
    (decodeDecimal cs.tail).bind fun n => if n ≤ 10 ^ 10 then some (-(n : ℤ)) else none
  else
    (decodeDecimal cs).bind fun n => if n ≤ 10 ^ 10 then some (n : ℤ) else none

/-- Decode a denominator: one to eleven decimal digits denoting an integer in `[1, 10 ^ 10]`;
`none` otherwise, `0` included. -/
def decodeDenominator (cs : List Char) : Option ℕ :=
  (decodeDecimal cs).bind fun d => if 1 ≤ d ∧ d ≤ 10 ^ 10 then some d else none

/-- Split a character list at every `sep`, dropping the separators: `List.splitOn sep`, written by
structural recursion so that kernel reduction in an importing module evaluates it. -/
def splitOnChar (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c = sep then [] :: splitOnChar sep cs else (splitOnChar sep cs).modifyHead (c :: ·)

/-- **Token decoding.** Split a token at `/` into exactly a numerator and a denominator and decode
both; the denominator is checked positive before the division. `none` otherwise. -/
def decodeToken (t : List Char) : Option ℚ :=
  match splitOnChar '/' t with
  | [a, b] =>
    (decodeNumerator a).bind fun z => (decodeDenominator b).map fun (d : ℕ) => (z : ℚ) / d
  | _ => none

/-- **The trace decoder.** For an input of at most 300 characters with exactly eleven
comma-separated tokens, the list of the token values when every token decodes; `none` for a longer
input, any other token count, or a token that does not decode. -/
def decodeTrace (s : List Char) : Option (List ℚ) :=
  if s.length ≤ 300 ∧ (splitOnChar ',' s).length = 11 then
    (splitOnChar ',' s).mapM decodeToken
  else none

/-- A token of the format as written, `[-]digits/digits`: the sign, then the numerator and the
denominator digit runs, leading zeros included. -/
structure TraceToken where
  /-- Whether the token starts with `-`. -/
  negative : Bool
  /-- The numerator digits, most significant first. -/
  numeratorDigits : List Char
  /-- The denominator digits, most significant first. -/
  denominatorDigits : List Char

namespace TraceToken

/-- The characters of a token: `-` when negative, the numerator digits, `/`, the denominator
digits. -/
def encode (t : TraceToken) : List Char :=
  (if t.negative then ['-'] else []) ++ t.numeratorDigits ++ '/' :: t.denominatorDigits

/-- The signed integer the numerator denotes; `-0` denotes `0`. -/
def numerator (t : TraceToken) : ℤ :=
  if t.negative then -(decimalValue t.numeratorDigits : ℤ) else decimalValue t.numeratorDigits

/-- The natural number the denominator digits denote. -/
def denominator (t : TraceToken) : ℕ := decimalValue t.denominatorDigits

/-- **Admissible token.** Both digit runs have one to eleven decimal digits,
`|numerator| ≤ 10 ^ 10` and `1 ≤ denominator ≤ 10 ^ 10`. -/
def Admissible (t : TraceToken) : Prop :=
  IsDecimalDigits t.numeratorDigits ∧ IsDecimalDigits t.denominatorDigits ∧
    |t.numerator| ≤ 10 ^ 10 ∧ 1 ≤ t.denominator ∧ t.denominator ≤ 10 ^ 10

/-- The rational a token denotes, `numerator / denominator`; for an admissible token a quotient by
a denominator of at least `1`. -/
def value (t : TraceToken) : ℚ := (t.numerator : ℚ) / (t.denominator : ℚ)

end TraceToken

private lemma splitOnChar_eq_splitOn (sep : Char) (s : List Char) :
    splitOnChar sep s = s.splitOn sep := by
  induction s with
  | nil => rw [List.splitOn_nil]; rfl
  | cons c cs ih =>
    rw [splitOnChar, List.splitOn_cons_eq_ite_modifyHead, ih]
    simp only [beq_iff_eq]

private lemma foldl_digitValue (ds : List Char) (acc : ℕ) :
    ds.foldl (fun n c => 10 * n + digitValue c) acc = acc * 10 ^ ds.length + decimalValue ds := by
  induction ds generalizing acc with
  | nil => simp [decimalValue]
  | cons c ds ih =>
    rw [List.foldl_cons, ih]
    simp only [decimalValue, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      Nat.ofDigits_append, Nat.ofDigits_singleton, List.length_map, List.length_reverse,
      List.length_cons]
    ring

/-- **Bounded decimal decoding denotes its integer.** A digit run decodes exactly when it has one
to eleven decimal digits, and then to its positional value. -/
lemma decodeDecimal_eq_some_iff {ds : List Char} {n : ℕ} :
    decodeDecimal ds = some n ↔ IsDecimalDigits ds ∧ n = decimalValue ds := by
  have hall : ds.all Char.isDigit = true ↔ ∀ c ∈ ds, c.isDigit = true := List.all_eq_true
  unfold decodeDecimal IsDecimalDigits
  split_ifs with h
  · rw [foldl_digitValue ds 0, zero_mul, zero_add, Option.some.injEq, eq_comm]
    exact ⟨fun h' => ⟨⟨h.1, h.2.1, hall.mp h.2.2⟩, h'⟩, fun h' => h'.2⟩
  · simp only [false_iff]
    exact fun h' => h ⟨h'.1.1, h'.1.2.1, hall.mpr h'.1.2.2⟩

private lemma not_mem_of_isDigit {ds : List Char} {c : Char} (hds : ∀ x ∈ ds, x.isDigit = true)
    (hc : c.isDigit = false) : c ∉ ds := fun h => by simp [hds c h] at hc

private lemma decodeDenominator_eq_some_iff {b : List Char} {d : ℕ} :
    decodeDenominator b = some d ↔
      IsDecimalDigits b ∧ d = decimalValue b ∧ 1 ≤ d ∧ d ≤ 10 ^ 10 := by
  unfold decodeDenominator
  rw [Option.bind_eq_some_iff]
  constructor
  · rintro ⟨n, hn, hd⟩
    obtain ⟨hb, rfl⟩ := decodeDecimal_eq_some_iff.mp hn
    split_ifs at hd with hr
    cases hd
    exact ⟨hb, rfl, hr⟩
  · rintro ⟨hb, rfl, hr⟩
    exact ⟨_, decodeDecimal_eq_some_iff.mpr ⟨hb, rfl⟩, ite_eq_left hr⟩

private lemma decodeNumerator_eq_some {a : List Char} {z : ℤ} (h : decodeNumerator a = some z) :
    ∃ (neg : Bool) (ds : List Char), a = (if neg then ['-'] else []) ++ ds ∧
      IsDecimalDigits ds ∧ decimalValue ds ≤ 10 ^ 10 ∧
        z = if neg then -(decimalValue ds : ℤ) else decimalValue ds := by
  unfold decodeNumerator at h
  split_ifs at h with hm
  · obtain ⟨n, hn, hz⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hb, rfl⟩ := decodeDecimal_eq_some_iff.mp hn
    split_ifs at hz with hr
    cases hz
    refine ⟨true, a.tail, ?_, hb, hr, rfl⟩
    cases a with
    | nil => simp at hm
    | cons c t => simp at hm; simp [hm]
  · obtain ⟨n, hn, hz⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hb, rfl⟩ := decodeDecimal_eq_some_iff.mp hn
    split_ifs at hz with hr
    cases hz
    exact ⟨false, a, by simp, hb, hr, rfl⟩

private lemma decodeNumerator_encode {neg : Bool} {ds : List Char} (hb : IsDecimalDigits ds)
    (hr : decimalValue ds ≤ 10 ^ 10) :
    decodeNumerator ((if neg then ['-'] else []) ++ ds) =
      some (if neg then -(decimalValue ds : ℤ) else decimalValue ds) := by
  have hdec := decodeDecimal_eq_some_iff.mpr ⟨hb, rfl⟩
  cases neg with
  | true =>
    simp only [decodeNumerator, ↓reduceIte, List.singleton_append, List.head?_cons,
      List.tail_cons, hdec, Option.bind_some, hr]
  | false =>
    obtain ⟨h1, -, hd⟩ := hb
    obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos h1)
    have hc : c ≠ '-' := by
      intro hc
      have := hd c (by simp)
      simp [hc] at this
    simp only [decodeNumerator, Bool.false_eq_true, ↓reduceIte, List.nil_append, List.head?_cons,
      Option.some.injEq, hc, hdec, Option.bind_some, hr]

private lemma splitOnChar_slash_encode (t : TraceToken) (h₁ : '/' ∉ t.numeratorDigits)
    (h₂ : '/' ∉ t.denominatorDigits) :
    splitOnChar '/' t.encode =
      [(if t.negative then ['-'] else []) ++ t.numeratorDigits, t.denominatorDigits] := by
  have h₀ : '/' ∉ (if t.negative then ['-'] else []) ++ t.numeratorDigits := by
    cases t.negative <;> simp [h₁]
  rw [splitOnChar_eq_splitOn, TraceToken.encode, List.splitOn_append_cons_self_of_not_mem h₀,
    List.splitOn_eq_singleton h₂]

/-- **Token decoding.** A token decodes exactly when it is the encoding of an admissible token, and
then to that token's value `numerator / denominator`. -/
lemma decodeToken_eq_some_iff {cs : List Char} {q : ℚ} :
    decodeToken cs = some q ↔ ∃ t : TraceToken, t.Admissible ∧ cs = t.encode ∧ q = t.value := by
  constructor
  · intro h
    unfold decodeToken at h
    split at h
    next a b hab =>
      obtain ⟨z, hz, hq⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hq
      obtain ⟨neg, ds, rfl, hb, hr, rfl⟩ := decodeNumerator_eq_some hz
      obtain ⟨hbd, rfl, hd1, hd2⟩ := decodeDenominator_eq_some_iff.mp hd
      refine ⟨⟨neg, ds, b⟩, ⟨hb, hbd, ?_, hd1, hd2⟩, ?_, rfl⟩
      · cases neg <;> simpa [TraceToken.numerator] using hr
      · have := List.intercalate_splitOn (xs := cs) '/'
        rw [← splitOnChar_eq_splitOn, hab] at this
        rw [← this]
        simp [TraceToken.encode]
    next => cases h
  · rintro ⟨t, ⟨hb, hbd, hr, hd1, hd2⟩, rfl, rfl⟩
    have hr' : decimalValue t.numeratorDigits ≤ 10 ^ 10 := by
      unfold TraceToken.numerator at hr
      split_ifs at hr <;> simpa using hr
    have hn : '/' ∉ t.numeratorDigits := not_mem_of_isDigit hb.2.2 (by decide)
    have hd : '/' ∉ t.denominatorDigits := not_mem_of_isDigit hbd.2.2 (by decide)
    unfold decodeToken
    rw [splitOnChar_slash_encode t hn hd]
    simp only
    rw [decodeNumerator_encode hb hr',
      decodeDenominator_eq_some_iff.mpr ⟨hbd, rfl, hd1, hd2⟩]
    simp [TraceToken.value, TraceToken.numerator, TraceToken.denominator]

private lemma mapM_decodeToken_encode {ts : List TraceToken} (h : ∀ t ∈ ts, t.Admissible) :
    (ts.map TraceToken.encode).mapM decodeToken = some (ts.map TraceToken.value) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have ht := decodeToken_eq_some_iff.mpr ⟨t, h t (by simp), rfl, rfl⟩
    rw [List.map_cons, List.mapM_cons, ht, ih fun u hu => h u (by simp [hu])]
    rfl

private lemma mapM_decodeToken_eq_some {fs : List (List Char)} {y : List ℚ}
    (h : fs.mapM decodeToken = some y) :
    ∃ ts : List TraceToken, (∀ t ∈ ts, t.Admissible) ∧ fs = ts.map TraceToken.encode ∧
      y = ts.map TraceToken.value := by
  induction fs generalizing y with
  | nil =>
    simp only [List.mapM_nil] at h
    cases h
    exact ⟨[], by simp, rfl, rfl⟩
  | cons f fs ih =>
    rw [List.mapM_cons] at h
    obtain ⟨q, hq, h'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨qs, hqs, h''⟩ := Option.bind_eq_some_iff.mp h'
    cases h''
    obtain ⟨t, ht, rfl, rfl⟩ := decodeToken_eq_some_iff.mp hq
    obtain ⟨ts, hts, rfl, rfl⟩ := ih hqs
    exact ⟨t :: ts, List.forall_mem_cons.mpr ⟨ht, hts⟩, rfl, rfl⟩

private lemma comma_not_mem_encode {t : TraceToken} (ht : t.Admissible) : ',' ∉ t.encode := by
  have hn : ',' ∉ t.numeratorDigits := not_mem_of_isDigit ht.1.2.2 (by decide)
  have hd : ',' ∉ t.denominatorDigits := not_mem_of_isDigit ht.2.1.2.2 (by decide)
  unfold TraceToken.encode
  cases t.negative <;> simp [hn, hd]

/-- **Trace decoding denotes exactly the token values.** An input decodes exactly when it has at
most 300 characters and is the comma-joined encoding of eleven admissible tokens, and then to the
list of their values, the rational trace that `checkThermalTrace` reads. -/
lemma decodeTrace_eq_some_iff {s : List Char} {y : List ℚ} :
    decodeTrace s = some y ↔ s.length ≤ 300 ∧ ∃ ts : List TraceToken, ts.length = 11 ∧
      (∀ t ∈ ts, t.Admissible) ∧ s = [','].intercalate (ts.map TraceToken.encode) ∧
        y = ts.map TraceToken.value := by
  constructor
  · intro h
    unfold decodeTrace at h
    split_ifs at h with hs
    obtain ⟨ts, hts, hfs, rfl⟩ := mapM_decodeToken_eq_some h
    refine ⟨hs.1, ts, ?_, hts, ?_, rfl⟩
    · rw [← List.length_map (f := TraceToken.encode), ← hfs, hs.2]
    · rw [← hfs, splitOnChar_eq_splitOn, List.intercalate_splitOn]
  · rintro ⟨hs, ts, h11, hts, rfl, rfl⟩
    have hsplit : splitOnChar ',' ([','].intercalate (ts.map TraceToken.encode)) =
        ts.map TraceToken.encode := by
      rw [splitOnChar_eq_splitOn]
      refine List.splitOn_intercalate ',' ?_ ?_
      · simp only [List.mem_map]
        rintro _ ⟨t, ht, rfl⟩
        exact comma_not_mem_encode (hts t ht)
      · intro h0
        have := congrArg List.length h0
        simp [h11] at this
    unfold decodeTrace
    simp only [hsplit, List.length_map, h11, hs, and_self, ↓reduceIte]
    exact mapM_decodeToken_encode hts

/-- **Explicit rejection.** An input is rejected exactly when it has more than 300 characters or
is not the comma-joined encoding of eleven admissible tokens: a wrong token count, a malformed
token or a violated bound. -/
lemma decodeTrace_eq_none_iff {s : List Char} :
    decodeTrace s = none ↔ ¬(s.length ≤ 300 ∧ ∃ ts : List TraceToken, ts.length = 11 ∧
      (∀ t ∈ ts, t.Admissible) ∧ s = [','].intercalate (ts.map TraceToken.encode)) := by
  constructor
  · rintro h ⟨hs, ts, h11, hts, hst⟩
    have := decodeTrace_eq_some_iff.mpr ⟨hs, ts, h11, hts, hst, rfl⟩
    rw [h] at this
    cases this
  · intro h
    cases hy : decodeTrace s with
    | none => rfl
    | some y =>
      obtain ⟨hs, ts, h11, hts, hst, -⟩ := decodeTrace_eq_some_iff.mp hy
      exact absurd ⟨hs, ts, h11, hts, hst⟩ h

/-! ## E. The proof-replay boundary -/

/-- **Decode, then check.** Accept an encoded trace exactly when it decodes and `checkThermalTrace`
accepts the decoded list. On a concrete encoding this is a closed Boolean computation, checked by
kernel reduction (`decide +kernel`). -/
def checkEncodedTrace (s : List Char) : Bool :=
  match decodeTrace s with
  | some y => checkThermalTrace y
  | none => false

/-- **Binding to the checker.** An encoded trace is accepted exactly when it decodes to a list that
`checkThermalTrace` accepts. -/
lemma checkEncodedTrace_eq_true_iff {s : List Char} :
    checkEncodedTrace s = true ↔ ∃ y, decodeTrace s = some y ∧ checkThermalTrace y = true := by
  unfold checkEncodedTrace
  cases decodeTrace s <;> simp

/-- **The accepted encodings.** An encoded trace is accepted exactly when it decodes to the trace
`(9 / 10) ^ j`, `j = 0, …, 10`. -/
lemma checkEncodedTrace_eq_true_iff_decodeTrace_eq {s : List Char} :
    checkEncodedTrace s = true ↔
      decodeTrace s = some ((List.range 11).map fun j => (9 / 10 : ℚ) ^ j) := by
  rw [checkEncodedTrace_eq_true_iff]
  constructor
  · rintro ⟨y, hy, hc⟩
    obtain ⟨hlen, hval⟩ := checkThermalTrace_rat hc
    rw [hy]
    congr 1
    refine List.ext_getElem (by simp [hlen]) fun i h₁ h₂ => ?_
    have hi : i ≤ 10 := by omega
    rw [List.getElem_map, List.getElem_range, ← hval i hi, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h₁, Option.getD_some]
  · intro h
    exact ⟨_, h, by decide +kernel⟩

/-- **Soundness of an accepted encoding.** The decoded list of an accepted encoding has eleven
entries and `y_j = (9 / 10) ^ j`, `j = 0, …, 10`, after the cast to the reals: the coefficients of
`T_j = T_amb + Δ y_j` for every `Δ`, including `Δ = 0`. -/
lemma checkEncodedTrace_sound {s : List Char} (h : checkEncodedTrace s = true) :
    ∃ y, decodeTrace s = some y ∧ y.length = 11 ∧
      ∀ j ≤ 10, ((y.getD j 0 : ℚ) : ℝ) = (9 / 10 : ℝ) ^ j := by
  obtain ⟨y, hy, hc⟩ := checkEncodedTrace_eq_true_iff.mp h
  exact ⟨y, hy, checkThermalTrace_sound hc⟩

end ThermalTraceCertificate
