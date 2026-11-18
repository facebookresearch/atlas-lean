/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.LTL.BuchiSize
public import Mathlib.Data.Nat.Pairing

/-!
# A linear-size token encoding of LTL formulas

Complexity statements about LTL take the formula as input, and its size must be measured
honestly: the encoding has one token per connective, so a formula of size `|φ|` has exactly
`|φ|` tokens (`Cslib.LTL.Formula.length_tokens`). Tokens are natural numbers `Nat.pair k a`,
with `k` the connective and `a` the atom (`0` for connectives without data), written in prefix
order. Parsing with fuel inverts the encoding (`Cslib.LTL.Formula.decodeList_tokens`).

This follows the token encoding of the linear-time μ-calculus in
`CSLibExt.Logics.Modal.LinearMuCalculus`.
-/

@[expose] public section

namespace Cslib.LTL.Formula

/-- **Token encoding of an LTL formula.** The prefix-order list of tokens of a formula over
atoms in `ℕ`: `Nat.pair 0 a` for the atom `a`, then `Nat.pair k 0` for truth (`k = 1`),
negation (`2`), conjunction (`3`), next (`4`) and until (`5`), each followed by the tokens of
its arguments. -/
def tokens : Formula ℕ → List ℕ
  | .atom a => [Nat.pair 0 a]
  | .top => [Nat.pair 1 0]
  | .not φ => Nat.pair 2 0 :: tokens φ
  | .and φ ψ => Nat.pair 3 0 :: tokens φ ++ tokens ψ
  | .next φ => Nat.pair 4 0 :: tokens φ
  | .until φ ψ => Nat.pair 5 0 :: tokens φ ++ tokens ψ

/-- **One token per occurrence.** The token encoding of an LTL formula has exactly as many
tokens as the formula has occurrences of atoms and connectives. -/
theorem length_tokens : ∀ φ : Formula ℕ, (tokens φ).length = φ.size
  | .atom _ => rfl
  | .top => rfl
  | .not φ => by simp [tokens, size, length_tokens φ]
  | .and φ ψ => by simp [tokens, size, length_tokens φ, length_tokens ψ]
  | .next φ => by simp [tokens, size, length_tokens φ]
  | .until φ ψ => by simp [tokens, size, length_tokens φ, length_tokens ψ]

/-- **Fuelled parsing of LTL tokens.** Reads one formula from the front of a token list and
returns it with the remaining tokens, or `none` if the fuel runs out or the list is not a
well-formed prefix. -/
def parseFuel : ℕ → List ℕ → Option (Formula ℕ × List ℕ)
  | 0, _ => none
  | fuel + 1, xs =>
    match xs with
    | [] => none
    | c :: rest =>
      match Nat.unpair c with
      | (0, a) => some (.atom a, rest)
      | (1, _) => some (.top, rest)
      | (2, _) =>
        match parseFuel fuel rest with
        | some (φ, rest') => some (.not φ, rest')
        | none => none
      | (3, _) =>
        match parseFuel fuel rest with
        | some (φ, rest') =>
          match parseFuel fuel rest' with
          | some (ψ, rest'') => some (.and φ ψ, rest'')
          | none => none
        | none => none
      | (4, _) =>
        match parseFuel fuel rest with
        | some (φ, rest') => some (.next φ, rest')
        | none => none
      | (5, _) =>
        match parseFuel fuel rest with
        | some (φ, rest') =>
          match parseFuel fuel rest' with
          | some (ψ, rest'') => some (.until φ ψ, rest'')
          | none => none
        | none => none
      | _ => none

/-- **Decoding a token list.** The formula whose token encoding is exactly the given list, if
there is one. -/
def decodeList (l : List ℕ) : Option (Formula ℕ) :=
  match parseFuel (l.length + 1) l with
  | some (φ, []) => some φ
  | _ => none

/-- **Parsing inverts the token encoding.** With fuel at least the number of tokens, parsing
the tokens of `φ` followed by any list returns `φ` and that list. -/
theorem parseFuel_tokens : ∀ (φ : Formula ℕ) (rest : List ℕ) (fuel : ℕ),
    (tokens φ).length ≤ fuel → parseFuel (fuel + 1) (tokens φ ++ rest) = some (φ, rest) := by
  intro φ
  induction φ with
  | atom a => intro rest fuel _; simp [parseFuel, tokens, Nat.unpair_pair]
  | top => intro rest fuel _; simp [parseFuel, tokens, Nat.unpair_pair]
  | not φ ih =>
    intro rest fuel hfuel
    cases fuel with
    | zero => simp only [tokens, List.length_cons] at hfuel; omega
    | succ fuel' =>
      have hφ : (tokens φ).length ≤ fuel' := by
        simp only [tokens, List.length_cons] at hfuel; omega
      unfold parseFuel
      simp only [tokens, Nat.unpair_pair, List.cons_append, ih, hφ]
  | and φ ψ ihφ ihψ =>
    intro rest fuel hfuel
    cases fuel with
    | zero => simp only [tokens, List.length_cons, List.length_append] at hfuel; omega
    | succ fuel' =>
      have hφ : (tokens φ).length ≤ fuel' := by
        simp only [tokens, List.length_cons, List.length_append] at hfuel; omega
      have hψ : (tokens ψ).length ≤ fuel' := by
        simp only [tokens, List.length_cons, List.length_append] at hfuel; omega
      unfold parseFuel
      simp only [tokens, Nat.unpair_pair, List.cons_append, List.append_assoc, ihφ, ihψ, hφ,
        hψ]
  | next φ ih =>
    intro rest fuel hfuel
    cases fuel with
    | zero => simp only [tokens, List.length_cons] at hfuel; omega
    | succ fuel' =>
      have hφ : (tokens φ).length ≤ fuel' := by
        simp only [tokens, List.length_cons] at hfuel; omega
      unfold parseFuel
      simp only [tokens, Nat.unpair_pair, List.cons_append, ih, hφ]
  | «until» φ ψ ihφ ihψ =>
    intro rest fuel hfuel
    cases fuel with
    | zero => simp only [tokens, List.length_cons, List.length_append] at hfuel; omega
    | succ fuel' =>
      have hφ : (tokens φ).length ≤ fuel' := by
        simp only [tokens, List.length_cons, List.length_append] at hfuel; omega
      have hψ : (tokens ψ).length ≤ fuel' := by
        simp only [tokens, List.length_cons, List.length_append] at hfuel; omega
      unfold parseFuel
      simp only [tokens, Nat.unpair_pair, List.cons_append, List.append_assoc, ihφ, ihψ, hφ,
        hψ]

/-- **Decoding inverts the token encoding.** Decoding the tokens of an LTL formula returns that
formula. -/
theorem decodeList_tokens (φ : Formula ℕ) : decodeList (tokens φ) = some φ := by
  have h := parseFuel_tokens φ [] (tokens φ).length le_rfl
  rw [List.append_nil] at h
  simp [decodeList, h]

end Cslib.LTL.Formula
