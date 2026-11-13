/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.TuringReducible
public import Mathlib.Computability.TuringDegree

@[expose] public section

/-!
# Turing degrees and the jump

Turing reducibility, Turing degrees, and the Turing jump (Soare,
*Recursively Enumerable Sets and Degrees*, Ch. I, §2 and Ch. III; Rogers,
*Theory of Recursive Functions and Effective Computability*, §9) organize
sets by their relative computability. This file defines oracle codes (the
`Nat.Partrec.Code` model extended with an oracle query), the Turing jump
as the diagonal halting set of the universal oracle machine, and
predicate-level Turing reducibility, equivalence, and degrees over
Mathlib's `TuringReducible` / `TuringDegree`. The Friedberg–Muchnik
theorem (incomparable RE degrees) and Post's jump characterisation of the
arithmetical hierarchy are registered as wanted theorems in
`WantedExt/TheoryOfComputation/FriedbergMuchnik.lean` and
`WantedExt/TheoryOfComputation/PostJumpCharacterisation.lean`.
-/

set_option autoImplicit false

namespace Cslib.Decidability

open scoped Computability

/-- **Oracle codes.** Oracle codes are the finite programs built from the basic codes
$\mathtt{zero}$, $\mathtt{succ}$, $\mathtt{left}$, $\mathtt{right}$ and $\mathtt{oracle}$ by the
binary constructors $\mathtt{pair}$, $\mathtt{comp}$ and $\mathtt{prec}$ and the unary constructor
$\mathtt{rfind}$. They are the codes for partial recursive functions (constant zero, successor,
the two unpairing projections, pairing, composition, primitive recursion and unbounded search)
extended by an instruction $\mathtt{oracle}$ that queries the oracle on its input.
Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, §2 (oracle computations). -/
inductive OracleCode where
  | zero : OracleCode
  | succ : OracleCode
  | left : OracleCode
  | right : OracleCode
  | pair : OracleCode → OracleCode → OracleCode
  | comp : OracleCode → OracleCode → OracleCode
  | prec : OracleCode → OracleCode → OracleCode
  | rfind : OracleCode → OracleCode
  | oracle : OracleCode

/-- **The Gödel numbering of oracle codes.** Write $\langle a, b \rangle$ for the pairing of
natural numbers equal to $b^2 + a$ if $a < b$ and to $a^2 + a + b$ otherwise. The code number
$\ulcorner c \urcorner$ of an oracle code $c$ is defined by recursion on $c$: $\mathsf{zero}$,
$\mathsf{succ}$, $\mathsf{left}$, $\mathsf{right}$ and $\mathsf{oracle}$ have code numbers
$\langle 0, 0 \rangle$, $\langle 1, 0 \rangle$, $\langle 2, 0 \rangle$, $\langle 3, 0 \rangle$ and
$\langle 8, 0 \rangle$; $\mathsf{pair}(a, b)$, $\mathsf{comp}(a, b)$ and $\mathsf{prec}(a, b)$
have code numbers $\langle 4, \langle \ulcorner a \urcorner, \ulcorner b \urcorner \rangle \rangle$,
$\langle 5, \langle \ulcorner a \urcorner, \ulcorner b \urcorner \rangle \rangle$ and
$\langle 6, \langle \ulcorner a \urcorner, \ulcorner b \urcorner \rangle \rangle$; and
$\mathsf{rfind}(a)$ has code number $\langle 7, \ulcorner a \urcorner \rangle$.

This numbering is an injection into $\mathbb{N}$.

Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.6 (Gödel numberings). -/
def encodeOracleCode : OracleCode → ℕ
  | .zero => Nat.pair 0 0
  | .succ => Nat.pair 1 0
  | .left => Nat.pair 2 0
  | .right => Nat.pair 3 0
  | .pair a b => Nat.pair 4 (Nat.pair (encodeOracleCode a) (encodeOracleCode b))
  | .comp a b => Nat.pair 5 (Nat.pair (encodeOracleCode a) (encodeOracleCode b))
  | .prec a b => Nat.pair 6 (Nat.pair (encodeOracleCode a) (encodeOracleCode b))
  | .rfind a => Nat.pair 7 (encodeOracleCode a)
  | .oracle => Nat.pair 8 0

/-- **The Gödel numbering of oracle codes is injective.**
Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.6 (Gödel numberings). -/
theorem encodeOracleCode_injective : Function.Injective encodeOracleCode := by
  intro a b hab
  induction a generalizing b with
  | zero => cases b <;> simp_all [encodeOracleCode, Nat.pair_eq_pair]
  | succ => cases b <;> simp_all [encodeOracleCode, Nat.pair_eq_pair]
  | left => cases b <;> simp_all [encodeOracleCode, Nat.pair_eq_pair]
  | right => cases b <;> simp_all [encodeOracleCode, Nat.pair_eq_pair]
  | oracle => cases b <;> simp_all [encodeOracleCode, Nat.pair_eq_pair]
  | pair a₁ a₂ ih₁ ih₂ =>
    cases b <;> simp only [encodeOracleCode, Nat.pair_eq_pair] at hab ⊢ <;>
      first
        | exact absurd hab.1 (by decide)
        | exact congrArg₂ OracleCode.pair (ih₁ hab.2.1) (ih₂ hab.2.2)
  | comp a₁ a₂ ih₁ ih₂ =>
    cases b <;> simp only [encodeOracleCode, Nat.pair_eq_pair] at hab ⊢ <;>
      first
        | exact absurd hab.1 (by decide)
        | exact congrArg₂ OracleCode.comp (ih₁ hab.2.1) (ih₂ hab.2.2)
  | prec a₁ a₂ ih₁ ih₂ =>
    cases b <;> simp only [encodeOracleCode, Nat.pair_eq_pair] at hab ⊢ <;>
      first
        | exact absurd hab.1 (by decide)
        | exact congrArg₂ OracleCode.prec (ih₁ hab.2.1) (ih₂ hab.2.2)
  | rfind a ih =>
    cases b <;> simp only [encodeOracleCode, Nat.pair_eq_pair] at hab ⊢ <;>
      first
        | exact absurd hab.1 (by decide)
        | exact congrArg OracleCode.rfind (ih hab.2)

/-- **Pairing is at least its first argument.** Let $\langle a, b \rangle$ denote the pairing of
natural numbers, equal to $b^2 + a$ if $a < b$ and to $a^2 + a + b$ otherwise. For all natural
numbers $a$ and $b$, $a \le \langle a, b \rangle$.
Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.3 (pairing functions). -/
theorem pair_ge_fst (a b : ℕ) : a ≤ Nat.pair a b := by
  unfold Nat.pair
  split_ifs <;> omega

/-- **Pairing is at least its second argument.** Let $\langle a, b \rangle$ denote the pairing of
natural numbers, equal to $b^2 + a$ if $a < b$ and to $a^2 + a + b$ otherwise. For all natural
numbers $a$ and $b$, $b \le \langle a, b \rangle$.
Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.3 (pairing functions). -/
theorem pair_ge_snd (a b : ℕ) : b ≤ Nat.pair a b := by
  unfold Nat.pair
  split_ifs with h
  · have hb : b ≤ b * b := Nat.le_mul_self b
    omega
  · have hb : b ≤ a := Nat.le_of_not_lt h
    omega

/-- **Pairing with $4$ strictly increases the second argument.** Let $\langle a, b \rangle$ denote
the pairing of natural numbers, equal to $b^2 + a$ if $a < b$ and to $a^2 + a + b$ otherwise.
For every natural number $x$, $x < \langle 4, x \rangle$.
Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.3 (pairing functions). -/
theorem pair_four_gt (x : ℕ) : x < Nat.pair 4 x := by
  unfold Nat.pair
  split_ifs with h
  · have hx : x ≤ x * x := Nat.le_mul_self x
    omega
  · omega

/-- **Pairing with a positive first argument strictly increases the second.** Let
$\langle a, b \rangle$ denote the pairing of natural numbers, equal to $b^2 + a$ if $a < b$ and to
$a^2 + a + b$ otherwise. For all natural numbers $t$ and $x$ with $t \ge 1$,
$x < \langle t, x \rangle$.
Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.3 (pairing functions). -/
theorem pair_gt_snd_of_pos {t x : ℕ} (ht : 1 ≤ t) : x < Nat.pair t x := by
  unfold Nat.pair
  split_ifs with h
  · have hx : x ≤ x * x := Nat.le_mul_self x
    by_cases hx0 : x = 0
    · omega
    · have hx1 : 1 ≤ x := Nat.one_le_iff_ne_zero.2 hx0
      omega
  · have hpos : 0 < t * t := Nat.mul_pos ht ht
    omega

/-- **The first unpairing component is at most the number.** Let
$\mathrm{pair} : \mathbb{N} \times \mathbb{N} \to \mathbb{N}$ be the pairing bijection with
$\mathrm{pair}(a, b) = b^2 + a$ if $a < b$ and $\mathrm{pair}(a, b) = a^2 + a + b$ otherwise.
For every natural number $n$, the first component of $\mathrm{pair}^{-1}(n)$ is at most $n$.

Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.3 (pairing functions). -/
theorem unpair_fst_le (n : ℕ) : n.unpair.1 ≤ n := by
  conv_rhs => rw [← Nat.pair_unpair n]
  exact pair_ge_fst _ _

/-- **The second unpairing component is at most the number.** Let
$\mathrm{pair} : \mathbb{N} \times \mathbb{N} \to \mathbb{N}$ be the pairing bijection with
$\mathrm{pair}(a, b) = b^2 + a$ if $a < b$ and $\mathrm{pair}(a, b) = a^2 + a + b$ otherwise.
For every natural number $n$, the second component of $\mathrm{pair}^{-1}(n)$ is at most $n$.

Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.3 (pairing functions). -/
theorem unpair_snd_le (n : ℕ) : n.unpair.2 ≤ n := by
  conv_rhs => rw [← Nat.pair_unpair n]
  exact pair_ge_snd _ _

/-- **Depth of an oracle code**: leaves have depth `0`; each constructor adds
one to the maximum depth of its children.
Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.6 (Gödel numberings; size bounds). -/
def oracleCodeDepth : OracleCode → ℕ
  | .zero => 0
  | .succ => 0
  | .left => 0
  | .right => 0
  | .oracle => 0
  | .pair a b => max (oracleCodeDepth a) (oracleCodeDepth b) + 1
  | .comp a b => max (oracleCodeDepth a) (oracleCodeDepth b) + 1
  | .prec a b => max (oracleCodeDepth a) (oracleCodeDepth b) + 1
  | .rfind a => oracleCodeDepth a + 1

/-- **Fuel-indexed decoder of oracle codes.** Write $\langle a, b \rangle$ for the pairing
bijection $\mathbb{N} \times \mathbb{N} \to \mathbb{N}$ of the Gödel numbering. Given a fuel $f$,
a tag $t$ and a payload $p$, the decoder either returns an oracle code or fails; to decode a
number $n = \langle n_1, n_2 \rangle$ with fuel $f$ means to run it with fuel $f$, tag $n_1$ and
payload $n_2$. With fuel $0$ it fails. With fuel $f + 1$, writing $p = \langle p_1, p_2 \rangle$:
if $p = 0$ and $t$ is $0$, $1$, $2$, $3$ or $8$, it returns the instruction zero, successor, left
projection, right projection or oracle query respectively; if $t$ is $4$, $5$ or $6$, it decodes
$p_1$ and $p_2$ with fuel $f$ and, when these give codes $a$ and $b$, returns the pairing,
composition or primitive recursion code built from $a$ and $b$ respectively, failing otherwise;
if $t = 7$, it decodes $p$ with fuel $f$ and, when this gives a code $a$, returns the unbounded
search code built from $a$, failing otherwise; in all other cases it fails.

The recursion is structural in the fuel and uses no classical choice, so the decoder is a
computable function; with enough fuel it inverts the Gödel numbering of oracle codes.

Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.6 (Gödel numberings; decoding). -/
def decodeOracleCodeFuel : ℕ → ℕ → ℕ → Option OracleCode
  | 0, _, _ => none
  | fuel + 1, tag, payload =>
    if tag = 0 ∧ payload = 0 then some .zero
    else if tag = 1 ∧ payload = 0 then some .succ
    else if tag = 2 ∧ payload = 0 then some .left
    else if tag = 3 ∧ payload = 0 then some .right
    else if tag = 4 then
      match decodeOracleCodeFuel fuel payload.unpair.1.unpair.1
          payload.unpair.1.unpair.2,
        decodeOracleCodeFuel fuel payload.unpair.2.unpair.1
          payload.unpair.2.unpair.2 with
      | some a, some b => some (.pair a b)
      | _, _ => none
    else if tag = 5 then
      match decodeOracleCodeFuel fuel payload.unpair.1.unpair.1
          payload.unpair.1.unpair.2,
        decodeOracleCodeFuel fuel payload.unpair.2.unpair.1
          payload.unpair.2.unpair.2 with
      | some a, some b => some (.comp a b)
      | _, _ => none
    else if tag = 6 then
      match decodeOracleCodeFuel fuel payload.unpair.1.unpair.1
          payload.unpair.1.unpair.2,
        decodeOracleCodeFuel fuel payload.unpair.2.unpair.1
          payload.unpair.2.unpair.2 with
      | some a, some b => some (.prec a b)
      | _, _ => none
    else if tag = 7 then
      match decodeOracleCodeFuel fuel payload.unpair.1 payload.unpair.2 with
      | some a => some (.rfind a)
      | none => none
    else if tag = 8 ∧ payload = 0 then some .oracle
    else none

/-- **The fuel-indexed decoder inverts the encoder.** Write $\langle a, b \rangle$ for the pairing
bijection $\mathbb{N} \times \mathbb{N} \to \mathbb{N}$ of the Gödel numbering. Let $c$ be an
oracle code with Gödel number $\langle t, p \rangle$. For every fuel $f$ strictly greater than the
depth of $c$, the fuel-indexed decoder with fuel $f$, tag $t$ and payload $p$ returns $c$.

Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.6 (Gödel numberings; decoding). -/
theorem decodeOracleCodeFuel_complete : ∀ (c : OracleCode) (fuel : ℕ),
    oracleCodeDepth c < fuel →
    decodeOracleCodeFuel fuel (encodeOracleCode c).unpair.1
      (encodeOracleCode c).unpair.2 = some c := by
  intro c
  induction c with
  | zero => intro fuel h; cases fuel with
    | zero => omega
    | succ fuel => simp [encodeOracleCode, Nat.unpair_pair, decodeOracleCodeFuel]
  | succ => intro fuel h; cases fuel with
    | zero => omega
    | succ fuel => simp [encodeOracleCode, Nat.unpair_pair, decodeOracleCodeFuel]
  | left => intro fuel h; cases fuel with
    | zero => omega
    | succ fuel => simp [encodeOracleCode, Nat.unpair_pair, decodeOracleCodeFuel]
  | right => intro fuel h; cases fuel with
    | zero => omega
    | succ fuel => simp [encodeOracleCode, Nat.unpair_pair, decodeOracleCodeFuel]
  | oracle => intro fuel h; cases fuel with
    | zero => omega
    | succ fuel => simp [encodeOracleCode, Nat.unpair_pair, decodeOracleCodeFuel]
  | pair a b iha ihb =>
    intro fuel h
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hdepth : oracleCodeDepth (.pair a b) = max (oracleCodeDepth a)
          (oracleCodeDepth b) + 1 := rfl
      have ha : oracleCodeDepth a < fuel := by
        have h1 := Nat.le_max_left (oracleCodeDepth a) (oracleCodeDepth b)
        omega
      have hb : oracleCodeDepth b < fuel := by
        have h1 := Nat.le_max_right (oracleCodeDepth a) (oracleCodeDepth b)
        omega
      have e1 := iha fuel ha
      have e2 := ihb fuel hb
      simp [encodeOracleCode, Nat.unpair_pair, decodeOracleCodeFuel, e1, e2]
  | comp a b iha ihb =>
    intro fuel h
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hdepth : oracleCodeDepth (.comp a b) = max (oracleCodeDepth a)
          (oracleCodeDepth b) + 1 := rfl
      have ha : oracleCodeDepth a < fuel := by
        have h1 := Nat.le_max_left (oracleCodeDepth a) (oracleCodeDepth b)
        omega
      have hb : oracleCodeDepth b < fuel := by
        have h1 := Nat.le_max_right (oracleCodeDepth a) (oracleCodeDepth b)
        omega
      have e1 := iha fuel ha
      have e2 := ihb fuel hb
      simp [encodeOracleCode, Nat.unpair_pair, decodeOracleCodeFuel, e1, e2]
  | prec a b iha ihb =>
    intro fuel h
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hdepth : oracleCodeDepth (.prec a b) = max (oracleCodeDepth a)
          (oracleCodeDepth b) + 1 := rfl
      have ha : oracleCodeDepth a < fuel := by
        have h1 := Nat.le_max_left (oracleCodeDepth a) (oracleCodeDepth b)
        omega
      have hb : oracleCodeDepth b < fuel := by
        have h1 := Nat.le_max_right (oracleCodeDepth a) (oracleCodeDepth b)
        omega
      have e1 := iha fuel ha
      have e2 := ihb fuel hb
      simp [encodeOracleCode, Nat.unpair_pair, decodeOracleCodeFuel, e1, e2]
  | rfind a ih =>
    intro fuel h
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hdepth : oracleCodeDepth (.rfind a) = oracleCodeDepth a + 1 := rfl
      have ha : oracleCodeDepth a < fuel := by omega
      have e1 := ih fuel ha
      simp [encodeOracleCode, Nat.unpair_pair, decodeOracleCodeFuel, e1]

/-- **Decoder soundness.** Write $\langle a, b \rangle$ for the pairing bijection
$\mathbb{N} \times \mathbb{N} \to \mathbb{N}$ of the Gödel numbering. For every fuel $f$, tag
$t$, payload $p$ and oracle code $c$, if the fuel-indexed decoder with fuel $f$, tag $t$ and
payload $p$ returns $c$, then the Gödel number of $c$ is $\langle t, p \rangle$.

Together with the fact that the fuel-indexed decoder inverts the encoder at any fuel above the
code depth, this says that the decoder is exactly the inverse of the Gödel numbering on its image.

Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.6 (Gödel numberings; decoding). -/
theorem decodeOracleCodeFuel_sound : ∀ (fuel : ℕ) (tag payload : ℕ)
    (c : OracleCode),
    decodeOracleCodeFuel fuel tag payload = some c →
    encodeOracleCode c = Nat.pair tag payload := by
  intro fuel
  induction fuel with
  | zero => intro tag payload c h; simp [decodeOracleCodeFuel] at h
  | succ fuel ih =>
    intro tag payload c h
    have htag : tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 3 ∨ tag = 4 ∨ tag = 5 ∨
        tag = 6 ∨ tag = 7 ∨ tag = 8 ∨ 8 < tag := by omega
    rcases htag with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hgt
    · by_cases hp : payload = 0
      · simp [decodeOracleCodeFuel, hp] at h
        obtain rfl := h.symm
        simp [encodeOracleCode, hp]
      · simp [decodeOracleCodeFuel, hp] at h
    · by_cases hp : payload = 0
      · simp [decodeOracleCodeFuel, hp] at h
        obtain rfl := h.symm
        simp [encodeOracleCode, hp]
      · simp [decodeOracleCodeFuel, hp] at h
    · by_cases hp : payload = 0
      · simp [decodeOracleCodeFuel, hp] at h
        obtain rfl := h.symm
        simp [encodeOracleCode, hp]
      · simp [decodeOracleCodeFuel, hp] at h
    · by_cases hp : payload = 0
      · simp [decodeOracleCodeFuel, hp] at h
        obtain rfl := h.symm
        simp [encodeOracleCode, hp]
      · simp [decodeOracleCodeFuel, hp] at h
    · simp only [decodeOracleCodeFuel] at h
      rw [if_true] at h
      cases h1 : decodeOracleCodeFuel fuel payload.unpair.1.unpair.1
          payload.unpair.1.unpair.2 with
      | none => rw [h1] at h; simp at h
      | some a =>
        cases h2 : decodeOracleCodeFuel fuel payload.unpair.2.unpair.1
            payload.unpair.2.unpair.2 with
        | none => rw [h1, h2] at h; simp at h
        | some b =>
          rw [h1, h2] at h
          obtain rfl := Option.some_inj.1 h
          have ha := ih _ _ _ h1
          have hb := ih _ _ _ h2
          have e1 : encodeOracleCode a = payload.unpair.1 := by
            rw [ha]; exact Nat.pair_unpair _
          have e2 : encodeOracleCode b = payload.unpair.2 := by
            rw [hb]; exact Nat.pair_unpair _
          show encodeOracleCode (OracleCode.pair a b) = Nat.pair 4 payload
          simp [encodeOracleCode, e1, e2, Nat.pair_unpair]
    · simp only [decodeOracleCodeFuel] at h
      rw [if_true] at h
      cases h1 : decodeOracleCodeFuel fuel payload.unpair.1.unpair.1
          payload.unpair.1.unpair.2 with
      | none => rw [h1] at h; simp at h
      | some a =>
        cases h2 : decodeOracleCodeFuel fuel payload.unpair.2.unpair.1
            payload.unpair.2.unpair.2 with
        | none => rw [h1, h2] at h; simp at h
        | some b =>
          rw [h1, h2] at h
          obtain rfl := Option.some_inj.1 h
          have ha := ih _ _ _ h1
          have hb := ih _ _ _ h2
          have e1 : encodeOracleCode a = payload.unpair.1 := by
            rw [ha]; exact Nat.pair_unpair _
          have e2 : encodeOracleCode b = payload.unpair.2 := by
            rw [hb]; exact Nat.pair_unpair _
          show encodeOracleCode (OracleCode.comp a b) = Nat.pair 5 payload
          simp [encodeOracleCode, e1, e2, Nat.pair_unpair]
    · simp only [decodeOracleCodeFuel] at h
      rw [if_true] at h
      cases h1 : decodeOracleCodeFuel fuel payload.unpair.1.unpair.1
          payload.unpair.1.unpair.2 with
      | none => rw [h1] at h; simp at h
      | some a =>
        cases h2 : decodeOracleCodeFuel fuel payload.unpair.2.unpair.1
            payload.unpair.2.unpair.2 with
        | none => rw [h1, h2] at h; simp at h
        | some b =>
          rw [h1, h2] at h
          obtain rfl := Option.some_inj.1 h
          have ha := ih _ _ _ h1
          have hb := ih _ _ _ h2
          have e1 : encodeOracleCode a = payload.unpair.1 := by
            rw [ha]; exact Nat.pair_unpair _
          have e2 : encodeOracleCode b = payload.unpair.2 := by
            rw [hb]; exact Nat.pair_unpair _
          show encodeOracleCode (OracleCode.prec a b) = Nat.pair 6 payload
          simp [encodeOracleCode, e1, e2, Nat.pair_unpair]
    · simp only [decodeOracleCodeFuel] at h
      rw [if_true] at h
      cases hdec : decodeOracleCodeFuel fuel payload.unpair.1 payload.unpair.2 with
      | none => rw [hdec] at h; simp at h
      | some a =>
        rw [hdec] at h
        obtain rfl := Option.some_inj.1 h
        have ha := ih _ _ _ hdec
        have e : encodeOracleCode a = payload := by
          rw [ha]; exact Nat.pair_unpair _
        show encodeOracleCode (OracleCode.rfind a) = Nat.pair 7 payload
        simp [encodeOracleCode, e]
    · by_cases hp : payload = 0
      · simp [decodeOracleCodeFuel, hp] at h
        obtain rfl := h.symm
        simp [encodeOracleCode, hp]
      · simp [decodeOracleCodeFuel, hp] at h
    · simp only [decodeOracleCodeFuel] at h
      have h0 : ¬(tag = 0 ∧ payload = 0) := by omega
      have h1 : ¬(tag = 1 ∧ payload = 0) := by omega
      have h2 : ¬(tag = 2 ∧ payload = 0) := by omega
      have h3 : ¬(tag = 3 ∧ payload = 0) := by omega
      have h4 : ¬tag = 4 := by omega
      have h5 : ¬tag = 5 := by omega
      have h6 : ¬tag = 6 := by omega
      have h7 : ¬tag = 7 := by omega
      have h8 : ¬(tag = 8 ∧ payload = 0) := by omega
      rw [ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
        ite_eq_right h4, ite_eq_right h5, ite_eq_right h6, ite_eq_right h7,
        ite_eq_right h8] at h
      simp at h

/-- **Depth is bounded by the code number.** For every oracle code $c$, the depth of $c$ is at most
the code number of $c$ under the Gödel numbering of oracle codes.

Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.6 (Gödel numberings; size bounds). -/
theorem oracleCodeDepth_le_encode : ∀ c : OracleCode,
    oracleCodeDepth c ≤ encodeOracleCode c := by
  intro c
  induction c with
  | zero => simp [oracleCodeDepth, encodeOracleCode]
  | succ => simp [oracleCodeDepth, encodeOracleCode]
  | left => simp [oracleCodeDepth, encodeOracleCode]
  | right => simp [oracleCodeDepth, encodeOracleCode]
  | oracle => simp [oracleCodeDepth, encodeOracleCode]
  | pair a b iha ihb =>
    show max (oracleCodeDepth a) (oracleCodeDepth b) + 1 ≤
      Nat.pair 4 (Nat.pair (encodeOracleCode a) (encodeOracleCode b))
    have h1 : max (oracleCodeDepth a) (oracleCodeDepth b) ≤
        Nat.pair (encodeOracleCode a) (encodeOracleCode b) := by
      have hge1 := pair_ge_fst (encodeOracleCode a) (encodeOracleCode b)
      have hge2 := pair_ge_snd (encodeOracleCode a) (encodeOracleCode b)
      omega
    have h2 := pair_gt_snd_of_pos (t := 4)
      (x := Nat.pair (encodeOracleCode a) (encodeOracleCode b)) (by decide)
    omega
  | comp a b iha ihb =>
    show max (oracleCodeDepth a) (oracleCodeDepth b) + 1 ≤
      Nat.pair 5 (Nat.pair (encodeOracleCode a) (encodeOracleCode b))
    have h1 : max (oracleCodeDepth a) (oracleCodeDepth b) ≤
        Nat.pair (encodeOracleCode a) (encodeOracleCode b) := by
      have hge1 := pair_ge_fst (encodeOracleCode a) (encodeOracleCode b)
      have hge2 := pair_ge_snd (encodeOracleCode a) (encodeOracleCode b)
      omega
    have h2 := pair_gt_snd_of_pos (t := 5)
      (x := Nat.pair (encodeOracleCode a) (encodeOracleCode b)) (by decide)
    omega
  | prec a b iha ihb =>
    show max (oracleCodeDepth a) (oracleCodeDepth b) + 1 ≤
      Nat.pair 6 (Nat.pair (encodeOracleCode a) (encodeOracleCode b))
    have h1 : max (oracleCodeDepth a) (oracleCodeDepth b) ≤
        Nat.pair (encodeOracleCode a) (encodeOracleCode b) := by
      have hge1 := pair_ge_fst (encodeOracleCode a) (encodeOracleCode b)
      have hge2 := pair_ge_snd (encodeOracleCode a) (encodeOracleCode b)
      omega
    have h2 := pair_gt_snd_of_pos (t := 6)
      (x := Nat.pair (encodeOracleCode a) (encodeOracleCode b)) (by decide)
    omega
  | rfind a ih =>
    show oracleCodeDepth a + 1 ≤ Nat.pair 7 (encodeOracleCode a)
    have h2 := pair_gt_snd_of_pos (t := 7) (x := encodeOracleCode a) (by decide)
    omega

/-- **Decoding oracle codes.** The computable decoder for the Gödel numbering of oracle codes
sends a natural number $n$ to the result of the fuel-indexed decoder with fuel $n + 1$, tag $n_1$
and payload $n_2$, where $(n_1, n_2)$ is the unpairing of $n$; the result is either an oracle code
or undefined. The fuel $n + 1$ is more than enough, since the depth of an oracle code is at most
its code number.

Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.6 (Gödel numberings; decoding). -/
def decodeOracleCode (n : ℕ) : Option OracleCode :=
  decodeOracleCodeFuel (n + 1) n.unpair.1 n.unpair.2

/-- **The computable decoder inverts the encoder.** For every oracle code $c$, the computable
decoder applied to the Gödel number of $c$ returns $c$.

Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.6 (Gödel numberings; decoding). -/
theorem decodeOracleCode_encode (c : OracleCode) :
    decodeOracleCode (encodeOracleCode c) = some c :=
  decodeOracleCodeFuel_complete c _ (by
    have h := oracleCodeDepth_le_encode c
    omega)


/-- **The fuel-indexed decoder agrees with the total decoder** whenever the
code number is below the fuel: decoding `(tag, payload)` at any fuel above
the code number gives the same result as decoding the code number itself.
Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.6 (Gödel numberings; decoding). -/
theorem decodeOracleCodeFuel_eq_decode {fuel tag payload : ℕ}
    (h : Nat.pair tag payload < fuel) :
    decodeOracleCodeFuel fuel tag payload =
      decodeOracleCode (Nat.pair tag payload) := by
  cases hdec : decodeOracleCodeFuel fuel tag payload with
  | none =>
    by_contra hne
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp (Ne.symm hne)
    have hcomp : decodeOracleCodeFuel (Nat.pair tag payload + 1) tag payload =
        some c := by
      have hc' := hc
      unfold decodeOracleCode at hc'
      rw [Nat.unpair_pair] at hc'
      exact hc'
    have henc := decodeOracleCodeFuel_sound _ _ _ _ hcomp
    have hle : oracleCodeDepth c ≤ Nat.pair tag payload := by
      rw [← henc]; exact oracleCodeDepth_le_encode c
    have hcomp2 := decodeOracleCodeFuel_complete c fuel (by omega)
    rw [henc] at hcomp2
    rw [Nat.unpair_pair] at hcomp2
    rw [hdec] at hcomp2
    exact absurd hcomp2 (by simp)
  | some c =>
    have henc := decodeOracleCodeFuel_sound _ _ _ _ hdec
    have hcomp := decodeOracleCodeFuel_complete c (Nat.pair tag payload + 1) (by
      have hle : oracleCodeDepth c ≤ Nat.pair tag payload := by
        rw [← henc]; exact oracleCodeDepth_le_encode c
      omega)
    rw [henc] at hcomp
    rw [Nat.unpair_pair] at hcomp
    show some c = decodeOracleCode (Nat.pair tag payload)
    unfold decodeOracleCode
    rw [Nat.unpair_pair]
    exact hcomp.symm

/-- **The decoder, by cases on the tag.** Write $\langle t, p \rangle$ for the pairing of natural
numbers used by the Gödel numbering of oracle codes, $(p_1, p_2)$ for the unpairing of $p$ (so that
$\langle p_1, p_2 \rangle = p$), and $\mathrm{dec}(n)$ for the result of the computable decoder on
$n$, which is either an oracle code or undefined. Then for all natural numbers $t$ and $p$, the
value $\mathrm{dec}\langle t, p \rangle$ is: $\mathsf{zero}$, $\mathsf{succ}$, $\mathsf{left}$,
$\mathsf{right}$ or $\mathsf{oracle}$ when $p = 0$ and $t$ is $0$, $1$, $2$, $3$ or $8$
respectively; $\mathsf{pair}(a, b)$, $\mathsf{comp}(a, b)$ or $\mathsf{prec}(a, b)$ when $t$ is
$4$, $5$ or $6$ respectively and $\mathrm{dec}(p_1) = a$ and $\mathrm{dec}(p_2) = b$ are both
defined; $\mathsf{rfind}(a)$ when $t = 7$ and $\mathrm{dec}(p) = a$ is defined; and undefined in
every other case.

For $t \in \{4, 5, 6, 7\}$ the numbers decoded on the right, $p_1$, $p_2$ and $p$, are at most $p$
and hence strictly below $\langle t, p \rangle$, so this is a recursion on the code number.

Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.6 (Gödel numberings; decoding). -/
theorem decodeOracleCode_pair (tag payload : ℕ) :
    decodeOracleCode (Nat.pair tag payload) =
      if tag = 0 ∧ payload = 0 then some .zero
      else if tag = 1 ∧ payload = 0 then some .succ
      else if tag = 2 ∧ payload = 0 then some .left
      else if tag = 3 ∧ payload = 0 then some .right
      else if tag = 4 then
        match decodeOracleCode payload.unpair.1, decodeOracleCode payload.unpair.2 with
        | some a, some b => some (.pair a b)
        | _, _ => none
      else if tag = 5 then
        match decodeOracleCode payload.unpair.1, decodeOracleCode payload.unpair.2 with
        | some a, some b => some (.comp a b)
        | _, _ => none
      else if tag = 6 then
        match decodeOracleCode payload.unpair.1, decodeOracleCode payload.unpair.2 with
        | some a, some b => some (.prec a b)
        | _, _ => none
      else if tag = 7 then
        match decodeOracleCode payload with
        | some a => some (.rfind a)
        | none => none
      else if tag = 8 ∧ payload = 0 then some .oracle
      else none := by
  have htag : tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 3 ∨ tag = 4 ∨ tag = 5 ∨
      tag = 6 ∨ tag = 7 ∨ tag = 8 ∨ 8 < tag := by omega
  rcases htag with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hgt
  · by_cases hp : payload = 0
    · subst hp
      simp [decodeOracleCode, decodeOracleCodeFuel, Nat.unpair_pair]
    · simp [decodeOracleCode, decodeOracleCodeFuel, Nat.unpair_pair, hp]
  · by_cases hp : payload = 0
    · subst hp
      simp [decodeOracleCode, decodeOracleCodeFuel, Nat.unpair_pair]
    · simp [decodeOracleCode, decodeOracleCodeFuel, Nat.unpair_pair, hp]
  · by_cases hp : payload = 0
    · subst hp
      simp [decodeOracleCode, decodeOracleCodeFuel, Nat.unpair_pair]
    · simp [decodeOracleCode, decodeOracleCodeFuel, Nat.unpair_pair, hp]
  · by_cases hp : payload = 0
    · subst hp
      simp [decodeOracleCode, decodeOracleCodeFuel, Nat.unpair_pair]
    · simp [decodeOracleCode, decodeOracleCodeFuel, Nat.unpair_pair, hp]
  · have hsub1 : Nat.pair payload.unpair.1.unpair.1 payload.unpair.1.unpair.2 <
        Nat.pair 4 payload := by
      have h1 : payload.unpair.1 ≤ payload := unpair_fst_le _
      have h2 : payload < Nat.pair 4 payload :=
        pair_gt_snd_of_pos (by decide : 1 ≤ 4)
      rw [Nat.pair_unpair]
      omega
    have hsub2 : Nat.pair payload.unpair.2.unpair.1 payload.unpair.2.unpair.2 <
        Nat.pair 4 payload := by
      have h1 : payload.unpair.2 ≤ payload := unpair_snd_le _
      have h2 : payload < Nat.pair 4 payload :=
        pair_gt_snd_of_pos (by decide : 1 ≤ 4)
      rw [Nat.pair_unpair]
      omega
    have e1 := decodeOracleCodeFuel_eq_decode (fuel := Nat.pair 4 payload)
      (tag := payload.unpair.1.unpair.1) (payload := payload.unpair.1.unpair.2) hsub1
    have e2 := decodeOracleCodeFuel_eq_decode (fuel := Nat.pair 4 payload)
      (tag := payload.unpair.2.unpair.1) (payload := payload.unpair.2.unpair.2) hsub2
    rw [Nat.pair_unpair] at e1 e2
    conv_lhs => unfold decodeOracleCode
    conv_lhs => simp only [Nat.unpair_pair, decodeOracleCodeFuel, ite_true]
    rw [e1, e2]
    simp
  · have hsub1 : Nat.pair payload.unpair.1.unpair.1 payload.unpair.1.unpair.2 <
        Nat.pair 5 payload := by
      have h1 : payload.unpair.1 ≤ payload := unpair_fst_le _
      have h2 : payload < Nat.pair 5 payload :=
        pair_gt_snd_of_pos (by decide : 1 ≤ 5)
      rw [Nat.pair_unpair]
      omega
    have hsub2 : Nat.pair payload.unpair.2.unpair.1 payload.unpair.2.unpair.2 <
        Nat.pair 5 payload := by
      have h1 : payload.unpair.2 ≤ payload := unpair_snd_le _
      have h2 : payload < Nat.pair 5 payload :=
        pair_gt_snd_of_pos (by decide : 1 ≤ 5)
      rw [Nat.pair_unpair]
      omega
    have e1 := decodeOracleCodeFuel_eq_decode (fuel := Nat.pair 5 payload)
      (tag := payload.unpair.1.unpair.1) (payload := payload.unpair.1.unpair.2) hsub1
    have e2 := decodeOracleCodeFuel_eq_decode (fuel := Nat.pair 5 payload)
      (tag := payload.unpair.2.unpair.1) (payload := payload.unpair.2.unpair.2) hsub2
    rw [Nat.pair_unpair] at e1 e2
    conv_lhs => unfold decodeOracleCode
    conv_lhs => simp only [Nat.unpair_pair, decodeOracleCodeFuel, ite_true]
    rw [e1, e2]
    simp
  · have hsub1 : Nat.pair payload.unpair.1.unpair.1 payload.unpair.1.unpair.2 <
        Nat.pair 6 payload := by
      have h1 : payload.unpair.1 ≤ payload := unpair_fst_le _
      have h2 : payload < Nat.pair 6 payload :=
        pair_gt_snd_of_pos (by decide : 1 ≤ 6)
      rw [Nat.pair_unpair]
      omega
    have hsub2 : Nat.pair payload.unpair.2.unpair.1 payload.unpair.2.unpair.2 <
        Nat.pair 6 payload := by
      have h1 : payload.unpair.2 ≤ payload := unpair_snd_le _
      have h2 : payload < Nat.pair 6 payload :=
        pair_gt_snd_of_pos (by decide : 1 ≤ 6)
      rw [Nat.pair_unpair]
      omega
    have e1 := decodeOracleCodeFuel_eq_decode (fuel := Nat.pair 6 payload)
      (tag := payload.unpair.1.unpair.1) (payload := payload.unpair.1.unpair.2) hsub1
    have e2 := decodeOracleCodeFuel_eq_decode (fuel := Nat.pair 6 payload)
      (tag := payload.unpair.2.unpair.1) (payload := payload.unpair.2.unpair.2) hsub2
    rw [Nat.pair_unpair] at e1 e2
    conv_lhs => unfold decodeOracleCode
    conv_lhs => simp only [Nat.unpair_pair, decodeOracleCodeFuel, ite_true]
    rw [e1, e2]
    simp
  · have hsub : Nat.pair payload.unpair.1 payload.unpair.2 < Nat.pair 7 payload := by
      have h2 : payload < Nat.pair 7 payload :=
        pair_gt_snd_of_pos (by decide : 1 ≤ 7)
      rw [Nat.pair_unpair]
      omega
    have e := decodeOracleCodeFuel_eq_decode (fuel := Nat.pair 7 payload)
      (tag := payload.unpair.1) (payload := payload.unpair.2) hsub
    rw [Nat.pair_unpair] at e
    conv_lhs => unfold decodeOracleCode
    conv_lhs => simp only [Nat.unpair_pair, decodeOracleCodeFuel, ite_true]
    rw [e]
    simp
  · by_cases hp : payload = 0
    · subst hp
      simp [decodeOracleCode, decodeOracleCodeFuel, Nat.unpair_pair]
    · simp [decodeOracleCode, decodeOracleCodeFuel, Nat.unpair_pair, hp]
  · have h0 : ¬(tag = 0 ∧ payload = 0) := by omega
    have h1 : ¬(tag = 1 ∧ payload = 0) := by omega
    have h2 : ¬(tag = 2 ∧ payload = 0) := by omega
    have h3 : ¬(tag = 3 ∧ payload = 0) := by omega
    have h4 : ¬tag = 4 := by omega
    have h5 : ¬tag = 5 := by omega
    have h6 : ¬tag = 6 := by omega
    have h7 : ¬tag = 7 := by omega
    have h8 : ¬(tag = 8 ∧ payload = 0) := by omega
    conv_lhs => unfold decodeOracleCode
    conv_lhs => simp only [Nat.unpair_pair, decodeOracleCodeFuel]
    simp only [ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
      ite_eq_right h4, ite_eq_right h5, ite_eq_right h6, ite_eq_right h7,
      ite_eq_right h8]

/-- **Whether a code number decodes.** For a natural number $n$, this is the Boolean value that is
true exactly when the computable decoder of oracle codes returns an oracle code on $n$.

By decoder soundness and the inversion of the encoder, this holds exactly when $n$ is the Gödel
number of an oracle code.

Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.6 (Gödel numberings; decoding). -/
def decodeIsSome (n : ℕ) : Bool :=
  (decodeOracleCode n).isSome

/-- **The definedness predicate, by cases on the tag.** Write $\langle a, b \rangle$ for the
pairing bijection $\mathbb{N} \times \mathbb{N} \to \mathbb{N}$ of the Gödel numbering, and say
that a natural number decodes when the computable decoder returns an oracle code on it. Let $t$
and $p$ be natural numbers and write $p = \langle p_1, p_2 \rangle$. Then $\langle t, p \rangle$
decodes if and only if one of the following holds: $t$ is $0$, $1$, $2$, $3$ or $8$ and $p = 0$;
$t$ is $4$, $5$ or $6$ and both $p_1$ and $p_2$ decode; or $t = 7$ and $p$ decodes.

In the recursive cases $t \ge 1$, so $p_1$, $p_2$ and $p$ are strictly smaller than
$\langle t, p \rangle$.

Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.6 (Gödel numberings; decoding). -/
theorem decodeIsSome_pair (tag payload : ℕ) :
    decodeIsSome (Nat.pair tag payload) =
      if tag = 0 ∧ payload = 0 then true
      else if tag = 1 ∧ payload = 0 then true
      else if tag = 2 ∧ payload = 0 then true
      else if tag = 3 ∧ payload = 0 then true
      else if tag = 4 then decodeIsSome payload.unpair.1 && decodeIsSome payload.unpair.2
      else if tag = 5 then decodeIsSome payload.unpair.1 && decodeIsSome payload.unpair.2
      else if tag = 6 then decodeIsSome payload.unpair.1 && decodeIsSome payload.unpair.2
      else if tag = 7 then decodeIsSome payload
      else if tag = 8 ∧ payload = 0 then true
      else false := by
  have htag : tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 3 ∨ tag = 4 ∨ tag = 5 ∨
      tag = 6 ∨ tag = 7 ∨ tag = 8 ∨ 8 < tag := by omega
  rcases htag with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hgt
  · by_cases hp : payload = 0 <;> simp [decodeIsSome, decodeOracleCode_pair, hp]
  · by_cases hp : payload = 0 <;> simp [decodeIsSome, decodeOracleCode_pair, hp]
  · by_cases hp : payload = 0 <;> simp [decodeIsSome, decodeOracleCode_pair, hp]
  · by_cases hp : payload = 0 <;> simp [decodeIsSome, decodeOracleCode_pair, hp]
  · have e0 : ¬(4 = 0 ∧ payload = 0) := by simp
    have e1 : ¬(4 = 1 ∧ payload = 0) := by simp
    have e2 : ¬(4 = 2 ∧ payload = 0) := by simp
    have e3 : ¬(4 = 3 ∧ payload = 0) := by simp
    rw [decodeIsSome, decodeOracleCode_pair]
    simp only [ite_eq_right e0, ite_eq_right e1, ite_eq_right e2, ite_eq_right e3,
      ite_eq_left rfl]
    cases h1 : decodeOracleCode payload.unpair.1 <;>
      cases h2 : decodeOracleCode payload.unpair.2 <;>
      simp [decodeIsSome, h1, h2]
  · have e0 : ¬(5 = 0 ∧ payload = 0) := by simp
    have e1 : ¬(5 = 1 ∧ payload = 0) := by simp
    have e2 : ¬(5 = 2 ∧ payload = 0) := by simp
    have e3 : ¬(5 = 3 ∧ payload = 0) := by simp
    have e4 : ¬(5 = 4) := by simp
    rw [decodeIsSome, decodeOracleCode_pair]
    simp only [ite_eq_right e0, ite_eq_right e1, ite_eq_right e2, ite_eq_right e3,
      ite_eq_right e4, ite_eq_left rfl]
    cases h1 : decodeOracleCode payload.unpair.1 <;>
      cases h2 : decodeOracleCode payload.unpair.2 <;>
      simp [decodeIsSome, h1, h2]
  · have e0 : ¬(6 = 0 ∧ payload = 0) := by simp
    have e1 : ¬(6 = 1 ∧ payload = 0) := by simp
    have e2 : ¬(6 = 2 ∧ payload = 0) := by simp
    have e3 : ¬(6 = 3 ∧ payload = 0) := by simp
    have e4 : ¬(6 = 4) := by simp
    have e5 : ¬(6 = 5) := by simp
    rw [decodeIsSome, decodeOracleCode_pair]
    simp only [ite_eq_right e0, ite_eq_right e1, ite_eq_right e2, ite_eq_right e3,
      ite_eq_right e4, ite_eq_right e5, ite_eq_left rfl]
    cases h1 : decodeOracleCode payload.unpair.1 <;>
      cases h2 : decodeOracleCode payload.unpair.2 <;>
      simp [decodeIsSome, h1, h2]
  · have e0 : ¬(7 = 0 ∧ payload = 0) := by simp
    have e1 : ¬(7 = 1 ∧ payload = 0) := by simp
    have e2 : ¬(7 = 2 ∧ payload = 0) := by simp
    have e3 : ¬(7 = 3 ∧ payload = 0) := by simp
    have e4 : ¬(7 = 4) := by simp
    have e5 : ¬(7 = 5) := by simp
    have e6 : ¬(7 = 6) := by simp
    rw [decodeIsSome, decodeOracleCode_pair]
    simp only [ite_eq_right e0, ite_eq_right e1, ite_eq_right e2, ite_eq_right e3,
      ite_eq_right e4, ite_eq_right e5, ite_eq_right e6, ite_eq_left rfl]
    cases h1 : decodeOracleCode payload <;> simp [decodeIsSome, h1]
  · by_cases hp : payload = 0 <;> simp [decodeIsSome, decodeOracleCode_pair, hp]
  · have h0 : ¬(tag = 0 ∧ payload = 0) := by omega
    have h1 : ¬(tag = 1 ∧ payload = 0) := by omega
    have h2 : ¬(tag = 2 ∧ payload = 0) := by omega
    have h3 : ¬(tag = 3 ∧ payload = 0) := by omega
    have h4 : ¬tag = 4 := by omega
    have h5 : ¬tag = 5 := by omega
    have h6 : ¬tag = 6 := by omega
    have h7 : ¬tag = 7 := by omega
    have h8 : ¬(tag = 8 ∧ payload = 0) := by omega
    simp only [decodeIsSome, decodeOracleCode_pair, ite_eq_right h0, ite_eq_right h1,
      ite_eq_right h2, ite_eq_right h3, ite_eq_right h4, ite_eq_right h5,
      ite_eq_right h6, ite_eq_right h7, ite_eq_right h8, Option.isSome_none]

/-- **One step of the course-of-values recursion for definedness.** Write $\langle a, b \rangle$
for the pairing bijection $\mathbb{N} \times \mathbb{N} \to \mathbb{N}$ of the Gödel numbering.
The step takes an argument of the unit type, which it ignores, and a list $L$ of natural numbers;
for $i \in \mathbb{N}$ write $L_i$ for the entry of $L$ at position $i$ (counting from $0$), with
$L_i = 0$ when $i$ is at least the length of $L$. Let $m$ be the length of $L$, and write
$m = \langle t, p \rangle$ and $p = \langle p_1, p_2 \rangle$. The step always returns a value,
namely $1$ if one of the following holds and $0$ otherwise: $t$ is $0$, $1$, $2$, $3$ or $8$ and
$p = 0$; $t$ is $4$, $5$ or $6$ and $L_{p_1} = L_{p_2} = 1$; or $t = 7$ and $L_p = 1$.

Applied to the list whose entry at position $k < m$ is $1$ if $k$ decodes to an oracle code and
$0$ otherwise, it returns the corresponding value for $m$, because in the recursive cases $p_1$,
$p_2$ and $p$ are smaller than $m$.

Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.6 (Gödel numberings; decoding). -/
def decodeIsSomeStep : Unit → List ℕ → Option ℕ := fun _ L =>
  if (L.length).unpair.1 = 0 then some (if (L.length).unpair.2 = 0 then 1 else 0)
  else if (L.length).unpair.1 = 1 then some (if (L.length).unpair.2 = 0 then 1 else 0)
  else if (L.length).unpair.1 = 2 then some (if (L.length).unpair.2 = 0 then 1 else 0)
  else if (L.length).unpair.1 = 3 then some (if (L.length).unpair.2 = 0 then 1 else 0)
  else if (L.length).unpair.1 = 4 then
    some (if L[(L.length).unpair.2.unpair.1]?.getD 0 = 1 ∧
      L[(L.length).unpair.2.unpair.2]?.getD 0 = 1 then 1 else 0)
  else if (L.length).unpair.1 = 5 then
    some (if L[(L.length).unpair.2.unpair.1]?.getD 0 = 1 ∧
      L[(L.length).unpair.2.unpair.2]?.getD 0 = 1 then 1 else 0)
  else if (L.length).unpair.1 = 6 then
    some (if L[(L.length).unpair.2.unpair.1]?.getD 0 = 1 ∧
      L[(L.length).unpair.2.unpair.2]?.getD 0 = 1 then 1 else 0)
  else if (L.length).unpair.1 = 7 then
    some (if L[(L.length).unpair.2]?.getD 0 = 1 then 1 else 0)
  else if (L.length).unpair.1 = 8 then some (if (L.length).unpair.2 = 0 then 1 else 0)
  else some 0

/-- **The course-of-values step for definedness is primitive recursive.** One step of the
course-of-values recursion for definedness is primitive recursive as a function of its two
arguments, an element of the unit type and a list of natural numbers.

Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.6 (Gödel numberings; decoding). -/
theorem primrec₂_decodeIsSomeStep : Primrec₂ decodeIsSomeStep := by
  have hL : Primrec (fun p : Unit × List ℕ => p.2) := Primrec.snd
  have hlen : Primrec (fun p : Unit × List ℕ => (p.2).length) :=
    Primrec.list_length.comp Primrec.snd
  have htag : Primrec (fun p : Unit × List ℕ => ((p.2).length).unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp hlen)
  have hpay : Primrec (fun p : Unit × List ℕ => ((p.2).length).unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp hlen)
  have hpay1 : Primrec
      (fun p : Unit × List ℕ => (((p.2).length).unpair.2).unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp hpay)
  have hpay2 : Primrec
      (fun p : Unit × List ℕ => (((p.2).length).unpair.2).unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp hpay)
  have hlookup1 : Primrec
      (fun p : Unit × List ℕ =>
        (p.2)[(((p.2).length).unpair.2).unpair.1]?.getD 0) :=
    Primrec₂.comp Primrec.option_getD
      (Primrec₂.comp Primrec.list_getElem? hL hpay1) (Primrec.const 0)
  have hlookup2 : Primrec
      (fun p : Unit × List ℕ =>
        (p.2)[(((p.2).length).unpair.2).unpair.2]?.getD 0) :=
    Primrec₂.comp Primrec.option_getD
      (Primrec₂.comp Primrec.list_getElem? hL hpay2) (Primrec.const 0)
  have hlookup : Primrec
      (fun p : Unit × List ℕ => (p.2)[((p.2).length).unpair.2]?.getD 0) :=
    Primrec₂.comp Primrec.option_getD
      (Primrec₂.comp Primrec.list_getElem? hL hpay) (Primrec.const 0)
  have htag0 : PrimrecPred (fun p : Unit × List ℕ => ((p.2).length).unpair.1 = 0) :=
    Primrec.eq.comp htag (Primrec.const 0)
  have htag1 : PrimrecPred (fun p : Unit × List ℕ => ((p.2).length).unpair.1 = 1) :=
    Primrec.eq.comp htag (Primrec.const 1)
  have htag2 : PrimrecPred (fun p : Unit × List ℕ => ((p.2).length).unpair.1 = 2) :=
    Primrec.eq.comp htag (Primrec.const 2)
  have htag3 : PrimrecPred (fun p : Unit × List ℕ => ((p.2).length).unpair.1 = 3) :=
    Primrec.eq.comp htag (Primrec.const 3)
  have htag4 : PrimrecPred (fun p : Unit × List ℕ => ((p.2).length).unpair.1 = 4) :=
    Primrec.eq.comp htag (Primrec.const 4)
  have htag5 : PrimrecPred (fun p : Unit × List ℕ => ((p.2).length).unpair.1 = 5) :=
    Primrec.eq.comp htag (Primrec.const 5)
  have htag6 : PrimrecPred (fun p : Unit × List ℕ => ((p.2).length).unpair.1 = 6) :=
    Primrec.eq.comp htag (Primrec.const 6)
  have htag7 : PrimrecPred (fun p : Unit × List ℕ => ((p.2).length).unpair.1 = 7) :=
    Primrec.eq.comp htag (Primrec.const 7)
  have htag8 : PrimrecPred (fun p : Unit × List ℕ => ((p.2).length).unpair.1 = 8) :=
    Primrec.eq.comp htag (Primrec.const 8)
  have hpay0 : PrimrecPred (fun p : Unit × List ℕ => ((p.2).length).unpair.2 = 0) :=
    Primrec.eq.comp hpay (Primrec.const 0)
  have hl1 : PrimrecPred
      (fun p : Unit × List ℕ =>
        (p.2)[(((p.2).length).unpair.2).unpair.1]?.getD 0 = 1) :=
    Primrec.eq.comp hlookup1 (Primrec.const 1)
  have hl2 : PrimrecPred
      (fun p : Unit × List ℕ =>
        (p.2)[(((p.2).length).unpair.2).unpair.2]?.getD 0 = 1) :=
    Primrec.eq.comp hlookup2 (Primrec.const 1)
  have hland : PrimrecPred (fun p : Unit × List ℕ =>
      (p.2)[(((p.2).length).unpair.2).unpair.1]?.getD 0 = 1 ∧
      (p.2)[(((p.2).length).unpair.2).unpair.2]?.getD 0 = 1) :=
    PrimrecPred.and hl1 hl2
  have hlr : PrimrecPred
      (fun p : Unit × List ℕ => (p.2)[((p.2).length).unpair.2]?.getD 0 = 1) :=
    Primrec.eq.comp hlookup (Primrec.const 1)
  have vLeaf : Primrec (fun p : Unit × List ℕ =>
      some (if ((p.2).length).unpair.2 = 0 then 1 else 0)) :=
    Primrec.option_some_iff.2 (Primrec.ite hpay0 (Primrec.const 1) (Primrec.const 0))
  have vBin : Primrec (fun p : Unit × List ℕ =>
      some (if (p.2)[(((p.2).length).unpair.2).unpair.1]?.getD 0 = 1 ∧
        (p.2)[(((p.2).length).unpair.2).unpair.2]?.getD 0 = 1 then 1 else 0)) :=
    Primrec.option_some_iff.2 (Primrec.ite hland (Primrec.const 1) (Primrec.const 0))
  have vRfind : Primrec (fun p : Unit × List ℕ =>
      some (if (p.2)[((p.2).length).unpair.2]?.getD 0 = 1 then 1 else 0)) :=
    Primrec.option_some_iff.2 (Primrec.ite hlr (Primrec.const 1) (Primrec.const 0))
  have vElse : Primrec (fun _ : Unit × List ℕ => some 0) :=
    Primrec.option_some_iff.2 (Primrec.const 0)
  exact Primrec.ite htag0 vLeaf (Primrec.ite htag1 vLeaf (Primrec.ite htag2 vLeaf
    (Primrec.ite htag3 vLeaf (Primrec.ite htag4 vBin (Primrec.ite htag5 vBin
    (Primrec.ite htag6 vBin (Primrec.ite htag7 vRfind (Primrec.ite htag8 vLeaf
    vElse))))))))

/-- **The definedness step function is correct.** For a natural number $n$, let $b_n$ be $1$ if
the computable decoder returns an oracle code on $n$, and $0$ otherwise. For every natural number
$m$, the one-step function of the course-of-values recursion for definedness, applied to the list
$(b_0, b_1, \dots, b_{m-1})$, returns $b_m$.

Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.6 (Gödel numberings; decoding). -/
theorem decodeIsSomeStep_correct (m : ℕ) :
    decodeIsSomeStep ()
      (List.map (fun n => (decodeIsSome n).toNat) (List.range m)) =
      some ((decodeIsSome m).toNat) := by
  obtain ⟨tag, payload, rfl⟩ : ∃ tag payload, m = Nat.pair tag payload :=
    ⟨m.unpair.1, m.unpair.2, (Nat.pair_unpair m).symm⟩
  set L := List.map (fun n => (decodeIsSome n).toNat)
    (List.range (Nat.pair tag payload)) with hL
  have hLlen : L.length = Nat.pair tag payload := by simp [hL]
  have hlookup : ∀ k < Nat.pair tag payload,
      L[k]? = some ((decodeIsSome k).toNat) := by
    intro k hk
    simp [hL, List.getElem?_map, List.getElem?_range, hk]
  have htag : tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 3 ∨ tag = 4 ∨ tag = 5 ∨
      tag = 6 ∨ tag = 7 ∨ tag = 8 ∨ 8 < tag := by omega
  rcases htag with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hgt
  · have hstep : decodeIsSomeStep () L =
        some (if payload = 0 then 1 else 0) := by
      simp [decodeIsSomeStep, hLlen, Nat.unpair_pair]
    rw [hstep]
    by_cases hp : payload = 0 <;> simp [decodeIsSome_pair, hp]
  · have hstep : decodeIsSomeStep () L =
        some (if payload = 0 then 1 else 0) := by
      simp [decodeIsSomeStep, hLlen, Nat.unpair_pair]
    rw [hstep]
    by_cases hp : payload = 0 <;> simp [decodeIsSome_pair, hp]
  · have hstep : decodeIsSomeStep () L =
        some (if payload = 0 then 1 else 0) := by
      simp [decodeIsSomeStep, hLlen, Nat.unpair_pair]
    rw [hstep]
    by_cases hp : payload = 0 <;> simp [decodeIsSome_pair, hp]
  · have hstep : decodeIsSomeStep () L =
        some (if payload = 0 then 1 else 0) := by
      simp [decodeIsSomeStep, hLlen, Nat.unpair_pair]
    rw [hstep]
    by_cases hp : payload = 0 <;> simp [decodeIsSome_pair, hp]
  · have hsub1 : payload.unpair.1 < Nat.pair 4 payload := by
      have h1 : payload.unpair.1 ≤ payload := unpair_fst_le _
      have h2 : payload < Nat.pair 4 payload :=
        pair_gt_snd_of_pos (by decide : 1 ≤ 4)
      omega
    have hsub2 : payload.unpair.2 < Nat.pair 4 payload := by
      have h1 : payload.unpair.2 ≤ payload := unpair_snd_le _
      have h2 : payload < Nat.pair 4 payload :=
        pair_gt_snd_of_pos (by decide : 1 ≤ 4)
      omega
    have hl1 := hlookup _ hsub1
    have hl2 := hlookup _ hsub2
    have hstep : decodeIsSomeStep () L =
        some (if (decodeIsSome payload.unpair.1).toNat = 1 ∧
          (decodeIsSome payload.unpair.2).toNat = 1 then 1 else 0) := by
      simp [decodeIsSomeStep, hLlen, Nat.unpair_pair, hl1, hl2]
    rw [hstep]
    cases ha : decodeIsSome payload.unpair.1 <;> cases hb : decodeIsSome payload.unpair.2 <;>
      simp [decodeIsSome_pair, ha, hb]
  · have hsub1 : payload.unpair.1 < Nat.pair 5 payload := by
      have h1 : payload.unpair.1 ≤ payload := unpair_fst_le _
      have h2 : payload < Nat.pair 5 payload :=
        pair_gt_snd_of_pos (by decide : 1 ≤ 5)
      omega
    have hsub2 : payload.unpair.2 < Nat.pair 5 payload := by
      have h1 : payload.unpair.2 ≤ payload := unpair_snd_le _
      have h2 : payload < Nat.pair 5 payload :=
        pair_gt_snd_of_pos (by decide : 1 ≤ 5)
      omega
    have hl1 := hlookup _ hsub1
    have hl2 := hlookup _ hsub2
    have hstep : decodeIsSomeStep () L =
        some (if (decodeIsSome payload.unpair.1).toNat = 1 ∧
          (decodeIsSome payload.unpair.2).toNat = 1 then 1 else 0) := by
      simp [decodeIsSomeStep, hLlen, Nat.unpair_pair, hl1, hl2]
    rw [hstep]
    cases ha : decodeIsSome payload.unpair.1 <;> cases hb : decodeIsSome payload.unpair.2 <;>
      simp [decodeIsSome_pair, ha, hb]
  · have hsub1 : payload.unpair.1 < Nat.pair 6 payload := by
      have h1 : payload.unpair.1 ≤ payload := unpair_fst_le _
      have h2 : payload < Nat.pair 6 payload :=
        pair_gt_snd_of_pos (by decide : 1 ≤ 6)
      omega
    have hsub2 : payload.unpair.2 < Nat.pair 6 payload := by
      have h1 : payload.unpair.2 ≤ payload := unpair_snd_le _
      have h2 : payload < Nat.pair 6 payload :=
        pair_gt_snd_of_pos (by decide : 1 ≤ 6)
      omega
    have hl1 := hlookup _ hsub1
    have hl2 := hlookup _ hsub2
    have hstep : decodeIsSomeStep () L =
        some (if (decodeIsSome payload.unpair.1).toNat = 1 ∧
          (decodeIsSome payload.unpair.2).toNat = 1 then 1 else 0) := by
      simp [decodeIsSomeStep, hLlen, Nat.unpair_pair, hl1, hl2]
    rw [hstep]
    cases ha : decodeIsSome payload.unpair.1 <;> cases hb : decodeIsSome payload.unpair.2 <;>
      simp [decodeIsSome_pair, ha, hb]
  · have hsub : payload < Nat.pair 7 payload :=
      pair_gt_snd_of_pos (by decide : 1 ≤ 7)
    have hl := hlookup _ hsub
    have hstep : decodeIsSomeStep () L =
        some (if (decodeIsSome payload).toNat = 1 then 1 else 0) := by
      simp [decodeIsSomeStep, hLlen, Nat.unpair_pair, hl]
    rw [hstep]
    cases ha : decodeIsSome payload <;> simp [decodeIsSome_pair, ha]
  · have hstep : decodeIsSomeStep () L =
        some (if payload = 0 then 1 else 0) := by
      simp [decodeIsSomeStep, hLlen, Nat.unpair_pair]
    rw [hstep]
    by_cases hp : payload = 0 <;> simp [decodeIsSome_pair, hp]
  · have e0 : tag ≠ 0 := by omega
    have e1 : tag ≠ 1 := by omega
    have e2 : tag ≠ 2 := by omega
    have e3 : tag ≠ 3 := by omega
    have e4 : tag ≠ 4 := by omega
    have e5 : tag ≠ 5 := by omega
    have e6 : tag ≠ 6 := by omega
    have e7 : tag ≠ 7 := by omega
    have e8 : tag ≠ 8 := by omega
    have hstep : decodeIsSomeStep () L = some 0 := by
      simp [decodeIsSomeStep, hLlen, Nat.unpair_pair, e0, e1, e2, e3, e4, e5, e6, e7, e8]
    rw [hstep]
    have h0 : ¬(tag = 0 ∧ payload = 0) := by omega
    have h1 : ¬(tag = 1 ∧ payload = 0) := by omega
    have h2 : ¬(tag = 2 ∧ payload = 0) := by omega
    have h3 : ¬(tag = 3 ∧ payload = 0) := by omega
    have h4 : ¬tag = 4 := by omega
    have h5 : ¬tag = 5 := by omega
    have h6 : ¬tag = 6 := by omega
    have h7 : ¬tag = 7 := by omega
    have h8 : ¬(tag = 8 ∧ payload = 0) := by omega
    simp [decodeIsSome_pair, ite_eq_right h0, ite_eq_right h1, ite_eq_right h2,
      ite_eq_right h3, ite_eq_right h4, ite_eq_right h5, ite_eq_right h6,
      ite_eq_right h7, ite_eq_right h8]

/-- **The definedness predicate is primitive recursive.** The function $\mathbb{N} \to \mathbb{N}$
sending $n$ to $1$ if $n$ decodes to an oracle code under the computable decoder and to $0$
otherwise is primitive recursive.

Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.6 (Gödel numberings; decoding). -/
theorem natPrimrec_decodeIsSome :
    Nat.Primrec (fun n => (decodeIsSome n).toNat) := by
  have h2 : Primrec₂ (fun (_ : Unit) (n : ℕ) => (decodeIsSome n).toNat) :=
    Primrec.nat_strong_rec _ primrec₂_decodeIsSomeStep
      (fun _ m => decodeIsSomeStep_correct m)
  have hnat : Nat.Primrec (Nat.unpaired fun m n =>
      Encodable.encode ((Encodable.decode m).bind fun a =>
        Option.map ((fun (_ : Unit) (n : ℕ) => (decodeIsSome n).toNat) a)
          (Encodable.decode n))) :=
    Primrec₂.nat_iff.1 h2
  have hcomp := Nat.Primrec.pred.comp (hnat.comp
    (Nat.Primrec.pair (Nat.Primrec.const 0) Nat.Primrec.id))
  apply Nat.Primrec.of_eq hcomp
  intro n
  simp [Nat.unpaired, Nat.unpair_pair]

/-- Oracle codes are countable, via the Gödel numbering.
Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.6 (Gödel numberings). -/
instance : Countable OracleCode :=
  Function.Injective.countable encodeOracleCode_injective

/-- Oracle codes are encodable, via the explicit computable decoder
(`Encodable` with `encode := encodeOracleCode`, `decode := decodeOracleCode`).
Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.6 (Gödel numberings). -/
instance : Encodable OracleCode :=
  ⟨encodeOracleCode, decodeOracleCode, decodeOracleCode_encode⟩

/-- **Effective enumeration of oracle codes.** The $n$-th oracle code is the code that the
computable decoder of the Gödel numbering of oracle codes assigns to $n$, or the basic code
$\mathtt{zero}$ (the constant $0$ program) when $n$ is not the number of any code. Because the
decoder inverts the Gödel numbering, this is an effective enumeration tied to that numbering,
not an arbitrary countable encoding.
Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.6 (standard enumerations). -/
def oracleCodeOfNat : ℕ → OracleCode :=
  fun n ↦ (decodeOracleCode n).getD OracleCode.zero

/-- **The effective enumeration is a left inverse of the Gödel numbering.** For every oracle code
$c$, the effective enumeration of oracle codes sends the code number of $c$ to $c$.

Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.6 (standard enumerations). -/
theorem oracleCodeOfNat_encode (c : OracleCode) :
    oracleCodeOfNat (encodeOracleCode c) = c := by
  simp [oracleCodeOfNat, decodeOracleCode_encode]

/-- **The enumeration of oracle codes is surjective.**
Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.6 (standard enumerations). -/
theorem oracleCodeOfNat_surjective : Function.Surjective oracleCodeOfNat := by
  intro c
  exact ⟨encodeOracleCode c, oracleCodeOfNat_encode c⟩

/-- **The Gödel numbering is `Primcodable`**: the round trip
`n ↦ encode (decode n)` is primitive recursive. This is the characteristic
API of the numbering: it makes `Primrec`/`Computable` statements about
oracle codes meaningful, and it is what the `Jump` definition relies on.
Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.6 (Gödel numberings). -/
instance : Primcodable OracleCode := by
  refine ⟨Nat.Primrec.of_eq
    (f := fun n => (decodeIsSome n).toNat * (n + 1)) ?_ ?_⟩
  · apply Nat.Primrec.of_eq (Nat.Primrec.mul.comp
      (Nat.Primrec.pair natPrimrec_decodeIsSome
        (Nat.Primrec.succ.comp Nat.Primrec.id)))
    intro n
    simp [Nat.unpaired, Nat.unpair_pair]
  · intro n
    show (decodeIsSome n).toNat * (n + 1) = Encodable.encode (decodeOracleCode n)
    cases hdec : decodeOracleCode n with
    | none => simp [decodeIsSome, hdec]
    | some c =>
      have henc : encodeOracleCode c = n := by
        have h := decodeOracleCodeFuel_sound (n + 1) n.unpair.1 n.unpair.2 c hdec
        rw [Nat.pair_unpair] at h
        exact h
      have henc' : Encodable.encode c = n := henc
      simp [decodeIsSome, hdec, henc']

/-- **The Gödel encoding of oracle codes is primitive recursive.** Regard oracle codes as coded
by their Gödel numbers, with the computable decoder as decoding. Then the map sending each oracle
code to its Gödel number is primitive recursive.

Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.6 (Gödel numberings). -/
theorem primrec_encodeOracleCode : Primrec encodeOracleCode :=
  Primrec.of_eq Primrec.encode fun _ => rfl

/-- **The Gödel decoder of oracle codes is primitive recursive.** Regard oracle codes as coded
by their Gödel numbers. Then the computable decoder, which sends a natural number $n$ to the
oracle code with Gödel number $n$ when there is one and to no value otherwise, is primitive
recursive as a map from natural numbers to optional oracle codes.

Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.6 (Gödel numberings; decoding). -/
theorem primrec_decodeOracleCode : Primrec decodeOracleCode :=
  Primrec.of_eq Primrec.decode fun _ => rfl

/-- **The effective enumeration of oracle codes is primitive recursive.** Regard oracle codes as
coded by their Gödel numbers. Then the effective enumeration of oracle codes, which sends a
natural number $n$ to the oracle code with Gödel number $n$ when there is one and to the zero
code otherwise, is primitive recursive.

Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.6 (standard enumerations). -/
theorem primrec_oracleCodeOfNat : Primrec oracleCodeOfNat :=
  Primrec₂.comp Primrec.option_getD primrec_decodeOracleCode (Primrec.const OracleCode.zero)

/-- **The effective enumeration of oracle codes is computable.**
Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.6 (standard enumerations). -/
theorem computable_oracleCodeOfNat : Computable oracleCodeOfNat :=
  primrec_oracleCodeOfNat.to_comp


/-- **Fuel-indexed evaluation of oracle codes.** Write $\langle a, b \rangle$ for the pairing of
natural numbers. For an oracle $o$ assigning to each natural number a natural number or no
value, a fuel $k$, an oracle code $c$ and an input $n$, the evaluator $E_k(c, n)$ returns a
natural number or fails. $E_0(c, n)$ always fails. $E_{k+1}(c, n)$ fails if $n > k$;
otherwise, with $n = \langle a, m \rangle$:

- $\mathtt{zero}$ returns $0$, $\mathtt{succ}$ returns $n + 1$, $\mathtt{left}$ returns $a$ and
  $\mathtt{right}$ returns $m$;
- $\mathtt{pair}(f, g)$ returns $\langle E_{k+1}(f, n), E_{k+1}(g, n) \rangle$;
- $\mathtt{comp}(f, g)$ returns $E_{k+1}(f, x)$ where $x = E_{k+1}(g, n)$;
- $\mathtt{prec}(f, g)$ returns $E_{k+1}(f, a)$ if $m = 0$, and if $m = y + 1$ it returns
  $E_{k+1}(g, \langle a, \langle y, i \rangle \rangle)$ where $i = E_k(\mathtt{prec}(f, g),
  \langle a, y \rangle)$;
- $\mathtt{rfind}(f)$ computes $x = E_{k+1}(f, \langle a, m \rangle)$ and returns $m$ if $x = 0$,
  and $E_k(\mathtt{rfind}(f), \langle a, m + 1 \rangle)$ otherwise;
- $\mathtt{oracle}$ returns $o(n)$, failing if $o$ has no value at $n$.

In every case the result fails if any evaluation it uses fails.
Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, §2 (oracle computations). -/
def oracleEvaln : (ℕ → Option ℕ) → ℕ → OracleCode → ℕ → Option ℕ
  | _, 0, _ => fun _ => Option.none
  | _o, k + 1, .zero => fun n => do
      guard (n ≤ k)
      return 0
  | _o, k + 1, .succ => fun n => do
      guard (n ≤ k)
      return (Nat.succ n)
  | _o, k + 1, .left => fun n => do
      guard (n ≤ k)
      return n.unpair.1
  | _o, k + 1, .right => fun n => do
      guard (n ≤ k)
      pure n.unpair.2
  | o, k + 1, .pair cf cg => fun n => do
      guard (n ≤ k)
      Nat.pair <$> oracleEvaln o (k + 1) cf n <*> oracleEvaln o (k + 1) cg n
  | o, k + 1, .comp cf cg => fun n => do
      guard (n ≤ k)
      let x ← oracleEvaln o (k + 1) cg n
      oracleEvaln o (k + 1) cf x
  | o, k + 1, .prec cf cg => fun n => do
      guard (n ≤ k)
      n.unpaired fun a n =>
        n.casesOn (oracleEvaln o (k + 1) cf a) fun y => do
          let i ← oracleEvaln o k (.prec cf cg) (Nat.pair a y)
          oracleEvaln o (k + 1) cg (Nat.pair a (Nat.pair y i))
  | o, k + 1, .rfind cf => fun n => do
      guard (n ≤ k)
      n.unpaired fun a m => do
        let x ← oracleEvaln o (k + 1) cf (Nat.pair a m)
        if x = 0 then
          pure m
        else
          oracleEvaln o k (.rfind cf) (Nat.pair a (m + 1))
  | o, k + 1, .oracle => fun n => do
      guard (n ≤ k)
      o n

/-- **Fuel bounds the inputs.** For every oracle $o$, fuel $k$, oracle code $c$ and input $n$,
if the fuel-indexed evaluator with fuel $k$ returns a value on $c$ and $n$ relative to $o$, then
$n < k$.
Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, §2 (oracle computations). -/
theorem oracleEvaln_bound {o : ℕ → Option ℕ} {k c n x}
    (h : x ∈ oracleEvaln o k c n) : n < k := by
  cases k with
  | zero => simp [oracleEvaln] at h
  | succ k =>
    by_cases hk : n ≤ k
    · omega
    · have hnone : oracleEvaln o (k + 1) c n = none := by
        cases c <;> simp [oracleEvaln, hk]
      rw [hnone] at h
      simp at h

/-- **Evaluation of oracle codes.** Let $o$ be an oracle that assigns to each natural number
either a natural number or no value, $c$ an oracle code and $n$ a natural number. The value of
$c$ on $n$ relative to $o$ is the value returned by the fuel-indexed evaluator of $c$ on $n$
relative to $o$ at the least fuel $k$ for which that evaluator returns a value; it is undefined
when there is no such $k$.
Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, §2 (oracle computations). -/
def oracleEval (o : ℕ → Option ℕ) (c : OracleCode) (n : ℕ) : Part ℕ :=
  Nat.rfindOpt fun k ↦ oracleEvaln o k c n

/-- **The Turing jump.** For a predicate $P$ on $\mathbb{N}$, the Turing jump $P'$ is the
predicate that holds at $n$ exactly when the $n$-th oracle code in the effective enumeration of
oracle codes, evaluated with the oracle that answers $1$ at $m$ if $P(m)$ holds and $0$ otherwise,
halts on input $n$. Thus $P'$ is the diagonal halting set of the universal oracle machine with
oracle $P$.

Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Definition 2.1 (the jump). -/
def Jump (P : ℕ → Prop) : ℕ → Prop :=
  fun n ↦ (oracleEval (fun m ↦ @ite (Option ℕ) (P m) (Classical.propDecidable _) (some 1) (some 0))
    (oracleCodeOfNat n) n).Dom

/-- **Turing reducibility of predicates.** A predicate $P$ on the natural numbers is Turing
reducible to a predicate $Q$ on the natural numbers when the characteristic function of $P$ is
Turing reducible to the characteristic function of $Q$, that is, partial recursive relative to an
oracle for the characteristic function of $Q$.

Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Definition 2.2. -/
def TuringReduciblePred (P Q : ℕ → Prop) : Prop :=
  charFun P ≤ᵀ charFun Q

/-- **Turing equivalence of predicates.** Two predicates $P$ and $Q$ on the natural numbers are
Turing equivalent when the characteristic function of $P$ is Turing reducible to the
characteristic function of $Q$ and the characteristic function of $Q$ is Turing reducible to the
characteristic function of $P$.

Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Definition 2.2. -/
def TuringEquivalentPred (P Q : ℕ → Prop) : Prop :=
  charFun P ≡ᵀ charFun Q

/-- **Turing degree of a predicate.** The Turing degree of a predicate $P$ on the natural numbers
is the Turing degree of its characteristic function, that is, the class of the characteristic
function of $P$ under Turing equivalence of partial functions
$\mathbb{N} \rightharpoonup \mathbb{N}$.

Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Definition 2.3. -/
noncomputable def turingDegreeOf (P : ℕ → Prop) : TuringDegree :=
  Quotient.mk _ (charFun P)

/-- **Turing reducibility is reflexive.** Every predicate $P$ on the natural numbers is Turing
reducible to itself.

Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Theorem 2.4. -/
theorem turingReduciblePred_refl (P : ℕ → Prop) : TuringReduciblePred P P := by
  change charFun P ≤ᵀ charFun P
  exact TuringReducible.refl _

/-- **Turing reducibility is transitive.** For predicates $P$, $Q$ and $R$ on the natural
numbers, if $P$ is Turing reducible to $Q$ and $Q$ is Turing reducible to $R$, then $P$ is Turing
reducible to $R$.

Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Theorem 2.4. -/
theorem turingReduciblePred_trans {P Q R : ℕ → Prop}
    (hPQ : TuringReduciblePred P Q) (hQR : TuringReduciblePred Q R) :
    TuringReduciblePred P R := by
  change charFun P ≤ᵀ charFun R
  exact TuringReducible.trans hPQ hQR

end Cslib.Decidability
