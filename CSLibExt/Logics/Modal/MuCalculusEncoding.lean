/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.MuCalculus
public import Mathlib.Data.Nat.Pairing

/-!
# Closed formulas and an injective encoding of the modal μ-calculus

This file adds the pieces of the modal μ-calculus (`CSLibExt/Logics/Modal/MuCalculus.lean`)
needed to state satisfiability as a decision problem:

* `MuFormula.ClosedAt` / `MuFormula.Closed`: a formula is closed when every de Bruijn
  variable is bound, and `sat_closed_env`: a closed formula's denotation does not depend
  on the environment.
* `muCode`: an injective encoding of formulas over `ℕ` atoms as natural numbers, via the
  Cantor pairing function `Nat.pair`.
* `muDecode`: a decoder inverting `muCode` (`muDecode_muCode`), so every formula is the
  decoding of its code.

Main results:

* `sat_closed_env`: closed formulas are environment-independent.
* `muDecode_muCode`: `muDecode (muCode φ) = some φ`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib
namespace Modal
namespace MuCalculus

universe u

namespace MuFormula

variable {Atom : Type u}

/-- A formula is closed at depth `d` when every free de Bruijn variable is `< d`:
each binder (including `μ` / `ν`, as well as `□` / `◇`, which do not bind) shifts the
depth. -/
def ClosedAt : ℕ → MuFormula Atom → Prop
  | _, .atom _ => True
  | _, .natom _ => True
  | d, .var n => n < d
  | _, .bot => True
  | _, .top => True
  | d, .and φ ψ => ClosedAt d φ ∧ ClosedAt d ψ
  | d, .or φ ψ => ClosedAt d φ ∧ ClosedAt d ψ
  | d, .box φ => ClosedAt d φ
  | d, .dia φ => ClosedAt d φ
  | d, .mu φ => ClosedAt (d + 1) φ
  | d, .nu φ => ClosedAt (d + 1) φ

/-- A formula is closed when it is closed at depth `0`: every variable is bound. -/
def Closed (φ : MuFormula Atom) : Prop := ClosedAt 0 φ

/-- The depth of a formula: the length of its longest root-to-leaf path, counting
each connective once. -/
def depth : MuFormula Atom → ℕ
  | .atom _ => 0
  | .natom _ => 0
  | .var _ => 0
  | .bot => 0
  | .top => 0
  | .and φ ψ => 1 + max (depth φ) (depth ψ)
  | .or φ ψ => 1 + max (depth φ) (depth ψ)
  | .box φ => 1 + depth φ
  | .dia φ => 1 + depth φ
  | .mu φ => 1 + depth φ
  | .nu φ => 1 + depth φ

end MuFormula

section ClosedEnv

variable {World Atom : Type*} (M : KripkeModel World Atom)

/-- A closed formula does not depend on the environment: environments agreeing below
the depth give the same denotation. -/
theorem sat_closed_env :
    ∀ (φ : MuFormula Atom) (d : ℕ) {env env' : ℕ → World → Prop},
    MuFormula.ClosedAt d φ → (∀ n, n < d → env n = env' n) →
    sat M env φ = sat M env' φ := by
  intro φ
  induction φ with
  | atom _ => intro d env env' _ _; rfl
  | natom _ => intro d env env' _ _; rfl
  | var n => intro d env env' hcl hEq; exact hEq n hcl
  | bot => intro d env env' _ _; rfl
  | top => intro d env env' _ _; rfl
  | and φ ψ ihφ ihψ =>
      intro d env env' hcl hEq
      funext w
      change (sat M env φ w ∧ sat M env ψ w) =
        (sat M env' φ w ∧ sat M env' ψ w)
      rw [congrFun (ihφ d hcl.1 hEq) w, congrFun (ihψ d hcl.2 hEq) w]
  | or φ ψ ihφ ihψ =>
      intro d env env' hcl hEq
      funext w
      change (sat M env φ w ∨ sat M env ψ w) =
        (sat M env' φ w ∨ sat M env' ψ w)
      rw [congrFun (ihφ d hcl.1 hEq) w, congrFun (ihψ d hcl.2 hEq) w]
  | box φ ih =>
      intro d env env' hcl hEq
      funext w
      change (∀ v, M.rel w v → sat M env φ v) =
        (∀ v, M.rel w v → sat M env' φ v)
      rw [ih d hcl hEq]
  | dia φ ih =>
      intro d env env' hcl hEq
      funext w
      change (∃ v, M.rel w v ∧ sat M env φ v) =
        (∃ v, M.rel w v ∧ sat M env' φ v)
      rw [ih d hcl hEq]
  | mu φ ih =>
      intro d env env' hcl hEq
      have key : ∀ S : World → Prop,
          sat M (extendEnv env S) φ = sat M (extendEnv env' S) φ := by
        intro S
        apply ih (d + 1) hcl
        intro n hn
        cases n with
        | zero => rfl
        | succ n => exact hEq n (Nat.lt_of_succ_lt_succ hn)
      have hop : muOp M env φ = muOp M env' φ :=
        OrderHom.ext _ _ (funext fun S => key S)
      rw [sat_mu_eq_lfp M env φ, sat_mu_eq_lfp M env' φ, hop]
  | nu φ ih =>
      intro d env env' hcl hEq
      have key : ∀ S : World → Prop,
          sat M (extendEnv env S) φ = sat M (extendEnv env' S) φ := by
        intro S
        apply ih (d + 1) hcl
        intro n hn
        cases n with
        | zero => rfl
        | succ n => exact hEq n (Nat.lt_of_succ_lt_succ hn)
      have hop : muOp M env φ = muOp M env' φ :=
        OrderHom.ext _ _ (funext fun S => key S)
      rw [sat_nu_eq_gfp M env φ, sat_nu_eq_gfp M env' φ, hop]

end ClosedEnv

section Encoding

/-- An injective encoding of μ-calculus formulas over `ℕ` atoms as natural numbers,
via the Cantor pairing function `Nat.pair`. -/
def muCode : MuFormula ℕ → ℕ
  | .atom a => Nat.pair 0 a
  | .natom a => Nat.pair 1 a
  | .var n => Nat.pair 2 n
  | .bot => Nat.pair 3 0
  | .top => Nat.pair 4 0
  | .and φ ψ => Nat.pair 5 (Nat.pair (muCode φ) (muCode ψ))
  | .or φ ψ => Nat.pair 6 (Nat.pair (muCode φ) (muCode ψ))
  | .box φ => Nat.pair 7 (muCode φ)
  | .dia φ => Nat.pair 8 (muCode φ)
  | .mu φ => Nat.pair 9 (muCode φ)
  | .nu φ => Nat.pair 10 (muCode φ)

/-- Fuelled decoding of a `muCode` number back to a formula. The fuel bounds the
recursion depth; `muDecode` supplies fuel `c + 1`, which exceeds every formula's
depth (see `depth_le_code`). -/
def muDecodeFuel : ℕ → ℕ → Option (MuFormula ℕ)
  | 0, _ => none
  | fuel + 1, c =>
    match Nat.unpair c with
    | (0, a) => some (.atom a)
    | (1, a) => some (.natom a)
    | (2, n) => some (.var n)
    | (3, _) => some .bot
    | (4, _) => some .top
    | (5, r) =>
      match Nat.unpair r with
      | (c₁, c₂) =>
        match muDecodeFuel fuel c₁, muDecodeFuel fuel c₂ with
        | some f₁, some f₂ => some (.and f₁ f₂)
        | _, _ => none
    | (6, r) =>
      match Nat.unpair r with
      | (c₁, c₂) =>
        match muDecodeFuel fuel c₁, muDecodeFuel fuel c₂ with
        | some f₁, some f₂ => some (.or f₁ f₂)
        | _, _ => none
    | (7, c₁) => .box <$> muDecodeFuel fuel c₁
    | (8, c₁) => .dia <$> muDecodeFuel fuel c₁
    | (9, c₁) => .mu <$> muDecodeFuel fuel c₁
    | (10, c₁) => .nu <$> muDecodeFuel fuel c₁
    | (_, _) => none

/-- Decode a `muCode` number back to the formula it encodes. -/
def muDecode (c : ℕ) : Option (MuFormula ℕ) := muDecodeFuel (c + 1) c

/-- A formula's depth is at most its code: pairing dominates each component
(`Nat.add_le_pair`). -/
theorem depth_le_code : ∀ φ : MuFormula ℕ, MuFormula.depth φ ≤ muCode φ := by
  intro φ
  induction φ with
  | atom a => simp [MuFormula.depth, muCode]
  | natom a => simp [MuFormula.depth, muCode]
  | var n => simp [MuFormula.depth, muCode]
  | bot => simp [MuFormula.depth, muCode]
  | top => simp [MuFormula.depth, muCode]
  | and φ ψ ihφ ihψ =>
      calc MuFormula.depth (.and φ ψ)
          = 1 + max (MuFormula.depth φ) (MuFormula.depth ψ) := rfl
      _ ≤ 1 + (muCode φ + muCode ψ) := by
          have h1 := ihφ
          have h2 := ihψ
          omega
      _ ≤ 5 + Nat.pair (muCode φ) (muCode ψ) := by
          have h := Nat.add_le_pair (muCode φ) (muCode ψ)
          omega
      _ ≤ Nat.pair 5 (Nat.pair (muCode φ) (muCode ψ)) := Nat.add_le_pair 5 _
      _ = muCode (.and φ ψ) := rfl
  | or φ ψ ihφ ihψ =>
      calc MuFormula.depth (.or φ ψ)
          = 1 + max (MuFormula.depth φ) (MuFormula.depth ψ) := rfl
      _ ≤ 1 + (muCode φ + muCode ψ) := by
          have h1 := ihφ
          have h2 := ihψ
          omega
      _ ≤ 6 + Nat.pair (muCode φ) (muCode ψ) := by
          have h := Nat.add_le_pair (muCode φ) (muCode ψ)
          omega
      _ ≤ Nat.pair 6 (Nat.pair (muCode φ) (muCode ψ)) := Nat.add_le_pair 6 _
      _ = muCode (.or φ ψ) := rfl
  | box φ ih =>
      calc MuFormula.depth (.box φ) = 1 + MuFormula.depth φ := rfl
      _ ≤ 1 + muCode φ := by have h := ih; omega
      _ ≤ 7 + muCode φ := by omega
      _ ≤ Nat.pair 7 (muCode φ) := Nat.add_le_pair 7 _
      _ = muCode (.box φ) := rfl
  | dia φ ih =>
      calc MuFormula.depth (.dia φ) = 1 + MuFormula.depth φ := rfl
      _ ≤ 1 + muCode φ := by have h := ih; omega
      _ ≤ 8 + muCode φ := by omega
      _ ≤ Nat.pair 8 (muCode φ) := Nat.add_le_pair 8 _
      _ = muCode (.dia φ) := rfl
  | mu φ ih =>
      calc MuFormula.depth (.mu φ) = 1 + MuFormula.depth φ := rfl
      _ ≤ 1 + muCode φ := by have h := ih; omega
      _ ≤ 9 + muCode φ := by omega
      _ ≤ Nat.pair 9 (muCode φ) := Nat.add_le_pair 9 _
      _ = muCode (.mu φ) := rfl
  | nu φ ih =>
      calc MuFormula.depth (.nu φ) = 1 + MuFormula.depth φ := rfl
      _ ≤ 1 + muCode φ := by have h := ih; omega
      _ ≤ 10 + muCode φ := by omega
      _ ≤ Nat.pair 10 (muCode φ) := Nat.add_le_pair 10 _
      _ = muCode (.nu φ) := rfl

/-- Decoding inverts encoding, with enough fuel: a formula's own code carries
more fuel than its depth needs. -/
theorem muDecodeFuel_muCode : ∀ (φ : MuFormula ℕ) (fuel : ℕ),
    MuFormula.depth φ ≤ fuel → muDecodeFuel (fuel + 1) (muCode φ) = some φ := by
  intro φ
  induction φ with
  | atom a => intro fuel _; simp [muDecodeFuel, muCode, Nat.unpair_pair]
  | natom a => intro fuel _; simp [muDecodeFuel, muCode, Nat.unpair_pair]
  | var n => intro fuel _; simp [muDecodeFuel, muCode, Nat.unpair_pair]
  | bot => intro fuel _; simp [muDecodeFuel, muCode, Nat.unpair_pair]
  | top => intro fuel _; simp [muDecodeFuel, muCode, Nat.unpair_pair]
  | and φ ψ ihφ ihψ =>
      intro fuel hfuel
      cases fuel with
      | zero => simp only [MuFormula.depth] at hfuel; omega
      | succ fuel' =>
        have hφ : MuFormula.depth φ ≤ fuel' := by
          simp only [MuFormula.depth] at hfuel; omega
        have hψ : MuFormula.depth ψ ≤ fuel' := by
          simp only [MuFormula.depth] at hfuel; omega
        unfold muDecodeFuel
        simp only [muCode, Nat.unpair_pair]
        rw [ihφ fuel' hφ, ihψ fuel' hψ]
  | or φ ψ ihφ ihψ =>
      intro fuel hfuel
      cases fuel with
      | zero => simp only [MuFormula.depth] at hfuel; omega
      | succ fuel' =>
        have hφ : MuFormula.depth φ ≤ fuel' := by
          simp only [MuFormula.depth] at hfuel; omega
        have hψ : MuFormula.depth ψ ≤ fuel' := by
          simp only [MuFormula.depth] at hfuel; omega
        unfold muDecodeFuel
        simp only [muCode, Nat.unpair_pair]
        rw [ihφ fuel' hφ, ihψ fuel' hψ]
  | box φ ih =>
      intro fuel hfuel
      cases fuel with
      | zero => simp only [MuFormula.depth] at hfuel; omega
      | succ fuel' =>
        have hφ : MuFormula.depth φ ≤ fuel' := by
          simp only [MuFormula.depth] at hfuel; omega
        unfold muDecodeFuel
        simp only [muCode, Nat.unpair_pair]
        rw [ih fuel' hφ]
        rfl
  | dia φ ih =>
      intro fuel hfuel
      cases fuel with
      | zero => simp only [MuFormula.depth] at hfuel; omega
      | succ fuel' =>
        have hφ : MuFormula.depth φ ≤ fuel' := by
          simp only [MuFormula.depth] at hfuel; omega
        unfold muDecodeFuel
        simp only [muCode, Nat.unpair_pair]
        rw [ih fuel' hφ]
        rfl
  | mu φ ih =>
      intro fuel hfuel
      cases fuel with
      | zero => simp only [MuFormula.depth] at hfuel; omega
      | succ fuel' =>
        have hφ : MuFormula.depth φ ≤ fuel' := by
          simp only [MuFormula.depth] at hfuel; omega
        unfold muDecodeFuel
        simp only [muCode, Nat.unpair_pair]
        rw [ih fuel' hφ]
        rfl
  | nu φ ih =>
      intro fuel hfuel
      cases fuel with
      | zero => simp only [MuFormula.depth] at hfuel; omega
      | succ fuel' =>
        have hφ : MuFormula.depth φ ≤ fuel' := by
          simp only [MuFormula.depth] at hfuel; omega
        unfold muDecodeFuel
        simp only [muCode, Nat.unpair_pair]
        rw [ih fuel' hφ]
        rfl

/-- Decoding inverts encoding. -/
theorem muDecode_muCode (φ : MuFormula ℕ) : muDecode (muCode φ) = some φ :=
  muDecodeFuel_muCode φ (muCode φ) (depth_le_code φ)

/-- The encoding is injective. -/
theorem muCode_injective : Function.Injective muCode := by
  intro φ ψ h
  have h' := congrArg muDecode h
  rw [muDecode_muCode, muDecode_muCode] at h'
  exact Option.some.inj h'

end Encoding

end MuCalculus
end Modal
end Cslib
