/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Computability.TuringMachine.BitOps
public import MathlibExt.Computability.Complexity

/-!
# Reading a framed bit block

A component for the fixed binary codecs: read `[true, bit]` pairs until
the `false` delimiter, reversing the payload onto another stack. Missing
bits or a missing delimiter take the failure branch. Both branches have
bounds in input length. The underlying statement language is `TM2`.
-/

@[expose] public section

namespace Cslib.Complexity.FramedCNF.Block

open Turing Function MetaMathlibExt.TM2Program
open MetaMathlibExt.BitstringEncoding

variable {K Λ : Type} [DecidableEq K] {Γ : K → Type}

/-- **Machine step reading one framed payload pair.**
Consume one framed-payload pair or its terminator. -/
def read (a b : K) (d : Γ a → Option Bool) (g : Bool → Γ b)
    (self good bad : Λ) : TM2.Stmt Γ Λ Bool :=
  .peek a (fun _ o => isBit d o) <| .branch id
    (.pop a (fun _ o => bitOf d o) <| .branch id
      (.peek a (fun _ o => isBit d o) <| .branch id
        (.pop a (fun _ o => bitOf d o) <| .push b g <|
          .goto fun _ => self)
        (.goto fun _ => bad))
      (.goto fun _ => good))
    (.goto fun _ => bad)

private theorem end_step {M : Λ → TM2.Stmt Γ Λ Bool}
    {a b : K} {d : Γ a → Option Bool} {g : Bool → Γ b}
    {self good bad : Λ} (hM : M self = read a b d g self good bad)
    {z : Γ a} (hz : d z = some false) (v : Bool)
    (S : ∀ k, List (Γ k)) (tail : List (Γ a))
    (hS : S a = z :: tail) :
    Run M 1 ⟨some self, v, S⟩
      ⟨some good, false, update S a tail⟩ := by
  apply Run.single
  simp [hM, read, TM2.stepAux, isBit, bitOf, hS, hz]

private theorem pair_step {M : Λ → TM2.Stmt Γ Λ Bool}
    {a b : K} {d : Γ a → Option Bool} {g : Bool → Γ b}
    {self good bad : Λ} (hM : M self = read a b d g self good bad)
    (hab : a ≠ b) {z y : Γ a} {bit : Bool}
    (hz : d z = some true) (hy : d y = some bit) (v : Bool)
    (S : ∀ k, List (Γ k)) (tail : List (Γ a))
    (hS : S a = z :: y :: tail) :
    Run M 1 ⟨some self, v, S⟩
      ⟨some self, bit, update (update S a tail) b (g bit :: S b)⟩ := by
  apply Run.single
  simp [hM, read, TM2.stepAux, isBit, bitOf, hS, hz, hy, hab.symm]

/-- **Reading a complete framed block.**
Read a complete block, preserving an arbitrary suffix and all stacks
other than the input and reversed-payload destination. -/
theorem run_delimit {M : Λ → TM2.Stmt Γ Λ Bool}
    {a b : K} {d : Γ a → Option Bool} {g : Bool → Γ b}
    {self good bad : Λ} (hM : M self = read a b d g self good bad)
    (hab : a ≠ b) (ga : Bool → Γ a) (hga : ∀ c, d (ga c) = some c)
    (payload : List Bool) : ∀ (tail : List (Γ a)) (v : Bool)
      (S : ∀ k, List (Γ k)),
      S a = (delimit payload).map ga ++ tail →
      ∃ S', Run M (payload.length + 1) ⟨some self, v, S⟩
        ⟨some good, false, S'⟩ ∧ S' a = tail ∧
        S' b = (payload.map g).reverse ++ S b ∧
        ∀ k, k ≠ a → k ≠ b → S' k = S k := by
  induction payload with
  | nil =>
    intro tail v S hS
    refine ⟨update S a tail,
      end_step hM (hga false) v S tail (by simpa [delimit] using hS),
      by simp, ?_, ?_⟩
    · simp [hab.symm]
    · intro k hka _
      simp [hka]
  | cons c payload ih =>
    intro tail v S hS
    let A := (delimit payload).map ga ++ tail
    let S₁ := update (update S a A) b (g c :: S b)
    have r₁ := pair_step hM hab (hga true) (hga c) v S A
      (by simpa [delimit, A] using hS)
    obtain ⟨S', r₂, ha, hb, hk⟩ :=
      ih tail c S₁ (by simp [S₁, hab, A])
    refine ⟨S', (r₁.trans r₂).of_eq (by simp; omega), ha, ?_, ?_⟩
    · simpa [S₁, List.reverse_cons, List.append_assoc] using hb
    · intro k hka hkb
      rw [hk k hka hkb]
      simp [S₁, hka, hkb]

/-- **Framed block reader fails on truncated framing.**
Truncated framing reaches the failure branch within input length
plus one, without assuming that the input is an encoder image. The
destination may contain a partial payload on failure; the caller must
discard or clear it before using that stack again. -/
theorem run_none {M : Λ → TM2.Stmt Γ Λ Bool}
    {a b : K} {d : Γ a → Option Bool} {g : Bool → Γ b}
    {self good bad : Λ} (hM : M self = read a b d g self good bad)
    (hab : a ≠ b) (ga : Bool → Γ a) (hga : ∀ c, d (ga c) = some c)
    (input : List Bool) (v : Bool) (S : ∀ k, List (Γ k))
    (hS : S a = input.map ga) (hn : undelimit input = none) :
    ∃ v' S', RunLe M (input.length + 1) ⟨some self, v, S⟩
      ⟨some bad, v', S'⟩ := by
  cases input with
  | nil =>
    refine ⟨false, S, 1, by simp, Run.single ?_⟩
    simp [hM, read, TM2.stepAux, isBit, bitOf, hS]
  | cons c input =>
    cases c with
    | false => simp [undelimit] at hn
    | true =>
      cases input with
      | nil =>
        refine ⟨false, update S a [], 1, by simp, Run.single ?_⟩
        simp [hM, read, TM2.stepAux, isBit, bitOf, hS, hga]
      | cons c input =>
        let S₁ := update (update S a (input.map ga)) b (g c :: S b)
        have r₁ := pair_step hM hab (hga true) (hga c) v S
          (input.map ga) (by simpa using hS)
        have hn' : undelimit input = none := by
          simpa [undelimit] using hn
        obtain ⟨v', S', hr⟩ := run_none hM hab ga hga input c S₁
          (by simp [S₁, hab]) hn'
        exact ⟨v', S', ((r₁.le le_rfl).trans hr).mono (by simp; omega)⟩
termination_by input.length

end Cslib.Complexity.FramedCNF.Block
