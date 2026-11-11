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
# Emitting a canonical frame in reverse

The ListNat normalizer accumulates completed frames in reverse order,
then reverses once at the end. This primitive consumes a raw bit block,
emits its canonical delimiter frame in reverse, and leaves other stacks
alone. It is a `TM2` statement schema, not another machine model.
-/

@[expose] public section

namespace Cslib.Complexity.PolynomialEncoding

open Turing Function MetaMathlibExt.TM2Program
open MetaMathlibExt.BitstringEncoding

variable {K Λ : Type} [DecidableEq K] {Γ : K → Type}

/-- Emit one raw payload as a reversed self-delimiting frame. -/
def emitFrame (a b : K) (d : Γ a → Option Bool) (g : Bool → Γ b)
    (self next : Λ) : TM2.Stmt Γ Λ Bool :=
  .peek a (fun _ o => isBit d o) <| .branch id
    (.pop a (fun _ o => bitOf d o) <|
      .push b (fun _ => g true) <| .push b g <| .goto fun _ => self)
    (.push b (fun _ => g false) <| .goto fun _ => next)

/-- Empty payloads emit exactly their terminator and preserve the rest. -/
private theorem emitFrame_end {M : Λ → TM2.Stmt Γ Λ Bool}
    {a b : K} {d : Γ a → Option Bool} {g : Bool → Γ b}
    {self next : Λ} (hM : M self = emitFrame a b d g self next)
    (v : Bool) (S : ∀ k, List (Γ k)) (h : EndsBitBlock d (S a)) :
    Run M 1 ⟨some self, v, S⟩
      ⟨some next, false, update S b (g false :: S b)⟩ := by
  apply Run.single
  have he : isBit d (S a).head? = false := by
    change (S a).head?.bind d = none at h
    simp only [isBit, h, Option.isSome_none]
  simp [hM, emitFrame, TM2.stepAux, he]

/-- One payload bit contributes the reversed two-bit framing pair. -/
private theorem emitFrame_step {M : Λ → TM2.Stmt Γ Λ Bool}
    {a b : K} {d : Γ a → Option Bool} {g : Bool → Γ b}
    {self next : Λ} (hM : M self = emitFrame a b d g self next)
    (hab : a ≠ b) (z : Γ a) (c : Bool) (hz : d z = some c)
    (v : Bool) (S : ∀ k, List (Γ k)) (tail : List (Γ a))
    (hS : S a = z :: tail) :
    Run M 1 ⟨some self, v, S⟩
      ⟨some self, c,
        update (update S a tail) b (g c :: g true :: S b)⟩ := by
  apply Run.single
  simp [hM, emitFrame, TM2.stepAux, isBit, bitOf, hz, hS, hab.symm]

/-- Emit a complete frame in `payload.length + 1` steps, restoring the
input suffix and leaving every unrelated stack unchanged. -/
theorem emitFrame_run {M : Λ → TM2.Stmt Γ Λ Bool}
    {a b : K} {d : Γ a → Option Bool} {g : Bool → Γ b}
    {self next : Λ} (hM : M self = emitFrame a b d g self next)
    (hab : a ≠ b) (ga : Bool → Γ a) (hga : ∀ c, d (ga c) = some c)
    (payload : List Bool) : ∀ (tail : List (Γ a)) (v : Bool)
      (S : ∀ k, List (Γ k)), EndsBitBlock d tail →
      S a = payload.map ga ++ tail →
      ∃ S', Run M (payload.length + 1) ⟨some self, v, S⟩
        ⟨some next, false, S'⟩ ∧ S' a = tail ∧
        S' b = ((delimit payload).map g).reverse ++ S b ∧
        ∀ k, k ≠ a → k ≠ b → S' k = S k := by
  induction payload with
  | nil =>
    intro tail v S ht hs
    have ha : S a = tail := by simpa using hs
    refine ⟨update S b (g false :: S b),
      emitFrame_end hM v S (ha.symm ▸ ht), ?_, ?_, ?_⟩
    · simp [hab, ha]
    · simp [delimit]
    · intro k _ hk
      simp [hk]
  | cons c payload ih =>
    intro tail v S ht hs
    let rest := payload.map ga ++ tail
    let T := update (update S a rest) b (g c :: g true :: S b)
    have first := emitFrame_step hM hab (ga c) c (hga c) v S rest
      (by simpa [rest] using hs)
    obtain ⟨U, run, ha, hb, hk⟩ := ih tail c T ht
      (by simp [T, hab, rest])
    refine ⟨U, (first.trans run).of_eq (by simp; omega), ha, ?_, ?_⟩
    · simpa [T, delimit, List.reverse_cons, List.append_assoc] using hb
    · intro k hka hkb
      rw [hk k hka hkb]
      simp [T, hka, hkb]

end Cslib.Complexity.PolynomialEncoding
