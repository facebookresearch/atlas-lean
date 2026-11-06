/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Computability.TuringMachine.BitOps

/-!
# Copying a bit block without consuming the source

This concrete TM2 composition is used to preserve a raw ListNat input
for canonicality comparison and to duplicate a verifier mask. An existing
moveB pass reverses onto scratch; a two-destination pass restores the
source while copying it. No decoded numeric value is enumerated.
-/

@[expose] public section

namespace Cslib.Complexity.PolynomialEncoding

open Turing Function MetaMathlibExt.TM2Program

variable {K Λ : Type} [DecidableEq K] {Γ : K → Type}

/-- **Two-destination bit-block transfer.**
Pop a bit block onto two distinct destinations, reversing both copies. -/
def splitB (a b c : K) (d : Γ a → Option Bool)
    (gb : Bool → Γ b) (gc : Bool → Γ c) (self next : Λ) :
    TM2.Stmt Γ Λ Bool :=
  .peek a (fun _ o => isBit d o) <| .branch id
    (.pop a (fun _ o => bitOf d o) <|
      .push b gb <| .push c gc <| .goto fun _ => self)
    (.goto fun _ => next)

private theorem splitB_step {M : Λ → TM2.Stmt Γ Λ Bool}
    {a b c : K} {d : Γ a → Option Bool}
    {gb : Bool → Γ b} {gc : Bool → Γ c} {self next : Λ}
    (hM : M self = splitB a b c d gb gc self next)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (z : Γ a) (bit : Bool) (hz : d z = some bit)
    (tail : List (Γ a)) (v : Bool) (S : ∀ k, List (Γ k))
    (hs : S a = z :: tail) :
    Run M 1 ⟨some self, v, S⟩
      ⟨some self, bit, update (update (update S a tail)
        b (gb bit :: S b)) c (gc bit :: S c)⟩ := by
  apply Run.single
  simp [hM, splitB, TM2.stepAux, isBit, bitOf, hs, hz,
    hab.symm, hac.symm, hbc.symm]

/-- **Two-destination bit transfer takes one step per bit plus one.**
Two-destination bit transfer takes one step per bit plus one,
with exact suffix and unrelated-stack preservation. -/
theorem splitB_run {M : Λ → TM2.Stmt Γ Λ Bool}
    {a b c : K} {d : Γ a → Option Bool}
    {gb : Bool → Γ b} {gc : Bool → Γ c} {self next : Λ}
    (hM : M self = splitB a b c d gb gc self next)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ga : Bool → Γ a) (hga : ∀ bit, d (ga bit) = some bit)
    (p : List Bool) : ∀ (tail : List (Γ a)) (v : Bool)
      (S : ∀ k, List (Γ k)), EndsBitBlock d tail →
      S a = p.map ga ++ tail →
      ∃ S', Run M (p.length + 1) ⟨some self, v, S⟩
        ⟨some next, false, S'⟩ ∧ S' a = tail ∧
        S' b = (p.map gb).reverse ++ S b ∧
        S' c = (p.map gc).reverse ++ S c ∧
        ∀ k, k ≠ a → k ≠ b → k ≠ c → S' k = S k := by
  induction p with
  | nil =>
    intro tail v S ht hs
    have ha : S a = tail := by simpa using hs
    have he : isBit d (S a).head? = false := by
      change tail.head?.bind d = none at ht
      simp [isBit, ha, ht]
    refine ⟨S, Run.single ?_, ha, by simp, by simp, ?_⟩
    · simp [hM, splitB, TM2.stepAux, he]
    · intro k _ _ _
      rfl
  | cons bit p ih =>
    intro tail v S ht hs
    let rest := p.map ga ++ tail
    let T := update (update (update S a rest)
      b (gb bit :: S b)) c (gc bit :: S c)
    have first := splitB_step hM hab hac hbc (ga bit) bit
      (hga bit) rest v S (by simpa [rest] using hs)
    obtain ⟨U, run, ha, hb, hc, hk⟩ := ih tail bit T ht
      (by simp [T, hab, hac, rest])
    refine ⟨U, (first.trans run).of_eq (by simp; omega), ha, ?_, ?_, ?_⟩
    · simpa [T, hbc, List.reverse_cons, List.append_assoc] using hb
    · simpa [T, List.reverse_cons, List.append_assoc] using hc
    · intro k hka hkb hkc
      rw [hk k hka hkb hkc]
      simp [T, hka, hkb, hkc]

/-- **Bit-block copy keeps the order and restores source and scratch.**
Copy a bit block in its original order, restoring both the source
and scratch, in exactly `2 * p.length + 2` steps. -/
theorem copyB_run {M : Λ → TM2.Stmt Γ Λ Bool}
    {a b t : K} {da : Γ a → Option Bool} {dt : Γ t → Option Bool}
    {ga : Bool → Γ a} {gb : Bool → Γ b} {gt : Bool → Γ t}
    {first second next : Λ}
    (h₁ : M first = moveB a t da gt first second)
    (h₂ : M second = splitB t a b dt ga gb second next)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (hga : ∀ bit, da (ga bit) = some bit)
    (hgt : ∀ bit, dt (gt bit) = some bit)
    (p : List Bool) (tail : List (Γ a)) (v : Bool)
    (S : ∀ k, List (Γ k)) (ha : S a = p.map ga ++ tail)
    (htail : EndsBitBlock da tail) (ht : EndsBitBlock dt (S t)) :
    ∃ S', Run M (2 * p.length + 2) ⟨some first, v, S⟩
      ⟨some next, false, S'⟩ ∧ S' a = S a ∧ S' t = S t ∧
      S' b = p.map gb ++ S b ∧
      ∀ k, k ≠ a → k ≠ b → k ≠ t → S' k = S k := by
  obtain ⟨v₁, T, r₁, hta, htt, htk⟩ :=
    moveB_run h₁ hat p (p.map ga) tail v S ha
      (by simp [IsBitBlock, hga]) htail
  obtain ⟨U, r₂, hut, hua, hub, huk⟩ := splitB_run h₂
    hat.symm hbt.symm hab gt hgt p.reverse (S t) v₁ T ht
    (by simpa [List.map_reverse] using htt)
  refine ⟨U, (r₁.trans r₂).of_eq (by simp; omega), ?_, hut, ?_, ?_⟩
  · simpa [List.map_reverse, hta, ha] using hua
  · have he : T b = S b := htk b hab.symm hbt
    simpa [List.map_reverse, he] using hub
  · intro k hka hkb hkt
    rw [huk k hkt hka hkb, htk k hka hkt]

end Cslib.Complexity.PolynomialEncoding
