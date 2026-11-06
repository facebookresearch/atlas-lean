/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.SSVerifierSum
public import MathlibExt.Computability.TuringMachine.Cleanup

/-!
# Binary arithmetic using the existing SUBSET-SUM machine

The adapter accepts two canonically framed inputs and selects both. It
clears any remaining mask and reverses the output without replacing the
adder. Raw Nat payloads must be normalized and framed before entry.
-/

@[expose] public section

namespace Cslib.Complexity.SSVerifierArithmetic

open Cslib.Complexity.Karp Cslib.Complexity.SatVerifier
open MetaMathlibExt MetaMathlibExt.TM2Program TM2Embedding Turing Function
open Computability BitstringEncoding

private theorem step_mask_length (l : SSVerify.Lab) (v : Bool)
    (S : SSVerify.K → List Sym) :
    ((TM2.stepAux (SSVerify.prog l) v S).stk .W).length ≤
      (S .W).length := by
  cases l <;>
    simp only [SSVerify.prog, SSVerify.rdS, SSVerify.nextS,
      SSVerify.addS, SSVerify.finS, moveB, cmpB, Bool.cond_eq_ite,
      TM2.stepAux]
  all_goals
    repeat' first | (solve | simp_all [TM2.stepAux]) | split

private theorem run_mask_length {n : ℕ}
    {c d : TM2.Cfg (fun _ : SSVerify.K => Sym) SSVerify.Lab Bool}
    (h : Run SSVerify.prog n c d) :
    (d.stk .W).length ≤ (c.stk .W).length := by
  induction n generalizing c with
  | zero =>
    have he : c = d := by simpa [Run] using h
    subst d
    exact le_rfl
  | succ n ih =>
    rcases c with ⟨_ | l, v, S⟩
    · rw [Run, iterate_succ_apply] at h
      change (flip bind (TM2.step SSVerify.prog))^[n] none = some d at h
      rw [iter_none] at h
      cases h
    · rw [Run, iterate_succ_apply] at h
      change Run SSVerify.prog n
        (TM2.stepAux (SSVerify.prog l) v S) d at h
      exact (ih h).trans (step_mask_length l v S)

/-- **Framed input of two natural numbers.**
Two canonical Nat blocks in the existing list framing. -/
def pairInput (m n : ℕ) : List Bool :=
  delimit (encodeNat m) ++ delimit (encodeNat n)

/-- **Labels of the binary addition machine.**
Original verifier labels plus initialization, clear, reverse, and halt. -/
abbrev Lab := SSVerify.Lab ⊕ Fin 4

/-- **Identity embedding of the verifier stacks.**
Reuse all original verifier stacks without re-encoding symbols. -/
def identity : SEmb (fun _ : SSVerify.K => Sym)
    (fun _ : SSVerify.K => Sym) where
  e := id
  inj := injective_id
  ι _ := Equiv.refl _

/-- **Redirection of the verifier's halt labels.**
Redirect the two halt labels, leaving every live label distinct. -/
def redirect : SSVerify.Lab → Lab
  | .yes | .no => .inr 1
  | l => .inl l

/-- **Only halt labels are redirected to the cleanup label.**
The cleanup continuation cannot alias any live verifier label. -/
@[simp] theorem redirect_eq_clear_iff (l : SSVerify.Lab) :
    redirect l = .inr 1 ↔ l = .yes ∨ l = .no := by
  cases l <;> simp [redirect]

/-- **Binary addition program built on the SUBSET-SUM machine.**
Run the existing sum machine, then clear the mask and restore LSB order.
Only the original halt labels are redirected to a continuation. -/
def prog : Lab → TM2.Stmt (fun _ : SSVerify.K => Sym) Lab Bool
  | .inl l => mapS identity redirect (SSVerify.prog l)
  | .inr i =>
    if i = 0 then
      .push .W (fun _ => .bit true) <|
        .push .W (fun _ => .bit true) <| .goto fun _ => .inl .next
    else if i = 1 then
      cleanS [.W] (.inr 1) (.inr 2)
    else if i = 2 then
      moveB .B .A Sym.bit? Sym.bit (.inr 2) (.inr 3)
    else .halt

private theorem embeds_sum : Embeds identity redirect SSVerify.prog prog := by
  intro l
  cases l <;> first | exact Or.inl rfl | exact Or.inr rfl

private theorem sum_two_run (m n : ℕ) (v : Bool) :
    let r := pairInput m n
    ∃ v' w', w'.length ≤ 2 ∧
      RunLe SSVerify.prog (r.length * (2 * r.length + 6) + r.length + 3)
        ⟨some .next, v,
          SSVerify.st (r.map .bit) [.bit true, .bit true] [] [] []⟩
        ⟨some (if encodeNat (m + n) = [] then .yes else .no), v',
          SSVerify.st [] w' [] [] ((encodeNat (m + n)).map .bit).reverse⟩ := by
  intro r
  obtain ⟨v', w', hr⟩ := SSVerifierSum.sum_component_run [m, n]
    [true, true] v
  have hrun : RunLe SSVerify.prog
      (r.length * (2 * r.length + 6) + r.length + 3)
      ⟨some .next, v,
        SSVerify.st (r.map .bit) [.bit true, .bit true] [] [] []⟩
      ⟨some (if encodeNat (m + n) = [] then .yes else .no), v',
        SSVerify.st [] w' [] [] ((encodeNat (m + n)).map .bit).reverse⟩ := by
    simpa [r, pairInput, SSVerify.pick] using hr
  obtain ⟨s, hs, hstep⟩ := hrun
  have hw := run_mask_length hstep
  exact ⟨v', w', by simpa using hw, s, hs, hstep⟩

private theorem sum_host_run (m n : ℕ) (v : Bool) :
    let r := pairInput m n
    ∃ v' w', w'.length ≤ 2 ∧
      RunLe prog (r.length * (2 * r.length + 6) + r.length + 3)
        ⟨some (.inl .next), v,
          SSVerify.st (r.map .bit) [.bit true, .bit true] [] [] []⟩
        ⟨some (.inr 1), v',
          SSVerify.st [] w' [] [] ((encodeNat (m + n)).map .bit).reverse⟩ := by
  intro r
  obtain ⟨v', w', hw, hr⟩ := sum_two_run m n v
  obtain ⟨T, ht, he, _⟩ := runLe_embed redirect embeds_sum hr
    (S' := SSVerify.st (r.map .bit) [.bit true, .bit true] [] [] [])
    (by intro k; simp [identity, r])
  have hT : T = SSVerify.st [] w' [] []
      ((encodeNat (m + n)).map .bit).reverse := by
    funext k
    simpa [identity] using he k
  have hl : redirect (if encodeNat (m + n) = [] then .yes else .no) =
      .inr 1 := by split <;> rfl
  rw [hl, hT] at ht
  exact ⟨v', w', hw, ht⟩

private theorem clear_mask_run (w b : List Sym) (v : Bool)
    (hw : w.length ≤ 2) :
    RunLe prog 3 ⟨some (.inr 1), v, SSVerify.st [] w [] [] b⟩
      ⟨some (.inr 2), false, SSVerify.st [] [] [] [] b⟩ := by
  have h := clean_run (M := prog) (ks := [SSVerify.K.W])
    (self := .inr 1) (next := .inr 2) rfl (by simp) 2 v
    (SSVerify.st [] w [] [] b) (by simpa using hw)
  have he : (fun k => if k ∈ [SSVerify.K.W] then []
      else SSVerify.st [] w [] [] b k) =
      SSVerify.st [] [] [] [] b := by
    funext k
    cases k <;> simp [SSVerify.st]
  rwa [he] at h

private theorem restore_run (bits : List Bool) :
    ∃ v', Run prog (bits.length + 1)
      ⟨some (.inr 2), false,
        SSVerify.st [] [] [] [] (bits.map .bit).reverse⟩
      ⟨some (.inr 3), v', SSVerify.st [] [] [] (bits.map .bit) []⟩ := by
  obtain ⟨v', S, hr, hb, ha, hk⟩ := moveB_run (M := prog)
    (self := .inr 2) (next := .inr 3) rfl
    (show SSVerify.K.B ≠ SSVerify.K.A by decide) bits.reverse
    (bits.map Sym.bit).reverse [] false
    (SSVerify.st [] [] [] [] (bits.map .bit).reverse) (by simp)
    (by simp [IsBitBlock, Sym.bit?, Function.comp_def, List.map_reverse])
    (by simp [EndsBitBlock])
  have he : S = SSVerify.st [] [] [] (bits.map .bit) [] := by
    funext k
    cases k
    case A => simpa [List.map_reverse] using ha
    case B => simpa using hb
    all_goals exact hk _ (by decide) (by decide)
  exact ⟨v', by simpa [he] using hr⟩

/-- **Bit length of the sum is at most the input length.**
The canonical sum fits within the two framed operands' bit length. -/
theorem length_sum_le_input (m n : ℕ) :
    (encodeNat (m + n)).length ≤ (pairInput m n).length := by
  have h := SSVerify.length_addB false (encodeNat m) (encodeNat n)
  rw [SSVerify.addB_encodeNat, Bool.toNat_false, Nat.add_zero] at h
  simp only [pairInput, List.length_append, length_delimit]
  omega

/-- **Binary addition of framed numbers in quadratic time.**
Add two canonically framed numbers, leaving only the LSB-first result.
The bound is quadratic in encoded input length; no loop enumerates values. -/
theorem run (m n : ℕ) (v : Bool) :
    let N := (pairInput m n).length
    ∃ v', RunLe prog (N * (2 * N + 6) + 2 * N + 8)
      ⟨some (.inr 0), v,
        SSVerify.st ((pairInput m n).map .bit) [] [] [] []⟩
      ⟨some (.inr 3), v',
        SSVerify.st [] [] [] ((encodeNat (m + n)).map .bit) []⟩ := by
  intro N
  obtain ⟨v₁, w, hw, hs⟩ := sum_host_run m n v
  have hi : Run prog 1
      ⟨some (.inr 0), v,
        SSVerify.st ((pairInput m n).map .bit) [] [] [] []⟩
      ⟨some (.inl .next), v, SSVerify.st ((pairInput m n).map .bit)
        [.bit true, .bit true] [] [] []⟩ := by
    apply Run.single
    simp [prog, TM2.stepAux]
  have hc := clear_mask_run w ((encodeNat (m + n)).map .bit).reverse v₁ hw
  obtain ⟨v₂, ho⟩ := restore_run (encodeNat (m + n))
  refine ⟨v₂, ((((hi.le le_rfl).trans hs).trans hc).trans
    (ho.le le_rfl)).mono ?_⟩
  have hl : (encodeNat (m + n)).length ≤ N := length_sum_le_input m n
  dsimp only [N] at hl ⊢
  omega

/-- **Embedded run of the binary addition component.**
The addition component runs in a host, with every external stack
unchanged and all embedded workspace cleared. -/
theorem run_embedded {K Λ : Type} [DecidableEq K] {Γ : K → Type}
    (E : SEmb (fun _ : SSVerify.K => Sym) Γ) (φ : Lab → Λ)
    (M : Λ → TM2.Stmt Γ Λ Bool) (hM : Embeds E φ prog M)
    (m n : ℕ) (v : Bool) (S : ∀ k, List (Γ k))
    (hS : Agree E (SSVerify.st ((pairInput m n).map .bit)
      [] [] [] []) S) :
    let N := (pairInput m n).length
    ∃ v' S', RunLe M (N * (2 * N + 6) + 2 * N + 8)
      ⟨some (φ (.inr 0)), v, S⟩ ⟨some (φ (.inr 3)), v', S'⟩ ∧
      Agree E (SSVerify.st [] [] []
        ((encodeNat (m + n)).map .bit) []) S' ∧ Frame E S S' := by
  obtain ⟨v', hr⟩ := run m n v
  obtain ⟨S', hs, ha, hf⟩ := runLe_embed φ hM hr hS
  exact ⟨v', S', hs, ha, hf⟩

end Cslib.Complexity.SSVerifierArithmetic
