/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.SatTokenizer
public import CSLibExt.Computability.Complexity.Host

/-!
# Tokenize a SAT encoding, then run an emitter on its token stack

Every Karp reduction out of SAT here reads a binary-index CNF encoding `x` and writes an instance
built from the formula. The SAT tokenizer (`SatTokenizer`) already decodes `x` into the token
stack `(toks φ).reverse`; a reduction only needs an *emitter*: a machine that, from the token
stack, writes the output on a stack of its own (`Emitter`). `TokThen.prog` runs the tokenizer
and then the emitter; on undecodable input it writes the fixed `Emitter.noOut` instead.

`TokThen.run`: from `x` on the input stack `X`, reach `fin` with the output stack holding
`out E x` (`E.g φ` if `decodeCNF x = some φ`, else `E.noOut`) within
`2 |x| + 3 + E.B |x|` steps. `TokThen.isPolyTime_out` turns this into `IsPolyTime (out E)` through
the reduction host (`Cslib.Complexity.Host`).
-/

@[expose] public section

namespace Cslib.Complexity.Karp

open Turing Function MetaMathlibExt MetaMathlibExt.TM2Program MetaMathlibExt.TM2Embedding
open Cslib.CookLevin Cslib.Logic.PL Cslib.Complexity.SatVerifier

/-- An emitter: a machine that writes an output on stack `cO` from the token stack on `cT`. -/
structure Emitter where
  /-- Stacks. -/
  K : Type
  [decK : DecidableEq K]
  /-- Alphabets. -/
  Γ : K → Type
  /-- Labels. -/
  L : Type
  [decL : DecidableEq L]
  /-- The program. -/
  prog : L → TM2.Stmt Γ L Bool
  /-- Start label. -/
  start : L
  /-- Exit label. -/
  done : L
  start_ne_done : start ≠ done
  prog_done : prog done = .halt
  /-- The token stack. -/
  cT : K
  /-- The output stack. -/
  cO : K
  cT_ne_cO : cT ≠ cO
  /-- Token symbols on `cT`. -/
  iT : Sym ≃ Γ cT
  /-- Output symbols on `cO` are bits. -/
  eO : Γ cO ≃ Bool
  /-- The output for a decodable input. -/
  g : CNF → List Bool
  /-- The output for an undecodable input. -/
  noOut : List Bool
  /-- The step bound, in the token count. -/
  B : ℕ → ℕ
  B_mono : Monotone B
  run : ∀ (φ : CNF) (v : Bool) (St : ∀ k, List (Γ k)), St cT = (toks φ).reverse.map iT →
    St cO = [] → (∀ k, k ≠ cT → k ≠ cO → St k = []) →
    ∃ v' S', RunLe prog (B (toks φ).length) ⟨some start, v, St⟩ ⟨some done, v', S'⟩ ∧
      S' cO = (g φ).map eO.symm

attribute [instance] Emitter.decK Emitter.decL

namespace TokThen

variable (E : Emitter)

/-- The output on bit string `x`. -/
def out (x : List Bool) : List Bool :=
  match decodeCNF x with
  | some φ => E.g φ
  | none => E.noOut

/-- Stacks: the tokenizer's (its own `T` stays unused) and the emitter's. -/
abbrev K := Tokenizer.K ⊕ E.K

/-- Alphabets. -/
@[reducible] def Γ : K E → Type
  | .inl _ => Sym
  | .inr k => E.Γ k

/-- Labels: the tokenizer's, the emitter's, `inr (inr false)` writes `noOut`, `inr (inr true)`
is the exit. -/
abbrev L := Tokenizer.Lab ⊕ E.L ⊕ Bool

/-- The exit label. -/
def fin : L E := .inr (.inr true)

/-- Tokenizer stacks: its token stack is the emitter's. -/
def eT : Tokenizer.K → K E
  | .T => .inr E.cT
  | .X => .inl .X
  | .W => .inl .W
  | .B => .inl .B
  | .CC => .inl .CC
  | .LC => .inl .LC

/-- The tokenizer's stack embedding. -/
def embT : SEmb (fun _ : Tokenizer.K => Sym) (Γ E) where
  e := eT E
  inj a b h := by cases a <;> cases b <;> first | rfl | exact absurd h (by simp [eT])
  ι k := match k with
    | .T => E.iT | .X => Equiv.refl Sym | .W => Equiv.refl Sym | .B => Equiv.refl Sym
    | .CC => Equiv.refl Sym | .LC => Equiv.refl Sym

/-- The emitter's stack embedding. -/
def embE : SEmb E.Γ (Γ E) where
  e := .inr
  inj := Sum.inr_injective
  ι _ := Equiv.refl _

/-- Tokenizer labels: accept starts the emitter, reject writes `noOut`. -/
def φT (l : Tokenizer.Lab) : L E :=
  if l = .acc then .inr (.inl E.start) else if l = .rej then .inr (.inr false) else .inl l

/-- Emitter labels: its exit is `fin`. -/
def φE (l : E.L) : L E := if l = E.done then fin E else .inr (.inl l)

/-- The program. -/
def prog : L E → TM2.Stmt (Γ E) (L E) Bool
  | .inl l => mapS (embT E) (φT E) (Tokenizer.prog l)
  | .inr (.inl l) => mapS (embE E) (φE E) (E.prog l)
  | .inr (.inr false) =>
      emit (Γ := Γ E) (.inr E.cO) ((E.noOut.map E.eO.symm).reverse) (fin E)
  | .inr (.inr true) => .halt

/-- The start label. -/
def start : L E := .inl Tokenizer.start

/-- Initial stacks: `x` on the tokenizer's input stack. -/
def init (x : List Bool) : ∀ k, List (Γ E k) := update (fun _ => []) (.inl .X) (x.map Sym.bit)

theorem embeds_tok : Embeds (embT E) (φT E) Tokenizer.prog (prog E) := by
  intro l
  by_cases ha : l = .acc
  · subst ha; exact .inr rfl
  by_cases hr : l = .rej
  · subst hr; exact .inr rfl
  left
  simp only [φT, ha, hr, if_false, prog]

theorem embeds_em : Embeds (embE E) (φE E) E.prog (prog E) := by
  intro l
  by_cases hd : l = E.done
  · subst hd; exact .inr E.prog_done
  left
  simp only [φE, hd, if_false, prog]

/-- The tokenizer's initial stacks. -/
def tokS (x : List Bool) : ∀ _ : Tokenizer.K, List Sym := update (fun _ => []) .X (x.map Sym.bit)

theorem agree_init (x : List Bool) : Agree (embT E) (tokS x) (init E x) := by
  intro k
  cases k
  · show init E x (.inl .X) = (x.map Sym.bit).map (fun a => a); simp [init]
  · show init E x (.inl .W) = ([] : List Sym).map (fun a => a); simp [init]
  · show init E x (.inr E.cT) = ([] : List Sym).map E.iT; simp [init]
  · show init E x (.inl .B) = ([] : List Sym).map (fun a => a); simp [init]
  · show init E x (.inl .CC) = ([] : List Sym).map (fun a => a); simp [init]
  · show init E x (.inl .LC) = ([] : List Sym).map (fun a => a); simp [init]

theorem mem_range_eT {k : K E} (h : ∃ k', eT E k' = k) : k = .inr E.cT ∨ ∃ k', k = .inl k' := by
  obtain ⟨k', rfl⟩ := h
  cases k' <;> simp [eT]

/-- **Tokenize, then emit**. -/
theorem run (x : List Bool) :
    ∃ v S', RunLe (prog E) (2 * x.length + 3 + E.B x.length) ⟨some (start E), false, init E x⟩
      ⟨some (fin E), v, S'⟩ ∧ S' (.inr E.cO) = (out E x).map E.eO.symm := by
  have hφs : φT E Tokenizer.start = start E := by simp [φT, Tokenizer.start, start]
  have hnot : ∀ k : E.K, k ≠ E.cT → ∀ k', eT E k' ≠ .inr k := by
    intro k hk k' h; cases k' <;> simp [eT] at h; exact hk h.symm
  cases hdec : decodeCNF x with
  | none =>
      obtain ⟨v₂, S₂, r⟩ := Tokenizer.run_none (w := []) hdec false (tokS x) (by simp [tokS])
        (by simp [tokS, update_of_ne]) (by simp [tokS, update_of_ne]) (by simp [tokS, update_of_ne])
      obtain ⟨T₁, r₁, -, hfr₁⟩ := runLe_embed (φT E) (embeds_tok E) r (agree_init E x)
      rw [hφs, show φT E .rej = .inr (.inr false) by simp [φT]] at r₁
      have hO : T₁ (.inr E.cO) = [] := by
        rw [hfr₁ _ (hnot _ (Ne.symm E.cT_ne_cO))]; simp [init]
      refine ⟨v₂, _, (r₁.trans ((emit_run (M := prog E) rfl v₂ T₁).le le_rfl)).mono ?_, ?_⟩
      · omega
      · simp [out, hdec, hO]
  | some φ =>
      have hx : x = encodeCNF φ := (decodeCNF_eq_some_iff x φ).mp hdec
      obtain ⟨v₂, S₂, r, -, -, -, -, s2T, -⟩ := Tokenizer.run_some (w := []) hdec false (tokS x)
        (by simp [tokS]) (by simp [tokS, update_of_ne]) (by simp [tokS, update_of_ne])
        (by simp [tokS, update_of_ne])
      obtain ⟨T₁, r₁, hag₁, hfr₁⟩ := runLe_embed (φT E) (embeds_tok E) r (agree_init E x)
      rw [hφs, show φT E .acc = .inr (.inl E.start) by simp [φT]] at r₁
      set St : ∀ k, List (E.Γ k) := fun k => T₁ (.inr k) with hSt
      have hT : St E.cT = (toks φ).reverse.map E.iT := by
        have h1 : T₁ (.inr E.cT) = (S₂ .T).map E.iT := hag₁ .T
        rw [s2T] at h1
        simpa [hSt, tokS, Function.update_apply] using h1
      have h0 : ∀ k, k ≠ E.cT → St k = [] := by
        intro k hk
        simp only [hSt]
        rw [hfr₁ _ (hnot k hk)]; simp [init]
      obtain ⟨v₃, S₃, re, hout⟩ := E.run φ v₂ St hT (h0 _ (Ne.symm E.cT_ne_cO))
        (fun k hk _ => h0 k hk)
      have hagE : Agree (embE E) St T₁ := fun k => by
        show T₁ (.inr k) = (T₁ (.inr k)).map (fun a => a); simp
      obtain ⟨T₂, r₂, hag₂, -⟩ := runLe_embed (φE E) (embeds_em E) re hagE
      rw [show φE E E.start = .inr (.inl E.start) by simp [φE, E.start_ne_done],
        show φE E E.done = fin E by simp [φE]] at r₂
      refine ⟨v₃, T₂, (r₁.trans r₂).mono ?_, ?_⟩
      · have htx : (toks φ).length ≤ x.length := hx ▸ SatVerifier.toks_length_le φ
        have := E.B_mono htx
        omega
      · have h2 : T₂ (.inr E.cO) = (S₃ E.cO).map (fun a => a) := hag₂ E.cO
        rw [h2, hout]; simp [out, hdec]

/-- The tokenizer's stacks, listed. -/
def tokKs : List Tokenizer.K := [.X, .W, .T, .B, .CC, .LC]

theorem mem_tokKs (k : Tokenizer.K) : k ∈ tokKs := by cases k <;> decide

/-- The combined machine as a host component, given finiteness data for the emitter. -/
def comp [Fintype E.K] [∀ k, Fintype (E.Γ k)] [Fintype E.L] (eks : List E.K) (hnd : eks.Nodup)
    (hmem : ∀ k, k ∈ eks) : Host.Comp where
  K := K E
  Γ := Γ E
  finΓ := fun k => match k with
    | .inl _ => SatVerifier.Sym.instFintype
    | .inr k => inferInstanceAs (Fintype (E.Γ k))
  L := L E
  prog := prog E
  ks := tokKs.map .inl ++ eks.map .inr
  ks_nodup := by
    refine List.nodup_append.2 ⟨(by decide : tokKs.Nodup).map Sum.inl_injective,
      hnd.map Sum.inr_injective, ?_⟩
    simp
  mem_ks := fun k => by
    rcases k with k | k
    · exact List.mem_append_left _ (List.mem_map_of_mem (mem_tokKs k))
    · exact List.mem_append_right _ (List.mem_map_of_mem (hmem k))

/-- **Reductions out of SAT are polynomial-time**: given an emitter and a polynomial bounding
`2 n + 3 + E.B n`, the map `out E` is `IsPolyTime`. -/
theorem isPolyTime_out [Fintype E.K] [∀ k, Fintype (E.Γ k)] [Fintype E.L] (eks : List E.K)
    (hnd : eks.Nodup) (hmem : ∀ k, k ∈ eks) (p : Polynomial ℕ)
    (hp : ∀ n, 2 * n + 3 + E.B n ≤ p.eval n) :
    MetaMathlibExt.ComplexityTheory.IsPolyTime (out E) :=
  Host.isPolyTime_reduction (c := comp E eks hnd hmem) (cX := .inl .X) (cO := .inr E.cO)
    (gX := Sym.bit) (start := start E) (done := fin E) E.eO (out E) p rfl fun x => by
      obtain ⟨v, S', r, h⟩ := run E x
      exact ⟨v, S', r.mono (hp _), h⟩

end TokThen

end Cslib.Complexity.Karp
