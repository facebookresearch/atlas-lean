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

/-- **Emitter.** An emitter is a multi-stack machine, given by a type of stacks and a type of
labels (both with decidable equality), an alphabet for each stack and a program with boolean
state, together with a start label and a different exit label at which the program halts, a
token stack and a different output stack, a bijection from the SAT token symbols to the token
stack's alphabet, a bijection from the output stack's alphabet to the booleans, an output map
$g$ from CNF formulas to bit strings, a bit string reserved as the output for undecodable inputs,
and a monotone step bound $B : \mathbb{N} \to \mathbb{N}$. It must satisfy: for every CNF formula
$\varphi$ whose token sequence has length $n$, every initial state, and all stack contents in
which the token stack holds the token sequence of $\varphi$ in reverse, each token translated by
the token bijection, and every other stack is empty, the program goes from the start label to
the exit label in at most $B(n)$ steps and ends with the output stack holding $g(\varphi)$, each
bit translated by the inverse of the output bijection. -/
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

/-- **Output of an emitter on a bit string.** For an emitter $E$ with output map $g$ and a bit
string $x$: if the length-prefixed CNF decoder reads a CNF formula $\varphi$ from $x$ with no bits
left over, the output is $g(\varphi)$; otherwise it is the bit string that $E$ reserves as the
output for undecodable inputs. -/
def out (x : List Bool) : List Bool :=
  match decodeCNF x with
  | some φ => E.g φ
  | none => E.noOut

/-- **Stacks of the tokenize-then-emit machine.** The stacks of the tokenize-then-emit machine for
an emitter $E$ are the disjoint union of the SAT tokenizer's stacks and $E$'s stacks.

The copy of the tokenizer's own token stack $T$ stays unused: the tokenizer writes its tokens on
$E$'s token stack. -/
abbrev K := Tokenizer.K ⊕ E.K

/-- **Alphabets of the tokenize-then-emit machine.** For an emitter $E$, every stack of the
combined machine that comes from the SAT tokenizer has the tokenizer's symbol alphabet, and every
stack $k$ that comes from $E$ has the alphabet of $k$ in $E$. -/
@[reducible] def Γ : K E → Type
  | .inl _ => Sym
  | .inr k => E.Γ k

/-- **Labels of the tokenize-then-emit machine.** For an emitter $E$, the labels of the combined
machine form the disjoint union of the SAT tokenizer's labels, the labels of $E$, and the two
booleans: false labels the step that writes the output $E$ fixes for undecodable input, and true
is the exit label. -/
abbrev L := Tokenizer.Lab ⊕ E.L ⊕ Bool

/-- **Exit label of the tokenize-then-emit machine.** The labels of the tokenize-then-emit machine
for an emitter $E$ are the SAT tokenizer's labels, $E$'s labels and two extra labels indexed by
the booleans; the exit label is the extra label indexed by true. -/
def fin : L E := .inr (.inr true)

/-- **Tokenizer stacks in the tokenize-then-emit machine.** The map from the SAT tokenizer's
stacks to the stacks of the tokenize-then-emit machine for an emitter $E$ that sends the
tokenizer's token stack $T$ to $E$'s token stack, and each other tokenizer stack ($X$, $W$, $B$,
$CC$, $LC$) to its own copy among the tokenizer stacks of the combined machine. -/
def eT : Tokenizer.K → K E
  | .T => .inr E.cT
  | .X => .inl .X
  | .W => .inl .W
  | .B => .inl .B
  | .CC => .inl .CC
  | .LC => .inl .LC

/-- **Embedding the tokenizer's stacks into tokenize-then-emit.** The stack embedding of the SAT
tokenizer into the tokenize-then-emit machine for an emitter $E$: the tokenizer's token stack $T$
goes to $E$'s token stack, with token symbols translated by $E$'s bijection from token symbols to
that stack's alphabet, and each other tokenizer stack goes to its own copy among the tokenizer
stacks of the combined machine, with symbols left unchanged. -/
def embT : SEmb (fun _ : Tokenizer.K => Sym) (Γ E) where
  e := eT E
  inj a b h := by cases a <;> cases b <;> first | rfl | exact absurd h (by simp [eT])
  ι k := match k with
    | .T => E.iT | .X => Equiv.refl Sym | .W => Equiv.refl Sym | .B => Equiv.refl Sym
    | .CC => Equiv.refl Sym | .LC => Equiv.refl Sym

/-- **Embedding the emitter's stacks into tokenize-then-emit.** The stack embedding of an emitter
$E$ into the tokenize-then-emit machine for $E$: each stack of $E$ goes to its own copy among the
emitter stacks of the combined machine, which carries the same alphabet, and symbols are left
unchanged. -/
def embE : SEmb E.Γ (Γ E) where
  e := .inr
  inj := Sum.inr_injective
  ι _ := Equiv.refl _

/-- **Renaming the tokenizer's labels.** For an emitter $E$, the tokenizer's accepting label goes
to the start label of $E$, its rejecting label goes to the label of the combined machine that
writes the output $E$ fixes for undecodable input, and every other tokenizer label goes to its own
copy among the combined machine's labels. -/
def φT (l : Tokenizer.Lab) : L E :=
  if l = .acc then .inr (.inl E.start) else if l = .rej then .inr (.inr false) else .inl l

/-- **Emitter labels in the tokenize-then-emit machine.** The map from the labels of an emitter
$E$ to the labels of the tokenize-then-emit machine for $E$ that sends $E$'s exit label to the
machine's exit label, and every other label of $E$ to its own copy among the emitter labels. -/
def φE (l : E.L) : L E := if l = E.done then fin E else .inr (.inl l)

/-- **Program of the tokenize-then-emit machine.** For an emitter $E$, the combined machine acts as
follows. At a label of the SAT tokenizer it runs the tokenizer's statement for that label, with the
tokenizer's token stack replaced by the token stack of $E$ (token symbols identified with those of
$E$), its other stacks kept as copies, and its labels renamed: acceptance goes to the start label
of $E$, rejection goes to the step that writes the undecodable-input output, and every other label
goes to its own copy. At a label of $E$ it runs the statement of $E$ on the stacks of $E$, with the
exit label of $E$ renamed to the exit label of the combined machine and every other label of $E$
kept. At the label for undecodable input it pushes, in one step, the fixed output that $E$ assigns
to undecodable input, as output symbols of $E$, onto the output stack of $E$ (so that the stack
then reads that output from the top) and goes to the exit label. At the exit label the machine
halts. -/
def prog : L E → TM2.Stmt (Γ E) (L E) Bool
  | .inl l => mapS (embT E) (φT E) (Tokenizer.prog l)
  | .inr (.inl l) => mapS (embE E) (φE E) (E.prog l)
  | .inr (.inr false) =>
      emit (Γ := Γ E) (.inr E.cO) ((E.noOut.map E.eO.symm).reverse) (fin E)
  | .inr (.inr true) => .halt

/-- **Start label of the tokenize-then-emit machine.** For an emitter $E$, the combined machine
starts at the start label of the SAT tokenizer. -/
def start : L E := .inl Tokenizer.start

/-- **Initial stacks of the tokenize-then-emit machine.** For a bit string $x$, the initial stack
contents of the tokenize-then-emit machine for an emitter $E$: the tokenizer's input stack $X$
holds the bits of $x$ in order, each written as a bit symbol, and every other stack is empty. -/
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

/-- **Initial stacks of the tokenizer.** For a bit string $x$, the SAT tokenizer's initial stacks
hold $x$, as bit symbols, on the formula-bit stack $X$ and leave every other stack empty. -/
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

/-- **Tokenize, then emit.** Let $E$ be an emitter with step bound $B$, and let $x$ be a bit
string. The tokenize-then-emit machine for $E$, started at its start label with internal state
false, with $x$ as bit symbols on the tokenizer's input stack and every other stack empty,
reaches its exit label, with some internal state, in at most $2|x| + 3 + B(|x|)$ steps, and the
output stack of $E$ then holds the output on $x$, written in the output symbols of $E$. -/
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

/-- **List of the tokenizer's stacks.** The list of the SAT tokenizer's six stacks in the order:
the formula-bit stack $X$, the witness-bit stack $W$, the token stack $T$, the table stack $B$,
the clause counter $CC$ and the literal counter $LC$. -/
def tokKs : List Tokenizer.K := [.X, .W, .T, .B, .CC, .LC]

theorem mem_tokKs (k : Tokenizer.K) : k ∈ tokKs := by cases k <;> decide

/-- **The tokenize-then-emit machine as a host component.** Given an emitter $E$ with finitely
many stacks, finite stack alphabets and finitely many labels, and a list of $E$'s stacks that
contains every stack exactly once, this is the reduction-host component whose stacks, alphabets,
labels and program are those of the tokenize-then-emit machine for $E$, with its stacks listed
as the SAT tokenizer's six stacks followed by the given list of $E$'s stacks. -/
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

/-- **Emitter reductions out of SAT are polynomial-time.** Let $E$ be an emitter with finitely
many stacks, finite stack alphabets and finitely many labels, given together with a list of its
stacks that contains every stack exactly once. Write $B$ for the step bound of $E$, $g$ for its
output map and $o$ for its output on undecodable inputs, and let $p$ be a polynomial with
natural-number coefficients such that $2n + 3 + B(n) \le p(n)$ for every $n$. Then the map
sending a bit string $x$ to $g(\varphi)$ when $x$ is the binary code of a CNF formula $\varphi$
(its clause count in unary followed by the encoded clauses), and to $o$ otherwise, is
polynomial-time computable for the canonical bit-string encoding of lists of booleans. -/
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
