/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright 2026 Joshua Tan.
Authors: Joshua Tan (original development); ported by Adam Kiezun and Metamate.

Adapted from `Asm.lean` of `JoshuaTan42/millennium-cook-levin` at commit
`879c4835640119ad009abeb62ebd7a96f87eb9e8`
(<https://github.com/JoshuaTan42/millennium-cook-levin/blob/879c4835640119ad009abeb62ebd7a96f87eb9e8/Asm.lean>),
licensed under the Apache License, Version 2.0
(<https://www.apache.org/licenses/LICENSE-2.0>). Changes: module-system header and imports,
`Cslib.Complexity.CookLevin` namespaces, deprecated lemma
names updated; module docstring rewritten for this repository (the source's notes and status lines
dropped), missing docstrings added, long lines wrapped.
-/

module

public import MathlibExt.Computability.TuringMachine.StackEmbedding
public import CSLibExt.Computability.Complexity.CookLevin.Accept
public import CSLibExt.Computability.Complexity.CookLevin.InitFamily

/-!
# Cook-Levin: the five generators as sub-machines of one host

* The host stacks: one shared output, one input-code stack, and a private, disjoint counter block
  per generator (update, situation definition, shift, accept, init), with the five stack
  embeddings (`TM2Embedding.SEmb`).
* The host program `hprog` runs init, update, situation definition, shift and accept in sequence
  (one chaining step between generators); `seq_run` is the sequencing theorem, generic in the five
  sub-programs.
* `realProg` instantiates the five real generators for a verifier; `real_run` shows that, from
  preloaded counters, the host emits exactly `encodeCNF (Phi …)`, and `phi_iff` that `Phi` is
  satisfiable iff some certificate makes the verifier accept (from `Situation.Enc.five_iff`).
-/

@[expose] public section


namespace Cslib.Complexity.CookLevin.Assembly

open MetaMathlibExt

open MetaMathlibExt.TM2Program Cslib.Complexity.DenseSAT MetaMathlibExt.TM2Embedding Turing Function
open Cslib.Complexity.CookLevin.CounterView (SK SΓ)
open Cslib.Complexity.CookLevin.InitFamily (IK IΓ emb)

/-! ## [HOST] Host stacks and the five embeddings -/

/-- **Stacks of the Cook–Levin host machine.** The host has a shared output stack, an input-code
stack, and five private counter blocks: an update block and a situation-definition block, each
with one stack per counter of the family generator, and a shift block, an accept block and an
init block, with one stack per counter of the shift, accept and init generator respectively. -/
inductive HK
  | out
  | inp
  | up (x : Family.CK)
  | sd (x : Family.CK)
  | sh (x : Shift.CK)
  | ac (x : Accept.CK)
  | ini (x : InitFamily.CK)
  deriving DecidableEq, Fintype

/-- **Alphabets of the Cook–Levin host machine.** For $g \in \mathbb{N}$, the host stacks carry
the following alphabets: the shared output stack holds Booleans, the input-code stack holds codes
in $\{0, \dots, g - 1\}$, and every stack of every private counter block has a one-element
alphabet. -/
abbrev HΓ (g : ℕ) : HK → Type
  | .out => Bool
  | .inp => Fin g
  | .up _ => Unit
  | .sd _ => Unit
  | .sh _ => Unit
  | .ac _ => Unit
  | .ini _ => Unit

section Embs

variable (g : ℕ)

/-- **Host stack renaming for the update generator.** The map from the stacks of the
clause-family generator, used as the update generator, to the host stacks that sends the output
stack to the shared output stack and the counter stack of each counter $x$ to the counter $x$ of
the host's update block. -/
def eU : Family.GK → HK
  | .out => .out
  | .c x => .up x

/-- **Host stack renaming for the situation-definition generator.** The map from the stacks of
the clause-family generator, used as the situation-definition generator, to the host stacks that
sends the output stack to the shared output stack and the counter stack of each counter $x$ to
the counter $x$ of the host's situation-definition block. -/
def eS : Family.GK → HK
  | .out => .out
  | .c x => .sd x

/-- **Host stack renaming for the shift generator.** The map from the stacks of the shift
generator to the host stacks that sends the output stack to the shared output stack and the
counter stack of each shift counter $x$ to the counter $x$ of the host's shift block. -/
def eH : SK Shift.CK → HK
  | .out => .out
  | .c x => .sh x

/-- **Host stack renaming for the accept generator.** The map from the stacks of the accept
generator to the host stacks that sends the output stack to the shared output stack and the
counter stack of each accept counter $x$ to the counter $x$ of the host's accept block. -/
def eA : SK Accept.CK → HK
  | .out => .out
  | .c x => .ac x

/-- **Host stack renaming for the init generator.** The map from the stacks of the init
generator to the host stacks that sends the output stack to the shared output stack, the input
stack to the host's input-code stack, and the counter stack of each init counter $x$ to the
counter $x$ of the host's init block. -/
def eI : IK InitFamily.CK → HK
  | .b .out => .out
  | .b (.c x) => .ini x
  | .inp => .inp

/-- **Embedding of the update generator's stacks into the host.** For $g \in \mathbb{N}$, this is
the stack embedding of the family generator's stacks (a Boolean output stack and one unit counter
stack per counter) into the host stacks with $g$ input codes, used for the update generator: the
output stack goes to the host's shared output stack, and the counter stack $x$ goes to the stack
$x$ of the host's private update block. Distinct stacks go to distinct host stacks, and each
stack's alphabet is identified with its host stack's alphabet by the identity. -/
def embU : SEmb Family.GΓ (HΓ g) where
  e := eU
  inj := by intro a b h; cases a <;> cases b <;> simp_all [eU]
  ι := fun k => match k with
    | .out => Equiv.refl _
    | .c _ => Equiv.refl _

/-- **Embedding of the situation-definition generator into the host.** For $g$ input codes, the
stack embedding of the clause-family generator's stacks, used as the situation-definition
generator, into the host stacks that sends the output stack to the shared output stack and the
counter stack of each counter $x$ to the counter $x$ of the host's situation-definition block,
identifying each stack's alphabet with itself. -/
def embS : SEmb Family.GΓ (HΓ g) where
  e := eS
  inj := by intro a b h; cases a <;> cases b <;> simp_all [eS]
  ι := fun k => match k with
    | .out => Equiv.refl _
    | .c _ => Equiv.refl _

/-- **Embedding of the shift generator into the host.** For $g$ input codes, the stack embedding
of the shift generator's stacks into the host stacks that sends the output stack to the shared
output stack and the counter stack of each shift counter $x$ to the counter $x$ of the host's
shift block, identifying each stack's alphabet with itself. -/
def embH : SEmb (SΓ Shift.CK) (HΓ g) where
  e := eH
  inj := by intro a b h; cases a <;> cases b <;> simp_all [eH]
  ι := fun k => match k with
    | .out => Equiv.refl _
    | .c _ => Equiv.refl _

/-- **Embedding of the accept generator into the host.** For $g$ input codes, the stack embedding
of the accept generator's stacks into the host stacks that sends the output stack to the shared
output stack and the counter stack of each accept counter $x$ to the counter $x$ of the host's
accept block, identifying each stack's alphabet with itself. -/
def embA : SEmb (SΓ Accept.CK) (HΓ g) where
  e := eA
  inj := by intro a b h; cases a <;> cases b <;> simp_all [eA]
  ι := fun k => match k with
    | .out => Equiv.refl _
    | .c _ => Equiv.refl _

/-- **Embedding of the init generator into the host.** For $g$ input codes, the stack embedding
of the init generator's stacks (with input alphabet the $g$ codes) into the host stacks that
sends the output stack to the shared output stack, the input stack to the host's input-code
stack, and the counter stack of each init counter $x$ to the counter $x$ of the host's init
block, identifying each stack's alphabet with itself. -/
def embI : SEmb (IΓ InitFamily.CK (Fin g)) (HΓ g) where
  e := eI
  inj := by
    intro a b h
    rcases a with (_ | a) | _ <;> rcases b with (_ | b) | _ <;> simp_all [eI]
  ι := fun k => match k with
    | .b .out => Equiv.refl _
    | .b (.c _) => Equiv.refl _
    | .inp => Equiv.refl _

end Embs

/-! ### `Agree` from host stack values, and the output after a run -/

section AgreeLemmas

variable {g : ℕ} (S : ∀ k, List (HΓ g k))

theorem agree_U {F : Family.CK → ℕ} {o : List Bool} (ho : S .out = o)
    (hc : ∀ x, S (.up x) = cnt () (F x)) : Agree (embU g) (CounterView.st F o) S := by
  intro k; cases k <;> simp [embU, eU, ho, hc]
  exact (List.map_id _).symm

theorem agree_S {F : Family.CK → ℕ} {o : List Bool} (ho : S .out = o)
    (hc : ∀ x, S (.sd x) = cnt () (F x)) : Agree (embS g) (CounterView.st F o) S := by
  intro k; cases k <;> simp [embS, eS, ho, hc]
  exact (List.map_id _).symm

theorem agree_H {F : Shift.CK → ℕ} {o : List Bool} (ho : S .out = o)
    (hc : ∀ x, S (.sh x) = cnt () (F x)) : Agree (embH g) (CounterView.st F o) S := by
  intro k; cases k <;> simp [embH, eH, ho, hc]
  exact (List.map_id _).symm

theorem agree_A {F : Accept.CK → ℕ} {o : List Bool} (ho : S .out = o)
    (hc : ∀ x, S (.ac x) = cnt () (F x)) : Agree (embA g) (CounterView.st F o) S := by
  intro k; cases k <;> simp [embA, eA, ho, hc]
  exact (List.map_id _).symm

theorem agree_I {F : InitFamily.CK → ℕ} {o : List Bool} {xs : List (Fin g)} (ho : S .out = o)
    (hi : S .inp = xs) (hc : ∀ x, S (.ini x) = cnt () (F x)) :
    Agree (embI g) (emb (CounterView.st F o) xs) S := by
  intro k; rcases k with (_ | x) | _ <;> simp [embI, eI, ho, hi, hc] <;> exact (List.map_id _).symm

end AgreeLemmas

/-! ## [SEQ] The host program and the sequencing theorem -/

/-- **Labels of the Cook–Levin host machine.** For parameters $N, n_L, K, g, d, n_1, n_Y$, the
host labels consist of a copy of the family generator's labels (for $N$ situations and $n_L$
literals) for the update phase, a second copy of them for the situation-definition phase, a copy
of the shift generator's labels (for $N$ situations, $K$ stacks, $g$ symbols and depth $d$), a
copy of the accept generator's labels (for $n_1$ code clauses and $g$ symbols), a copy of the
init generator's labels (for $g$ symbols and $n_Y$ certificate codes), and one final label. -/
inductive HL (N nL KK g d n1 ny : ℕ)
  | up (l : Family.GL N nL)
  | sd (l : Family.GL N nL)
  | sh (l : Shift.GL N KK g d)
  | ac (l : Accept.GL n1 g)
  | ini (l : InitFamily.GL g ny)
  | fin
  deriving DecidableEq, Fintype

section Seq

variable {g N nL KK d n1 ny : ℕ}
  (Pu Ps : Family.GL N nL → TM2.Stmt Family.GΓ (Family.GL N nL) Bool)
  (Ph : Shift.GL N KK g d → TM2.Stmt (SΓ Shift.CK) (Shift.GL N KK g d) Bool)
  (Pa : Accept.GL n1 g → TM2.Stmt (SΓ Accept.CK) (Accept.GL n1 g) Bool)
  (Pi : InitFamily.GL g ny → TM2.Stmt (IΓ InitFamily.CK (Fin g)) (InitFamily.GL g ny) Bool)

/-- **Chaining step of the host program.** For a host label $l$, the chaining step is the host
statement that sets the Boolean internal state to false (the state in which every generator
starts) and then jumps to $l$. -/
def chain (l : HL N nL KK g d n1 ny) : TM2.Stmt (HΓ g) (HL N nL KK g d n1 ny) Bool :=
  .load (fun _ => false) (.goto fun _ => l)

/-- **The host program.** Given the five generator programs (update, situation definition, shift,
accept and init), the host program runs init, then update, then situation definition, then shift,
then accept. At each label of a generator other than its final label, the host executes that
generator's statement with the generator's stacks embedded into the host stacks (output onto the
shared output stack, counters onto the generator's own private counter block, and for init the
input stack onto the host's input-code stack) and its labels renamed into the host's copy of
them. At a generator's final label the host performs one chaining step: it resets the Boolean
state to false and jumps to the start label of the next generator, and after accept it jumps to
the final host label, where it halts. -/
def hprog : HL N nL KK g d n1 ny → TM2.Stmt (HΓ g) (HL N nL KK g d n1 ny) Bool
  | .ini l => if l = .done then chain (.up (.pre .eg)) else mapS (embI g) HL.ini (Pi l)
  | .up l => if l = .done then chain (.sd (.pre .eg)) else mapS (embU g) HL.up (Pu l)
  | .sd l => if l = .done then chain (.sh (.pre .eg)) else mapS (embS g) HL.sd (Ps l)
  | .sh l => if l = .done then chain (.ac (.pre .eg)) else mapS (embH g) HL.sh (Ph l)
  | .ac l => if l = .done then chain .fin else mapS (embA g) HL.ac (Pa l)
  | .fin => .halt

/-- **The host as a finite multi-stack Turing machine.** Given the five generator programs (update
and situation-definition programs over the family generator's stacks, a shift program, an accept
program, and an init program whose input alphabet has $g$ codes), the host machine is the finite
multi-stack Turing machine whose stacks are the host stacks, with the input-code stack as input
stack and the shared output stack as output stack, whose alphabets are the host alphabets, whose
labels are the host labels, whose start label is the init generator's start label, whose
internal state is a Boolean with initial value false, and whose program is the host program built
from the five generator programs.

This is a finiteness check only: the input and output stacks are provisional until the
precomputation is attached. -/
def hostTM : FinTM2 where
  K := HK
  k₀ := .inp
  k₁ := .out
  Γ := HΓ g
  Λ := HL N nL KK g d n1 ny
  main := .ini (.pre1 .eg)
  σ := Bool
  initialState := false
  m := hprog Pu Ps Ph Pa Pi

variable {Pu Ps Ph Pa Pi}

theorem embeds_I (h : Pi .done = .halt) : Embeds (embI g) HL.ini Pi (hprog Pu Ps Ph Pa Pi) := by
  intro l; by_cases hl : l = .done
  · exact Or.inr (hl ▸ h)
  · exact Or.inl (by simp only [hprog, ite_eq_right hl])

theorem embeds_U (h : Pu .done = .halt) : Embeds (embU g) HL.up Pu (hprog Pu Ps Ph Pa Pi) := by
  intro l; by_cases hl : l = .done
  · exact Or.inr (hl ▸ h)
  · exact Or.inl (by simp only [hprog, ite_eq_right hl])

theorem embeds_S (h : Ps .done = .halt) : Embeds (embS g) HL.sd Ps (hprog Pu Ps Ph Pa Pi) := by
  intro l; by_cases hl : l = .done
  · exact Or.inr (hl ▸ h)
  · exact Or.inl (by simp only [hprog, ite_eq_right hl])

theorem embeds_H (h : Ph .done = .halt) : Embeds (embH g) HL.sh Ph (hprog Pu Ps Ph Pa Pi) := by
  intro l; by_cases hl : l = .done
  · exact Or.inr (hl ▸ h)
  · exact Or.inl (by simp only [hprog, ite_eq_right hl])

theorem embeds_A (h : Pa .done = .halt) : Embeds (embA g) HL.ac Pa (hprog Pu Ps Ph Pa Pi) := by
  intro l; by_cases hl : l = .done
  · exact Or.inr (hl ▸ h)
  · exact Or.inl (by simp only [hprog, ite_eq_right hl])

theorem chain_run {l l' : HL N nL KK g d n1 ny} (h : hprog Pu Ps Ph Pa Pi l = chain l') (v : Bool)
    (S : ∀ k, List (HΓ g k)) :
    RunLe (hprog Pu Ps Ph Pa Pi) 1 ⟨some l, v, S⟩ ⟨some l', false, S⟩ :=
  (Run.single (by rw [h]; rfl)).le le_rfl

/-- **Sequencing.** Let $P_u$, $P_s$ (update and situation definition), $P_h$ (shift), $P_a$
(accept) and $P_i$ (init) be generator programs that halt at their label `done`, and let $\xi$ be
a list of input codes. Suppose that for each generator $j \in \{u, s, h, a, i\}$ there are counter
values $F_j$, a word $w_j$ and a bound $B_j$ such that, for every output word $o$, the run of $P_j$
from its start label with state bit false, on stacks holding the counters $F_j$ and the output $o$
(for init, also $\xi$ on its input stack), reaches `done` within $B_j$ steps, with some state bit
and with output $w_j o$. Let $o$ be a word and let $S_0$ be host stacks whose output stack holds
$o$, whose input stack holds $\xi$, and whose private block of each generator $j$ holds the
counters $F_j$. Then the host program on $P_u, P_s, P_h, P_a, P_i$, started at the init
generator's start label with state bit false on $S_0$, reaches its final label within
$B_i + B_u + B_s + B_h + B_a + 5$ steps, with some state bit and with output
$w_a w_h w_s w_u w_i o$. -/
theorem seq_run (hu0 : Pu .done = .halt) (hs0 : Ps .done = .halt) (hh0 : Ph .done = .halt)
    (ha0 : Pa .done = .halt) (hi0 : Pi .done = .halt)
    {Fu Fs : Family.CK → ℕ} {Fh : Shift.CK → ℕ} {Fa : Accept.CK → ℕ} {Fi : InitFamily.CK → ℕ}
    {xs : List (Fin g)} {wu ws wh wa wi : List Bool} {Bu Bs Bh Ba Bi : ℕ}
    (hu : ∀ o, ∃ (v : Bool) (S : ∀ k, List (Family.GΓ k)),
      RunLe Pu Bu ⟨some (.pre .eg), false, CounterView.st Fu o⟩ ⟨some .done, v, S⟩ ∧ S .out = wu ++ o)
    (hs : ∀ o, ∃ (v : Bool) (S : ∀ k, List (Family.GΓ k)),
      RunLe Ps Bs ⟨some (.pre .eg), false, CounterView.st Fs o⟩ ⟨some .done, v, S⟩ ∧ S .out = ws ++ o)
    (hh : ∀ o, ∃ (v : Bool) (S : ∀ k, List (SΓ Shift.CK k)),
      RunLe Ph Bh ⟨some (.pre .eg), false, CounterView.st Fh o⟩ ⟨some .done, v, S⟩ ∧ S .out = wh ++ o)
    (ha : ∀ o, ∃ (v : Bool) (S : ∀ k, List (SΓ Accept.CK k)),
      RunLe Pa Ba ⟨some (.pre .eg), false, CounterView.st Fa o⟩ ⟨some .done, v, S⟩ ∧ S .out = wa ++ o)
    (hi : ∀ o, ∃ (v : Bool) (S : ∀ k, List (IΓ InitFamily.CK (Fin g) k)),
      RunLe Pi Bi ⟨some (.pre1 .eg), false, emb (CounterView.st Fi o) xs⟩ ⟨some .done, v, S⟩ ∧
        S (.b .out) = wi ++ o)
    (S₀ : ∀ k, List (HΓ g k)) (o : List Bool) (ho : S₀ .out = o) (hin : S₀ .inp = xs)
    (cu : ∀ x, S₀ (.up x) = cnt () (Fu x)) (cs : ∀ x, S₀ (.sd x) = cnt () (Fs x))
    (ch : ∀ x, S₀ (.sh x) = cnt () (Fh x)) (ca : ∀ x, S₀ (.ac x) = cnt () (Fa x))
    (ci : ∀ x, S₀ (.ini x) = cnt () (Fi x)) :
    ∃ (v : Bool) (S : ∀ k, List (HΓ g k)),
      RunLe (hprog Pu Ps Ph Pa Pi) (Bi + Bu + Bs + Bh + Ba + 5)
        ⟨some (.ini (.pre1 .eg)), false, S₀⟩ ⟨some .fin, v, S⟩ ∧
      S .out = wa ++ (wh ++ (ws ++ (wu ++ (wi ++ o)))) := by
  -- init
  obtain ⟨v1, S1, r1, o1⟩ := hi o
  obtain ⟨T1, q1, a1, f1⟩ := runLe_embed HL.ini (embeds_I hi0) r1 (agree_I S₀ ho hin ci)
  have t1o : T1 .out = wi ++ o := ((a1 (.b .out)).trans (List.map_id _)).trans o1
  have t1u : ∀ x, T1 (.up x) = S₀ (.up x) := fun x =>
    f1 _ (fun k => by rcases k with (_ | _) | _ <;> simp [embI, eI])
  have t1s : ∀ x, T1 (.sd x) = S₀ (.sd x) := fun x =>
    f1 _ (fun k => by rcases k with (_ | _) | _ <;> simp [embI, eI])
  have t1h : ∀ x, T1 (.sh x) = S₀ (.sh x) := fun x =>
    f1 _ (fun k => by rcases k with (_ | _) | _ <;> simp [embI, eI])
  have t1a : ∀ x, T1 (.ac x) = S₀ (.ac x) := fun x =>
    f1 _ (fun k => by rcases k with (_ | _) | _ <;> simp [embI, eI])
  -- update
  obtain ⟨v2, S2, r2, o2⟩ := hu (wi ++ o)
  obtain ⟨T2, q2, a2, f2⟩ := runLe_embed HL.up (embeds_U hu0) r2
    (agree_U T1 t1o (fun x => (t1u x).trans (cu x)))
  have t2o : T2 .out = wu ++ (wi ++ o) := ((a2 .out).trans (List.map_id _)).trans o2
  have t2s : ∀ x, T2 (.sd x) = S₀ (.sd x) := fun x =>
    (f2 _ (fun k => by cases k <;> simp [embU, eU])).trans (t1s x)
  have t2h : ∀ x, T2 (.sh x) = S₀ (.sh x) := fun x =>
    (f2 _ (fun k => by cases k <;> simp [embU, eU])).trans (t1h x)
  have t2a : ∀ x, T2 (.ac x) = S₀ (.ac x) := fun x =>
    (f2 _ (fun k => by cases k <;> simp [embU, eU])).trans (t1a x)
  -- S-definition
  obtain ⟨v3, S3, r3, o3⟩ := hs (wu ++ (wi ++ o))
  obtain ⟨T3, q3, a3, f3⟩ := runLe_embed HL.sd (embeds_S hs0) r3
    (agree_S T2 t2o (fun x => (t2s x).trans (cs x)))
  have t3o : T3 .out = ws ++ (wu ++ (wi ++ o)) := ((a3 .out).trans (List.map_id _)).trans o3
  have t3h : ∀ x, T3 (.sh x) = S₀ (.sh x) := fun x =>
    (f3 _ (fun k => by cases k <;> simp [embS, eS])).trans (t2h x)
  have t3a : ∀ x, T3 (.ac x) = S₀ (.ac x) := fun x =>
    (f3 _ (fun k => by cases k <;> simp [embS, eS])).trans (t2a x)
  -- shift
  obtain ⟨v4, S4, r4, o4⟩ := hh (ws ++ (wu ++ (wi ++ o)))
  obtain ⟨T4, q4, a4, f4⟩ := runLe_embed HL.sh (embeds_H hh0) r4
    (agree_H T3 t3o (fun x => (t3h x).trans (ch x)))
  have t4o : T4 .out = wh ++ (ws ++ (wu ++ (wi ++ o))) :=
    ((a4 .out).trans (List.map_id _)).trans o4
  have t4a : ∀ x, T4 (.ac x) = S₀ (.ac x) := fun x =>
    (f4 _ (fun k => by cases k <;> simp [embH, eH])).trans (t3a x)
  -- accept
  obtain ⟨v5, S5, r5, o5⟩ := ha (wh ++ (ws ++ (wu ++ (wi ++ o))))
  obtain ⟨T5, q5, a5, _⟩ := runLe_embed HL.ac (embeds_A ha0) r5
    (agree_A T4 t4o (fun x => (t4a x).trans (ca x)))
  have t5o : T5 .out = wa ++ (wh ++ (ws ++ (wu ++ (wi ++ o)))) :=
    ((a5 .out).trans (List.map_id _)).trans o5
  refine ⟨false, T5, ?_, t5o⟩
  have c1 := chain_run (Pu := Pu) (Ps := Ps) (Ph := Ph) (Pa := Pa) (Pi := Pi)
    (l := .ini .done) (l' := .up (.pre .eg)) (by simp [hprog]) v1 T1
  have c2 := chain_run (Pu := Pu) (Ps := Ps) (Ph := Ph) (Pa := Pa) (Pi := Pi)
    (l := .up .done) (l' := .sd (.pre .eg)) (by simp [hprog]) v2 T2
  have c3 := chain_run (Pu := Pu) (Ps := Ps) (Ph := Ph) (Pa := Pa) (Pi := Pi)
    (l := .sd .done) (l' := .sh (.pre .eg)) (by simp [hprog]) v3 T3
  have c4 := chain_run (Pu := Pu) (Ps := Ps) (Ph := Ph) (Pa := Pa) (Pi := Pi)
    (l := .sh .done) (l' := .ac (.pre .eg)) (by simp [hprog]) v4 T4
  have c5 := chain_run (Pu := Pu) (Ps := Ps) (Ph := Ph) (Pa := Pa) (Pi := Pi)
    (l := .ac .done) (l' := .fin) (by simp [hprog]) v5 T5
  exact ((((((((((q1.trans c1).trans q2).trans c2).trans q3).trans c3).trans q4).trans c4).trans
    q5).trans c5).mono (by omega))

end Seq

/-! ## [REAL] The host on the five real generators of a machine `M`, linked to `five_iff` -/

section Real

open Cslib.Complexity.CookLevin.Situation

variable {M : FinTM2} (E : Enc M)

/-- **The host on the real generators of a machine.** Let $M$ be a finite multi-stack Turing
machine with encoding data $E$, let $Y$ be a list of input symbols, and let $\mathit{acc}$ be an
output symbol. This is the host program whose five generators are the real ones for $M$. The
update generator is the family generator of $E$ for the (label, state) codes, window codes and
next (label, state) codes of the situations of $E$. The situation-definition generator is the
family generator of $E$ for the same (label, state) codes and window codes, with the positions of
the situation variables in place of the next codes. The shift generator is the one of $E$. The
accept generator is the one for the number of (label, state) codes, the code of the halted label
with the initial internal state, the number of the output stack, and the code of $\mathit{acc}$
on the output stack. The init generator is the one for the code of the start label and initial
state of $M$, the number of the input stack, and the sorted distinct codes of the symbols of $Y$.
The input itself is not a parameter: the init generator reads it from the host's input-code
stack. -/
noncomputable abbrev realProg (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) :=
  hprog (Family.prog E.layout E.la E.na E.wa E.N) (Family.prog E.layout E.la E.sa E.wa E.N)
    (Shift.prog E.layout E.sa E.pl E.cn E.pu E.N)
    (Accept.prog E.layout E.A0 E.acode (E.kc M.k₁) (E.enc M.k₁ acc))
    (InitFamily.iprog E.layout (E.lc (some M.main,
        M.initialState)) (E.kc M.k₀) (InitFamily.ycs E Ys))

/-- **The formula emitted by the host.** Let $M$ be a finite multi-stack Turing machine with
encoding data $E$, let $x$ and $Y$ be lists of input symbols, let $\mathit{acc}$ be an output
symbol, and let $m, T \in \mathbb{N}$. Let $H = m + (T + 1) d + 1$ be the stack cap, where $d$ is
the window depth of $M$. The CNF formula $\Phi(x, Y, \mathit{acc}, m, T)$ is the concatenation, in
this order, of the accept family for $\mathit{acc}$, the shift family, the situation-definition
family, the update family, and the init family for $x$, $Y$ and $m$, all at run length $T$ and
stack cap $H$. -/
noncomputable def Phi (x Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (m T : ℕ) : CNF :=
  E.accFamily acc T (capH m T (depth M)) ++
    (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T (capH m T (depth M)) ++
      (Family.family E.layout E.la E.sa E.wa T (capH m T (depth M)) E.N ++
        (Family.family E.layout E.la E.na E.wa T (capH m T (depth M)) E.N ++
          E.initFamily x Ys m T (capH m T (depth M)))))

/-- **Step bound of the host.** Let $M$ be a finite multi-stack Turing machine with encoding data
$E$, let $Y$ be a list of input symbols, and let $m, T \in \mathbb{N}$. Let $H = m + (T + 1) d + 1$,
where $d$ is the window depth of $M$, and let $R = T + H + 1$. Let $L$ be the layout of $E$ and $N$
its number of situations. Let $c_I$ be the init generator's constant for $L$, the number of
distinct codes of symbols of $Y$, and the number of the input stack; let $c_F$ be the family
generator's constant for $L$ and $N$; let $c_S$ be the shift generator's constant for $L$ and $N$;
and let $c_A$ be the accept generator's constant for $L$, the number of (label, state) codes, and
the number of the output stack. The step bound is
$$c_I R^5 + c_F R^5 + c_F R^5 + c_S R^6 + c_A R^4 + 5,$$
the bounds of the init, update, situation-definition, shift and accept generators plus five
chaining steps. -/
noncomputable def realB (Ys : List (M.Γ M.k₀)) (m T : ℕ) : ℕ :=
  InitFamily.initC E.layout (InitFamily.ycs E Ys).length (E.kc M.k₀) * (T + capH m T (depth M) + 1) ^ 5 +
    Family.genC E.layout E.N * (T + capH m T (depth M) + 1) ^ 5 +
    Family.genC E.layout E.N * (T + capH m T (depth M) + 1) ^ 5 +
    Shift.shC E.layout E.N * (T + capH m T (depth M) + 1) ^ 6 +
    Accept.accC E.layout E.A0 (E.kc M.k₁) * (T + capH m T (depth M) + 1) ^ 4 + 5

/-- **The assembled generator, after the precomputation.** Let $E$ be an encoding of a machine
$M$, let $x$ and $Y$ be lists of input symbols of $M$, let $a$ be a symbol of its output stack,
and let $m, T \in \mathbb{N}$ with $|x| \le m$. Put $H = m + (T + 1)d + 1$, where $d$ is the
window depth of $M$. Let $S_0$ be host stacks whose output stack holds a word $o$, whose input
stack holds the symbol codes of $x$ in reverse order, whose update, situation-definition, shift
and accept blocks each hold $T$ on the time counter, $H$ on the height counter and nothing on the
other counters, and whose init block holds $T$, $|x|$, $m - |x|$ and $H - m$ on its four size
counters and nothing on the others. Then the host program on the real generators of $E$ for $Y$
and $a$, started at the init generator's start label with state bit false on $S_0$, reaches its
final label within the step bound $\mathrm{realB}(E, Y, m, T)$ (the five generators' bounds plus
five chaining steps), with some state bit and with output stack the dense encoding of the formula
$\Phi(E, x, Y, a, m, T)$ followed by $o$. -/
theorem real_run (x Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (m T : ℕ) (hx : x.length ≤ m)
    (S₀ : ∀ k, List (HΓ E.layout.g k)) (o : List Bool) (ho : S₀ .out = o)
    (hin : S₀ .inp = (x.map (InitFamily.encF E)).reverse)
    (cu : ∀ z, S₀ (.up z) = cnt () (Family.initF T (capH m T (depth M)) z))
    (cs : ∀ z, S₀ (.sd z) = cnt () (Family.initF T (capH m T (depth M)) z))
    (ch : ∀ z, S₀ (.sh z) = cnt () (Shift.initF T (capH m T (depth M)) z))
    (ca : ∀ z, S₀ (.ac z) = cnt () (Accept.initF T (capH m T (depth M)) z))
    (ci : ∀ z, S₀ (.ini z) = cnt () (InitFamily.initF T x.length (m - x.length)
      (capH m T (depth M) - m) z)) :
    ∃ (v : Bool) (S : ∀ k, List (HΓ E.layout.g k)),
      RunLe (realProg E Ys acc) (realB E Ys m T)
        ⟨some (.ini (.pre1 .eg)), false, S₀⟩ ⟨some .fin, v, S⟩ ∧
      S .out = encodeCNF (Phi E x Ys acc m T) ++ o := by
  have hH := depth_le_capH M m T
  have hpos : 0 < capH m T (depth M) := by unfold capH; omega
  obtain ⟨v, S, h, h'⟩ := seq_run rfl rfl rfl rfl rfl
    (fun o => upd_time E hH T o) (fun o => sdef_time E hH T o) (fun o => shift_time E hH T o)
    (fun o => Accept.acc_gen_time E acc T _ hpos o)
    (fun o => InitFamily.init_gen_capH E x Ys m T hx o) S₀ o ho hin cu cs ch ca ci
  refine ⟨v, S, h, ?_⟩
  rw [h']
  simp only [Phi, encodeCNF, List.flatMap_append, List.append_assoc]

/-- **Correctness of the assembled formula.** Let $M$ be a finite multi-stack Turing machine with
encoding data $E$, let $x$ and $Y$ be lists of input symbols of $M$, let $\mathit{acc}$ be an
output symbol of $M$, and let $m, T \in \mathbb{N}$. Suppose that $|x| \le m$ and that
$\mathit{acc}$ is one of the effective symbols of the output stack under $E$. Then the formula
$\Phi(x, Y, \mathit{acc}, m, T)$ emitted by the host is satisfiable if and only if there is a list
$y$ of input symbols, all belonging to $Y$, such that the concatenation $xy$ has length at most
$m$ and the idle-extended run of $M$ from the initial configuration on input $xy$ is, after $T$
steps, an accepting configuration for $\mathit{acc}$: halted, in the initial internal state, with
$\mathit{acc}$ on top of the output stack.

The proof carries the soundness and completeness of the five families through the
concatenation. -/
theorem phi_iff {x Ys : List (M.Γ M.k₀)} {acc : M.Γ M.k₁} {m T : ℕ} (hx : x.length ≤ m)
    (hacc : ∃ i, E.dec M.k₁ i = acc) :
    (∃ a, cnfSat (Phi E x Ys acc m T) a) ↔
      ∃ y : List (M.Γ M.k₀), (∀ z ∈ y, z ∈ Ys) ∧ (x ++ y).length ≤ m ∧
        Accepts M (runI M (initList M (x ++ y)) T) acc := by
  rw [← E.five_iff hx hacc]
  simp only [Phi, cnfSat_append]
  constructor
  · rintro ⟨a, ha, hh, hs, hu, hi⟩; exact ⟨a, hu, hs, hh, hi, ha⟩
  · rintro ⟨a, hu, hs, hh, hi, ha⟩; exact ⟨a, ha, hh, hs, hu, hi⟩

end Real

end Cslib.Complexity.CookLevin.Assembly
