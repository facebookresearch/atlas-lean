/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.EncodingConverters
public import MathlibExt.Computability.TuringMachine.BitOps
public import MathlibExt.Computability.TuringMachine.Cleanup
public import MathlibExt.Computability.TuringMachine.Composition
public import MathlibExt.Computability.TuringMachine.StackEmbedding
public import Mathlib.Tactic.Ring

/-!
# Generic hosts for component machines

A Karp reduction or an NP verifier written as a hand-made `TM2` program does its work in a
*component*: a program on a few stacks of its own, started with its input on some of them. To
get a `TM2ComputableInPolyTime` out of it, a *host* must move the input off the canonical input
stack, run the component, empty every work stack and leave exactly the answer on the output
stack. This file builds that host once, for every component.

* `Comp`: a component machine (finitely many stacks and labels, state `Bool`).
* `reduction`: from a component that turns the bits `x` on its stack `cX` into `f x` on its stack
  `cO` within `p |x|` steps, a `TM2ComputableInPolyTime` for `f` on raw bit lists;
  `isPolyTime_reduction` composes it with `DecodeBits.computable` and `EncodeBits.computable`.
* `verifier`: from a component that starts with `x` on `cX` and `w` on `cW` and stops at label
  `yes` or `no` according to `f x w` within `p (|x| + |w|)` steps, a `TM2ComputableInPolyTime` on
  the `x # w` input `Verifier.pairEncode`; `isPolyTime_verifier` composes it with
  `Converter.computable`.

The host stacks are `inp | out | X1 | W1 | comp k`, the component's stacks embedded by
`TM2Embedding.SEmb` with `e := comp`. Phase 0 moves each input block onto its component stack
with two `moveB` passes through a buffer (`X1` or `W1`), so the order is kept, and resets the
state. The component then runs embedded (`runLe_embed`); its exit labels lead to a `cleanS` loop
that empties every stack but the output. The cleanup's length is bounded by the stack sizes,
which the step count bounds (`TM2Composition.length_iter`).
-/

@[expose] public section

namespace Cslib.Complexity.Host

open Turing Function MetaMathlibExt MetaMathlibExt.TM2Program MetaMathlibExt.TM2Embedding
  Cslib.Complexity.DenseSAT

/-- **Component machine.** A component machine consists of a finite type $K$ of stacks with
decidable equality, a finite alphabet $\Gamma_k$ for each stack $k$, a finite type $L$ of labels
with decidable equality, a multi-stack Turing machine program assigning to each label in $L$ a
statement over the alphabets $\Gamma$ and the labels $L$ with Boolean internal state, and a list
of the stacks in which every stack occurs exactly once, so that a host can empty all of them. -/
structure Comp where
  /-- Stack indices. -/
  K : Type
  /-- Decidable equality of stack indices. -/
  [decK : DecidableEq K]
  /-- Finitely many stacks. -/
  [finK : Fintype K]
  /-- Stack alphabets. -/
  Γ : K → Type
  /-- Finite alphabets. -/
  [finΓ : ∀ k, Fintype (Γ k)]
  /-- Labels. -/
  L : Type
  /-- Decidable equality of labels. -/
  [decL : DecidableEq L]
  /-- Finitely many labels. -/
  [finL : Fintype L]
  /-- The program. -/
  prog : L → TM2.Stmt Γ L Bool
  /-- The stacks, listed. -/
  ks : List K
  /-- No stack is listed twice. -/
  ks_nodup : ks.Nodup
  /-- Every stack is listed. -/
  mem_ks : ∀ k, k ∈ ks

attribute [instance] Comp.decK Comp.finK Comp.finΓ Comp.decL Comp.finL

/-! ### Host stacks, alphabets and labels -/

/-- **Stacks of the generic host.** For a component machine $c$ with stack indices $K$, the host
stacks are an input stack, an output stack, two buffers $X_1$ and $W_1$ used in phase 0 (which
moves the input onto the component's stacks), and one copy of each component stack $k \in K$. -/
inductive HK (c : Comp)
  | inp | out | X1 | W1
  | comp (k : c.K)
  deriving DecidableEq

/-- **The list of host stacks.** For a component machine $c$, the host stacks are listed as the
input stack, the output stack, the two buffer stacks $X_1$ and $W_1$, and then the host's copies
of the stacks of $c$, in the order of the list of stacks that $c$ carries. -/
def allKs (c : Comp) : List (HK c) := .inp :: .out :: .X1 :: .W1 :: c.ks.map .comp

theorem allKs_nodup (c : Comp) : (allKs c).Nodup := by
  have h : (c.ks.map HK.comp).Nodup := c.ks_nodup.map fun _ _ h => HK.comp.inj h
  simp [allKs, h]

theorem mem_allKs {c : Comp} (k : HK c) : k ∈ allKs c := by
  cases k <;> simp [allKs, c.mem_ks]

/-- Finitely many host stacks. -/
instance (c : Comp) : Fintype (HK c) := Fintype.ofList (allKs c) mem_allKs

/-- **Alphabets of the generic host.** For a component machine $c$ with stack alphabets
$(\Gamma_k)_k$ and a type $\alpha$, the alphabet of a host stack is $\alpha$ on the input stack,
$\Gamma_k$ on the host copy of the component's stack $k$, and the booleans on the output stack and
on the two phase-0 buffers. -/
@[reducible] def HΓ (c : Comp) (α : Type) : HK c → Type
  | .inp => α
  | .comp k => c.Γ k
  | _ => Bool

/-- **Phase-0 labels of the generic host.** The six labels of a host's phase 0, which moves the
input onto the component's stacks: two for the two passes that move the first block $x$, one that
drops the separator, two for the two passes that move the second block $w$, and one that resets
the state and starts the component. -/
inductive P0 | m1 | m2 | sep | m3 | m4 | go
  deriving DecidableEq

/-- Finitely many phase-0 labels. -/
instance P0.instFintypeEnumFix : Fintype P0 where
  elems := ⟨↑[P0.m1, .m2, .sep, .m3, .m4, .go], by decide⟩
  complete := fun x => by cases x <;> decide

/-- **Labels of the generic host.** For a component machine $c$ with labels $L$, and with $P_0$ the
set of phase-0 labels, the host labels are one label for each $p \in P_0$, one copy of each
component label $l \in L$, and, for each boolean answer $a$, a cleanup label and an output label
carrying $a$. -/
inductive HLab (c : Comp)
  | ph (p : P0)
  | comp (l : c.L)
  | clean (ans : Bool)
  | fin (ans : Bool)
  deriving DecidableEq

/-- **Labels of the generic host as a sum type.** For a component machine $c$ with labels $L$, let
$P_0$ be the set of phase-0 labels and $B = \{\mathrm{false}, \mathrm{true}\}$. The host labels of
$c$ are in bijection with the disjoint union $P_0 \sqcup L \sqcup B \sqcup B$: the phase-0 label
$p$ corresponds to $p$, the host copy of the component label $l$ to $l$, the cleanup label with
answer $a$ to $a$ in the first copy of $B$, and the output label with answer $a$ to $a$ in the
second copy of $B$.

The bijection shows that there are finitely many host labels. -/
def HLab.equiv (c : Comp) : HLab c ≃ P0 ⊕ c.L ⊕ Bool ⊕ Bool where
  toFun
    | .ph p => .inl p | .comp l => .inr (.inl l) | .clean a => .inr (.inr (.inl a))
    | .fin a => .inr (.inr (.inr a))
  invFun
    | .inl p => .ph p | .inr (.inl l) => .comp l | .inr (.inr (.inl a)) => .clean a
    | .inr (.inr (.inr a)) => .fin a
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with p | l | a | a <;> rfl

/-- Finitely many host labels. -/
instance (c : Comp) : Fintype (HLab c) := Fintype.ofEquiv _ (HLab.equiv c).symm

/-- **The component's stacks inside a host.** For a component machine $c$ and an input alphabet
$\alpha$, the stack embedding of $c$ into the host over $\alpha$ sends each stack $k$ of $c$ to
the host's copy of $k$, whose alphabet is the alphabet $\Gamma_k$ of $k$, and identifies the two
alphabets by the identity. Distinct stacks have distinct copies, so the embedding is injective. -/
def emb (c : Comp) (α : Type) : SEmb c.Γ (HΓ c α) where
  e := .comp
  inj _ _ h := HK.comp.inj h
  ι _ := Equiv.refl _

/-- **Agreement with the embedded component.** Let $c$ be a component machine and $\alpha$ an
input alphabet. For stack contents $S$ of $c$ and stack contents $T$ of the host over $\alpha$,
$T$ agrees with $S$ under the embedding of the component's stacks into the host if and only if,
for every stack $k$ of $c$, the host's copy of $k$ holds exactly $S(k)$. -/
theorem agree_emb {c : Comp} {α : Type} {S : ∀ k, List (c.Γ k)} {T : ∀ k, List (HΓ c α k)} :
    Agree (emb c α) S T ↔ ∀ k, T (.comp k) = S k := by
  refine forall_congr' fun k => ?_
  change T (.comp k) = (S k).map id ↔ _
  rw [List.map_id]

/-! ### Generic pieces of a host run -/

/-- **Moving a bit block through a buffer.** Let $a$, $t$, $b$ be pairwise distinct stacks of a
program $M$ with Boolean state, and let $l_1$, $l_2$, $l_3$ be labels such that $M$ runs at $l_1$
the bit-moving loop from $a$ to $t$ with decoder $d$ and encoder $g_t$, looping at $l_1$ and
exiting to $l_2$, and at $l_2$ the bit-moving loop from $t$ to $b$ with decoder $d_t$ and encoder
$g$, looping at $l_2$ and exiting to $l_3$, where $d_t$ decodes $g_t(y)$ to $y$ for every bit $y$.
Let $x = x_1 \cdots x_n$ be a bit list and $S$ stack contents in which $a$ holds a bit block for
$x$ under $d$ followed by a rest $A$ that ends a bit block under $d$, and $t$ is empty. Then for
every state $v$ there are a state $v'$ and stack contents $S'$ such that $M$ runs in exactly
$2n + 2$ steps from label $l_1$, state $v$ and stacks $S$ to label $l_3$, state $v'$ and stacks
$S'$, where $S'(a) = A$, $S'(t)$ is empty, $S'(b)$ is $g(x_1), \dots, g(x_n)$ (top first)
followed by $S(b)$, and $S'(k) = S(k)$ for every other stack $k$. -/
theorem move2_run {K Λ : Type} [DecidableEq K] {Γ : K → Type} {M : Λ → TM2.Stmt Γ Λ Bool}
    {a t b : K} {d : Γ a → Option Bool} {gt : Bool → Γ t} {dt : Γ t → Option Bool}
    {g : Bool → Γ b} {l₁ l₂ l₃ : Λ} (h₁ : M l₁ = moveB a t d gt l₁ l₂)
    (h₂ : M l₂ = moveB t b dt g l₂ l₃) (hat : a ≠ t) (htb : t ≠ b) (hab : a ≠ b)
    (hdt : ∀ y, dt (gt y) = some y) (x : List Bool) (xs A : List (Γ a)) (v : Bool)
    (S : ∀ k, List (Γ k)) (hS : S a = xs ++ A) (hxs : IsBitBlock d xs x)
    (hA : EndsBitBlock d A) (ht : S t = []) :
    ∃ v' S', Run M (2 * x.length + 2) ⟨some l₁, v, S⟩ ⟨some l₃, v', S'⟩ ∧ S' a = A ∧
      S' t = [] ∧ S' b = x.map g ++ S b ∧ ∀ k, k ≠ a → k ≠ t → k ≠ b → S' k = S k := by
  obtain ⟨v₁, S₁, r₁, h1a, h1t, h1k⟩ := moveB_run h₁ hat x xs A v S hS hxs hA
  obtain ⟨v₂, S₂, r₂, h2t, h2b, h2k⟩ := moveB_run h₂ htb x.reverse (x.map gt).reverse [] v₁ S₁
    (by rw [h1t, ht]) (by simp [IsBitBlock, List.map_reverse, hdt])
    (by simp [EndsBitBlock])
  refine ⟨v₂, S₂, (r₁.trans r₂).of_eq (by simp; omega), ?_, h2t, ?_, ?_⟩
  · rw [h2k a hat hab, h1a]
  · rw [h2b, h1k b hab.symm htb.symm]; simp [List.map_reverse]
  · intro k hka hkt hkb; rw [h2k k hkt hkb, h1k k hka hkt]

/-- **Cleanup stacks of the generic host.** For a component machine $c$ and a host stack $o$, the
cleanup stacks are the list of all host stacks with $o$ removed, in the order of the list of
host stacks. The cleanup empties these stacks and leaves the output stack $o$. -/
def cleanKs (c : Comp) (o : HK c) : List (HK c) := (allKs c).filter (· ≠ o)

theorem cleanKs_nodup (c : Comp) (o : HK c) : (cleanKs c o).Nodup := (allKs_nodup c).filter _

/-- **Membership in the cleanup stacks of the generic host.** For a component machine $c$ and host
stacks $o$ and $k$, the stack $k$ belongs to the list of stacks that the cleanup for the output
stack $o$ empties if and only if $k \ne o$. -/
theorem mem_cleanKs {c : Comp} {o k : HK c} : k ∈ cleanKs c o ↔ k ≠ o := by
  simp [cleanKs, mem_allKs]

/-- **Cleanup in a host.** Let $c$ be a component machine, $\alpha$ an input alphabet, $o$ a host
stack, $a$ a bit, and $M$ a host program with Boolean state whose statement at the cleanup label
for $a$ is the cleanup round on the list of all host stacks with $o$ removed, kept in the order
of the list of host stacks, repeating at the cleanup label for $a$ and exiting to the output
label for $a$. If $S$ assigns to every host stack at most $m$ symbols, then for every state $v$,
$M$ runs from the cleanup label for $a$ with state $v$ and stacks $S$ to the output label for $a$
in at most $m + 1$ steps, ending with state false, stack $o$ holding $S(o)$ and every other stack
empty. -/
theorem cleanup_run {c : Comp} {α : Type} {M : HLab c → TM2.Stmt (HΓ c α) (HLab c) Bool}
    {o : HK c} {ans : Bool} (hM : M (.clean ans) = cleanS (cleanKs c o) (.clean ans) (.fin ans))
    (m : ℕ) (v : Bool) (S : ∀ k, List (HΓ c α k)) (hl : ∀ k, (S k).length ≤ m) :
    RunLe M (m + 1) ⟨some (.clean ans), v, S⟩
      ⟨some (.fin ans), false, update (fun _ => []) o (S o)⟩ := by
  have h := clean_run hM (cleanKs_nodup c o) m v S (fun k _ => hl k)
  have e : (fun k => if k ∈ cleanKs c o then [] else S k) = update (fun _ => []) o (S o) := by
    funext k
    by_cases hk : k = o
    · subst hk; simp [mem_cleanKs]
    · simp [mem_cleanKs, hk]
  rwa [e] at h

/-- **Stack lengths grow by at most the push bound per step.** Let $M$ be a finite multi-stack
Turing machine with push bound $B$. If every stack of $S$ has length at most $N$ and $M$ runs in
$n$ steps from a configuration with some label, state $v$ and stacks $S$ to a configuration with
some label, state $v'$ and stacks $S'$, then every stack of $S'$ has length at most $N + Bn$. -/
theorem stk_length_le (M : FinTM2) {n N : ℕ} {S S' : ∀ k, List (M.Γ k)} {v v' : M.σ}
    {l l' : M.Λ} (hS : ∀ k, (S k).length ≤ N) (h : Run M.m n ⟨some l, v, S⟩ ⟨some l', v', S'⟩) :
    ∀ k, (S' k).length ≤ N + TM2Composition.pushBound M * n := fun k =>
  (TM2Composition.length_iter M k n _ _ h).trans (Nat.add_le_add_right (hS k) _)

/-- **Initial configuration of a finite multi-stack machine.** For a finite multi-stack Turing
machine $M$ with input stack $k_0$, main label $\lambda_0$ and initial internal state $\sigma_0$,
and a list $l$ over the alphabet of $k_0$, the initial configuration of $M$ on $l$ has current
label $\lambda_0$, internal state $\sigma_0$, the list $l$ on $k_0$ and every other stack empty. -/
theorem initList_eq (M : FinTM2) (l : List (M.Γ M.k₀)) :
    initList M l = ⟨some M.main, M.initialState, update (fun _ => []) M.k₀ l⟩ := by
  rw [TM2Composition.update_nil_eq_initList]
  rfl

/-- **Halting configuration of a finite multi-stack machine.** For a finite multi-stack Turing
machine $M$ with output stack $k_1$ and initial internal state $\sigma_0$, and a list $l$ over the
alphabet of $k_1$, the halting configuration of $M$ with output $l$ has no current label, internal
state $\sigma_0$, the list $l$ on $k_1$ and every other stack empty. -/
theorem haltList_eq (M : FinTM2) (l : List (M.Γ M.k₁)) :
    haltList M l = ⟨none, M.initialState, update (fun _ => []) M.k₁ l⟩ := by
  simp only [haltList]
  congr 1
  funext k
  by_cases h : k = M.k₁
  · subst h; simp
  · simp [h]

/-- **Stack lengths when only one stack is filled.** Let $c$ be a component machine and consider
its host with input alphabet $\alpha$. If a host stack $o$ holds a list $l$ and every other host
stack is empty, then every host stack has length at most the length of $l$. -/
theorem update_length_le {c : Comp} {α : Type} (o : HK c) (l : List (HΓ c α o)) :
    ∀ k, (update (fun _ => []) o l k).length ≤ l.length := by
  intro k
  by_cases h : k = o
  · subst h; simp
  · simp [h]

/-! ### The reduction host -/

section Reduction

variable (c : Comp) (cX cO : c.K) (gX : Bool → c.Γ cX) (start done : c.L)

/-- **Component labels in the reduction host.** For a component with exit label $\mathit{done}$,
the label $\mathit{done}$ is sent to the host's cleanup label with answer false, and every other
component label $l$ to the host label that runs the component at $l$. -/
def φR (l : c.L) : HLab c := if l = done then .clean false else .comp l

/-- **Reduction host program.** The program of the reduction host for a component with stacks
$c_X$ and $c_O$, an encoding $g_X$ of bits as symbols of $c_X$ and labels $\mathit{start}$ and
$\mathit{done}$. Phase 0 moves the whole input stack onto the buffer $X_1$ with the bit-moving
loop, then moves $X_1$ onto the host's copy of $c_X$ re-encoded by $g_X$ (so in the original
order), then sets the state to false and goes to $\mathit{start}$, or to the cleanup if
$\mathit{start} = \mathit{done}$. At the host label of a component label $l$ it runs the
component's statement at $l$ on the host's copies of the component stacks, with every jump to
$\mathit{done}$ sent to the cleanup. The cleanup pops every stack other than the copy of $c_O$
once per round, repeating while something was popped, and then goes to the final label, which
halts. The phase-0 labels for a separator and a second block halt. -/
def rprog : HLab c → TM2.Stmt (HΓ c Bool) (HLab c) Bool
  | .ph .m1 => moveB (Γ := HΓ c Bool) .inp .X1 some id (.ph .m1) (.ph .m2)
  | .ph .m2 => moveB (Γ := HΓ c Bool) .X1 (.comp cX) some gX (.ph .m2) (.ph .go)
  | .ph .go => .load (fun _ => false) (.goto fun _ => φR c done start)
  | .ph .sep | .ph .m3 | .ph .m4 => .halt
  | .comp l => mapS (emb c Bool) (φR c done) (c.prog l)
  | .clean _ => cleanS (cleanKs c (.comp cO)) (.clean false) (.fin false)
  | .fin _ => .halt

/-- **Reduction host machine.** The reduction host as a finite multi-stack Turing machine: its
stacks are the host stacks with the host alphabets for bit input, its labels are the host labels,
its state is a bit starting at false, its program is the reduction host program started at the
first phase-0 label, its input stack is the input stack (raw bits) and its output stack is the
host's copy of the component's stack $c_O$. -/
def rtm : FinTM2 where
  K := HK c
  k₀ := .inp
  k₁ := .comp cO
  Γ := HΓ c Bool
  Λ := HLab c
  main := .ph .m1
  σ := Bool
  initialState := false
  Γk₀Fin := (inferInstance : Fintype Bool)
  m := rprog c cX cO gX start done

/-- **Step bound of the reduction host.** Let $c$ be a component machine with stacks $c_X$ and
$c_O$, an encoding $g_X$ of bits as symbols of $c_X$ and labels $\mathit{start}$ and
$\mathit{done}$, and let $B$ be the push bound of the reduction host machine built from these
data. For a polynomial $p$ with natural-number coefficients, the step bound of the reduction host
is the polynomial in the variable $X$
$$(B + 1)(2X + 3 + p) + X + 2.$$

At an input length $n$ it counts phase 0 and the component, at most $2n + 3 + p(n)$ steps, then
the cleanup, which takes at most one step more than the longest stack, of length at most $n$
plus $B$ times the steps so far, and the halt. -/
noncomputable def rtime (p : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (TM2Composition.pushBound (rtm c cX cO gX start done) + 1) *
      (Polynomial.C 2 * Polynomial.X + Polynomial.C 3 + p) + Polynomial.X + Polynomial.C 2

theorem rtime_eval (p : Polynomial ℕ) (n : ℕ) :
    (rtime c cX cO gX start done p).eval n =
      (2 * n + 3 + p.eval n) +
        (n + TM2Composition.pushBound (rtm c cX cO gX start done) * (2 * n + 3 + p.eval n)) +
          2 := by
  simp only [rtime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  ring

variable {c cX cO gX start done}

/-- **The reduction host embeds the component.** Let $c$ be a component machine with stacks
$c_X$ and $c_O$, a map $g_X$ from bits to the alphabet of $c_X$, and labels $s$ and $d$,
and suppose that $c$ halts at $d$. Rename the labels of $c$ by sending $d$ to the cleanup label
with answer false and every other label $l$ to the host's copy of $l$, and embed the stacks of
$c$ as the host's copies over the bit input alphabet. Then the reduction host built from
$c_X$, $c_O$, $g_X$, $s$ and $d$ embeds $c$: for every label $l$ of $c$, either $c$ halts at
$l$, or the host's statement at the renamed label of $l$ is the statement of $c$ at $l$ with
stacks and labels translated. -/
theorem embeds_rprog (hdone : c.prog done = .halt) :
    Embeds (emb c Bool) (φR c done) c.prog (rprog c cX cO gX start done) := by
  intro l
  by_cases h : l = done
  · subst h; exact .inr hdone
  · left
    rw [show φR c done l = .comp l by simp [φR, h]]
    rfl

/-- **The reduction host's run on one input.** Let $c$ be a component with stacks $c_X$ and $c_O$,
an encoding $g_X$ of bits as symbols of $c_X$, an identification $e_O$ of the alphabet of $c_O$
with the bits, and labels $\mathit{start}$ and $\mathit{done}$, where the component halts at
$\mathit{done}$. Let $p$ be a polynomial with natural-number coefficients and $x$, $o$ bit lists,
and suppose that the component, started at $\mathit{start}$ with state false, with $x$ encoded by
$g_X$ on $c_X$ and every other stack empty, reaches $\mathit{done}$ within $p(|x|)$ steps with
some state and stacks in which $c_O$ holds $o$ translated symbol by symbol by $e_O^{-1}$. Then the
reduction host program, started at its first phase-0 label with state false, $x$ on the input
stack and every other stack empty, halts within $T(|x|)$ steps, where $T$ is the reduction host's
step bound for $p$, with state false, $o$ translated by $e_O^{-1}$ on the host's copy of $c_O$ and
every other stack empty. -/
theorem rprog_run_at (eO : c.Γ cO ≃ Bool) (out : List Bool) (p : Polynomial ℕ)
    (hdone : c.prog done = .halt) (x : List Bool)
    (hrun : ∃ v S', RunLe c.prog (p.eval x.length)
      ⟨some start, false, update (fun _ => []) cX (x.map gX)⟩ ⟨some done, v, S'⟩ ∧
        S' cO = out.map eO.symm) :
    RunLe (rprog c cX cO gX start done) ((rtime c cX cO gX start done p).eval x.length)
      ⟨some (.ph .m1), false, update (fun _ => []) .inp x⟩
      ⟨none, false, update (fun _ => []) (.comp cO) (out.map eO.symm)⟩ := by
  set S₀ : ∀ k, List (HΓ c Bool k) := update (fun _ => []) .inp x with hS₀
  obtain ⟨v₁, S₁, r₁, -, -, h1b, h1k⟩ := move2_run (M := rprog c cX cO gX start done)
    (a := .inp) (t := .X1) (b := .comp cX) (d := some) (gt := id) (dt := some) (g := gX)
    (l₁ := .ph .m1) (l₂ := .ph .m2) (l₃ := .ph .go) rfl rfl (by simp) (by simp) (by simp)
    (fun _ => rfl) x x [] false S₀ (by simp [hS₀]) rfl rfl (by simp [hS₀])
  have r₂ : Run (rprog c cX cO gX start done) 1 ⟨some (.ph .go), v₁, S₁⟩
      ⟨some (φR c done start), false, S₁⟩ := Run.single rfl
  have hag : Agree (emb c Bool) (update (fun _ => []) cX (x.map gX)) S₁ := by
    rw [agree_emb]
    intro k
    by_cases hk : k = cX
    · subst hk; rw [update_self, h1b]; simp [hS₀]
    · rw [update_of_ne hk, h1k _ (by simp) (by simp) (by simpa using hk)]; simp [hS₀]
  obtain ⟨v, S', hr, hO⟩ := hrun
  obtain ⟨T₁, ⟨n₁, hn₁, r₃⟩, hag₁, -⟩ := runLe_embed (φR c done) (embeds_rprog hdone) hr hag
  rw [show φR c done done = .clean false by simp [φR]] at r₃
  have r := (r₁.trans r₂).trans r₃
  have hl := stk_length_le (rtm c cX cO gX start done) (N := x.length)
    (update_length_le (c := c) (α := Bool) .inp x) r
  obtain ⟨n₄, hn₄, r₄⟩ := cleanup_run (M := rprog c cX cO gX start done) (o := .comp cO)
    (ans := false) rfl _ v T₁ hl
  have hT : T₁ (.comp cO) = out.map eO.symm := by rw [agree_emb.1 hag₁ cO, hO]
  rw [hT] at r₄
  have r₅ : Run (rprog c cX cO gX start done) 1
      ⟨some (.fin false), false, update (fun _ => []) (.comp cO) (out.map eO.symm)⟩
      ⟨none, false, update (fun _ => []) (.comp cO) (out.map eO.symm)⟩ := Run.single rfl
  refine ⟨_, ?_, (r.trans r₄).trans r₅⟩
  rw [rtime_eval]
  have h2 := Nat.mul_le_mul_left (TM2Composition.pushBound (rtm c cX cO gX start done))
    (show 2 * x.length + 2 + 1 + n₁ ≤ 2 * x.length + 3 + p.eval x.length by omega)
  omega

/-- **The reduction host's run.** Let $c$ be a component with stacks $c_X$ and $c_O$, an encoding
$g_X$ of bits as symbols of $c_X$, an identification $e_O$ of the alphabet of $c_O$ with the bits,
and labels $\mathit{start}$ and $\mathit{done}$, where the component halts at $\mathit{done}$. Let
$f$ be a function from bit lists to bit lists and $p$ a polynomial with natural-number
coefficients, and suppose that for every bit list $y$ the component, started at $\mathit{start}$
with state false, with $y$ encoded by $g_X$ on $c_X$ and every other stack empty, reaches
$\mathit{done}$ within $p(|y|)$ steps with some state and stacks in which $c_O$ holds $f(y)$
translated symbol by symbol by $e_O^{-1}$. Then for every bit list $x$ the reduction host program,
started at its first phase-0 label with state false, $x$ on the input stack and every other stack
empty, halts within $T(|x|)$ steps, where $T$ is the reduction host's step bound for $p$, with
state false, $f(x)$ translated by $e_O^{-1}$ on the host's copy of $c_O$ and every other stack
empty. -/
theorem rprog_run (eO : c.Γ cO ≃ Bool) (f : List Bool → List Bool) (p : Polynomial ℕ)
    (hdone : c.prog done = .halt)
    (hrun : ∀ x, ∃ v S', RunLe c.prog (p.eval x.length)
      ⟨some start, false, update (fun _ => []) cX (x.map gX)⟩ ⟨some done, v, S'⟩ ∧
        S' cO = (f x).map eO.symm)
    (x : List Bool) :
    RunLe (rprog c cX cO gX start done) ((rtime c cX cO gX start done p).eval x.length)
      ⟨some (.ph .m1), false, update (fun _ => []) .inp x⟩
      ⟨none, false, update (fun _ => []) (.comp cO) ((f x).map eO.symm)⟩ :=
  rprog_run_at eO (f x) p hdone x (hrun x)

/-- **Reduction host.** Let $c$ be a component with stacks $c_X$ and $c_O$, an encoding $g_X$ of
bits as symbols of $c_X$, an identification $e_O$ of the alphabet of $c_O$ with the bits, and
labels $\mathit{start}$ and $\mathit{done}$, where the component halts at $\mathit{done}$. Let $f$
be a function from bit lists to bit lists and $p$ a polynomial with natural-number coefficients.
Suppose that for every bit list $x$ the component, started at $\mathit{start}$ with state false,
with $x$ encoded by $g_X$ on $c_X$ and every other stack empty, reaches $\mathit{done}$ within
$p(|x|)$ steps with some state and stacks in which $c_O$ holds $f(x)$ translated symbol by symbol
by $e_O^{-1}$. Then $f$ is computable in polynomial time on raw bit lists (the identity as input
and output encoding): by the reduction host machine, with the bits as input alphabet, $e_O$ as
output alphabet and the reduction host's step bound for $p$ as time bound. -/
noncomputable def reduction (eO : c.Γ cO ≃ Bool) (f : List Bool → List Bool) (p : Polynomial ℕ)
    (hdone : c.prog done = .halt)
    (hrun : ∀ x, ∃ v S', RunLe c.prog (p.eval x.length)
      ⟨some start, false, update (fun _ => []) cX (x.map gX)⟩ ⟨some done, v, S'⟩ ∧
        S' cO = (f x).map eO.symm) :
    TM2ComputableInPolyTime (fun l : List Bool => l) (fun l : List Bool => l) f where
  tm := rtm c cX cO gX start done
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := eO
  time := rtime c cX cO gX start done p
  outputsFun := fun x => by
    have h := rprog_run eO f p hdone hrun x
    unfold RunLe at h
    refine ⟨⟨Classical.choose h, ?_⟩, (Classical.choose_spec h).1⟩
    erw [List.map_id, initList_eq, Option.map_some, haltList_eq]
    exact (Classical.choose_spec h).2

/-- **Reduction host, canonical form.** Let $c$ be a component machine with stacks $c_X$ and
$c_O$ and labels $\mathit{start}$ and $\mathit{done}$, where the statement at $\mathit{done}$ is
the halting statement. Let $g_X$ map bits to symbols of $c_X$, let $e_O$ be a bijection from the
alphabet of $c_O$ to the booleans, let $f$ map bit lists to bit lists, and let $p$ be a polynomial
with coefficients in $\mathbb{N}$. Suppose that for every bit list $x$, the component started at
$\mathit{start}$ with internal state false, with $g_X$ applied to each bit of $x$ on $c_X$ and
every other stack empty, reaches the label $\mathit{done}$ in at most $p(|x|)$ steps with stack
$c_O$ holding exactly $e_O^{-1}$ applied to each bit of $f(x)$. Then $f$ is polynomial-time
computable for the canonical bitstring encodings. -/
theorem isPolyTime_reduction (eO : c.Γ cO ≃ Bool) (f : List Bool → List Bool)
    (p : Polynomial ℕ) (hdone : c.prog done = .halt)
    (hrun : ∀ x, ∃ v S', RunLe c.prog (p.eval x.length)
      ⟨some start, false, update (fun _ => []) cX (x.map gX)⟩ ⟨some done, v, S'⟩ ∧
        S' cO = (f x).map eO.symm) :
    ComplexityTheory.IsPolyTime f := by
  obtain ⟨h⟩ := tm2ComputableInPolyTime_comp DecodeBits.computable
    (reduction eO f p hdone hrun)
  exact tm2ComputableInPolyTime_comp (f := f) (g := id) h EncodeBits.computable

/-- **Decider host.** Let $c$ be a component machine with stacks $c_X$ and $c_O$ and labels
$\mathit{start}$ and $\mathit{done}$, where the statement at $\mathit{done}$ is the halting
statement. Let $g_X$ map bits to symbols of $c_X$, let $e_O$ be a bijection from the alphabet of
$c_O$ to the booleans, let $L$ map bit lists to booleans, and let $p$ be a polynomial with
coefficients in $\mathbb{N}$. Suppose that for every bit list $x$, the component started at
$\mathit{start}$ with internal state false, with $g_X$ applied to each bit of $x$ on $c_X$ and
every other stack empty, reaches the label $\mathit{done}$ in at most $p(|x|)$ steps with exactly
the one symbol $e_O^{-1}(L(x))$ on $c_O$. Then $L$ is polynomial-time computable for the
canonical bitstring encodings, that is, $L$ belongs to the class $\mathrm{P}$ of decision
problems decidable in polynomial time.

The proof applies the reduction host to $x \mapsto [L(x)]$, read with the one-bit encoding of the
booleans. -/
theorem isPolyTime_decider (eO : c.Γ cO ≃ Bool) (L : List Bool → Bool) (p : Polynomial ℕ)
    (hdone : c.prog done = .halt)
    (hrun : ∀ x, ∃ v S', RunLe c.prog (p.eval x.length)
      ⟨some start, false, update (fun _ => []) cX (x.map gX)⟩ ⟨some done, v, S'⟩ ∧
        S' cO = [eO.symm (L x)]) :
    ComplexityTheory.IsPolyTime L := by
  obtain ⟨h⟩ := tm2ComputableInPolyTime_comp DecodeBits.computable
    (reduction eO (fun x => [L x]) p hdone hrun)
  exact ⟨⟨h.toTM2ComputableAux, h.time, h.outputsFun⟩⟩

end Reduction

/-! ### The verifier host -/

section Verifier

variable (c : Comp) (cX cW : c.K) (gX : Bool → c.Γ cX) (gW : Bool → c.Γ cW) (start yes no : c.L)

/-- **Relabelling in the verifier host.** Given labels $\mathit{yes}$ and $\mathit{no}$ of a
component machine $c$, a label $l$ of $c$ is sent to the host label that starts the cleanup with
answer true if $l = \mathit{yes}$, to the host label that starts the cleanup with answer false if
$l \ne \mathit{yes}$ and $l = \mathit{no}$, and to the host label that runs the component at $l$
otherwise. -/
def φV (l : c.L) : HLab c :=
  if l = yes then .clean true else if l = no then .clean false else .comp l

/-- **Reading a bit of $x$.** On the pair alphabet of the $x \# w$ input, the symbol that
encodes a bit $b$ of $x$ (the left injection of $b$) is read as the bit $b$; every other symbol,
the separator $\#$ or a bit of $w$ (both right injections), is read as no bit. -/
def dX : Verifier.G → Option Bool
  | .inl b => some b
  | _ => none

/-- **Reading a bit of $w$.** On the pair alphabet of the $x \# w$ input, the symbol that
encodes a bit $b$ of $w$ (the right injection of $\mathrm{some}\,b$) is read as the bit $b$;
every other symbol, a bit of $x$ (a left injection) or the separator $\#$ (the right injection
of $\mathrm{none}$), is read as no bit. -/
def dW : Verifier.G → Option Bool
  | .inr (some b) => some b
  | _ => none

/-- **Verifier host program.** The program of the verifier host for a component machine $c$ with
stacks $c_X$ and $c_W$, encodings $g_X$ and $g_W$ of bits as symbols of $c_X$ and $c_W$, and
labels $\mathit{start}$, $\mathit{yes}$ and $\mathit{no}$, on the host stacks with the work
alphabet of the dense-SAT verifier on the input stack. On an input $x \# w$ in the pair encoding,
phase 0 moves the symbols on top of the input stack that encode bits of $x$ onto the buffer $X_1$
with the bit-moving loop, then moves $X_1$ onto the host's copy of $c_X$ re-encoded by $g_X$ (so
in the original order); it pops one symbol off the input stack (the separator $\#$); it moves
the symbols that encode bits of $w$ onto the buffer $W_1$ and then $W_1$ onto the host's copy of
$c_W$ re-encoded by $g_W$; then it sets the state to false and goes to the renamed label of
$\mathit{start}$. Here a label of $c$ is renamed to the cleanup label with answer true if it is
$\mathit{yes}$, to the cleanup label with answer false if it is $\mathit{no}$ but not
$\mathit{yes}$, and to the host's copy of itself otherwise. At the host's copy of a component
label $l$ it runs the component's statement at $l$ on the host's copies of the component stacks,
with every jump target renamed. The cleanup label with answer $a$ pops every stack other than the
output stack once per round, repeating while something was popped, and then goes to the output
label with answer $a$, which pushes $a$ on the output stack and halts. -/
def vprog : HLab c → TM2.Stmt (HΓ c Verifier.G) (HLab c) Bool
  | .ph .m1 => moveB (Γ := HΓ c Verifier.G) .inp .X1 dX id (.ph .m1) (.ph .m2)
  | .ph .m2 => moveB (Γ := HΓ c Verifier.G) .X1 (.comp cX) some gX (.ph .m2) (.ph .sep)
  | .ph .sep => .pop .inp (fun s _ => s) (.goto fun _ => .ph .m3)
  | .ph .m3 => moveB (Γ := HΓ c Verifier.G) .inp .W1 dW id (.ph .m3) (.ph .m4)
  | .ph .m4 => moveB (Γ := HΓ c Verifier.G) .W1 (.comp cW) some gW (.ph .m4) (.ph .go)
  | .ph .go => .load (fun _ => false) (.goto fun _ => φV c yes no start)
  | .comp l => mapS (emb c Verifier.G) (φV c yes no) (c.prog l)
  | .clean ans => cleanS (cleanKs c .out) (.clean ans) (.fin ans)
  | .fin ans => .push .out (fun _ => ans) .halt

/-- **The verifier host machine.** The verifier host as a finite multi-stack Turing machine for a
component machine $c$: its stacks are the host stacks, with the pair alphabet on the input stack,
the alphabets of $c$ on the component's stacks and bits on the other stacks; its labels are the
host labels and its program is the verifier host program; it starts at the first phase-0 label
with a boolean internal state, initially false; it reads its input from the input stack and leaves
its output on the output stack. -/
def vtm : FinTM2 where
  K := HK c
  k₀ := .inp
  k₁ := .out
  Γ := HΓ c Verifier.G
  Λ := HLab c
  main := .ph .m1
  σ := Bool
  initialState := false
  Γk₀Fin := (inferInstance : Fintype Verifier.G)
  m := vprog c cX cW gX gW start yes no

/-- **Step bound of the verifier host.** Let $c$ be a component machine with stacks $c_X$ and
$c_W$, encodings $g_X$ and $g_W$ of bits as symbols of $c_X$ and $c_W$, and labels
$\mathit{start}$, $\mathit{yes}$ and $\mathit{no}$, and let $B$ be the push bound of the verifier
host machine built from these data. For a polynomial $p$ with natural-number coefficients, the
step bound of the verifier host is the polynomial in the variable $X$
$$(B + 1)(2X + 4 + p) + X + 2.$$

At an input length $n$ it counts phase 0 and the component, at most $2n + 4 + p(n)$ steps, then
the cleanup, which takes at most one step more than the longest stack, of length at most $n$
plus $B$ times the steps so far, and the output step. -/
noncomputable def vtime (p : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (TM2Composition.pushBound (vtm c cX cW gX gW start yes no) + 1) *
      (Polynomial.C 2 * Polynomial.X + Polynomial.C 4 + p) + Polynomial.X + Polynomial.C 2

theorem vtime_eval (p : Polynomial ℕ) (n : ℕ) :
    (vtime c cX cW gX gW start yes no p).eval n =
      (2 * n + 4 + p.eval n) +
        (n + TM2Composition.pushBound (vtm c cX cW gX gW start yes no) *
          (2 * n + 4 + p.eval n)) + 2 := by
  simp only [vtime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  ring

variable {c cX cW gX gW start yes no}

/-- **The verifier host embeds the component.** Let $c$ be a component machine with stacks $c_X$
and $c_W$, maps $g_X$ and $g_W$ from bits to the alphabets of $c_X$ and $c_W$, and labels
$\mathit{start}$, $\mathit{yes}$ and $\mathit{no}$, and suppose that the statement of $c$ at
$\mathit{yes}$ and the statement of $c$ at $\mathit{no}$ are the halt statement. Rename the labels
of $c$ by sending $\mathit{yes}$ to the cleanup label with answer true, $\mathit{no}$ (when it
differs from $\mathit{yes}$) to the cleanup label with answer false, and every other label $l$ to
the host's copy of $l$, and embed the stacks of $c$ as the host's copies over the work alphabet
of the dense-SAT verifier. Then the verifier host program built from $c_X$, $c_W$, $g_X$, $g_W$,
$\mathit{start}$, $\mathit{yes}$ and $\mathit{no}$ embeds $c$: for every label $l$ of $c$, either
the statement of $c$ at $l$ is the halt statement, or the host's statement at the renamed label
of $l$ is the statement of $c$ at $l$ with stacks and labels translated. -/
theorem embeds_vprog (hyes : c.prog yes = .halt) (hno : c.prog no = .halt) :
    Embeds (emb c Verifier.G) (φV c yes no) c.prog (vprog c cX cW gX gW start yes no) := by
  intro l
  by_cases h1 : l = yes
  · subst h1; exact .inr hyes
  by_cases h2 : l = no
  · subst h2; exact .inr hno
  left
  rw [show φV c yes no l = .comp l by simp [φV, h1, h2]]
  rfl

/-- **The verifier host's run.** Let $c$ be a component machine with stacks $c_X \ne c_W$, maps
$g_X$ and $g_W$ from bits to the alphabets of $c_X$ and $c_W$, and labels $\mathit{start}$,
$\mathit{yes}$ and $\mathit{no}$ with $\mathit{yes} \ne \mathit{no}$, where the program halts at
$\mathit{yes}$ and at $\mathit{no}$. Let $f$ assign a boolean to each pair of bit lists and let
$p$ be a polynomial with natural number coefficients. Suppose that for all bit lists $x$ and $w$,
the component started at $\mathit{start}$ with state false, the bits of $x$ mapped by $g_X$ on
$c_X$, the bits of $w$ mapped by $g_W$ on $c_W$ and every other stack empty reaches the label
$\mathit{yes}$ if $f(x, w)$ is true and $\mathit{no}$ otherwise within $p(|x| + |w|)$ steps. Then
for all bit lists $x$ and $w$, with $n$ the length of the pair encoding of $(x, w)$, the verifier
host program started at its first phase-0 label with state false, the pair encoding of $(x, w)$
on the input stack and every other stack empty halts within $T(n)$ steps, where $T$ is the
verifier host's step bound for $p$, with state false, the one-element list $[f(x, w)]$ on the
output stack and every other stack empty. -/
theorem vprog_run (f : List Bool → List Bool → Bool) (p : Polynomial ℕ) (hXW : cX ≠ cW)
    (hyn : yes ≠ no) (hyes : c.prog yes = .halt) (hno : c.prog no = .halt)
    (hrun : ∀ x w, ∃ v S', RunLe c.prog (p.eval (x.length + w.length))
      ⟨some start, false, update (update (fun _ => []) cX (x.map gX)) cW (w.map gW)⟩
      ⟨some (if f x w then yes else no), v, S'⟩)
    (x w : List Bool) :
    RunLe (vprog c cX cW gX gW start yes no)
      ((vtime c cX cW gX gW start yes no p).eval (Verifier.pairEncode (x, w)).length)
      ⟨some (.ph .m1), false, update (fun _ => []) .inp (Verifier.pairEncode (x, w))⟩
      ⟨none, false, update (fun _ => []) .out [f x w]⟩ := by
  set M := vprog c cX cW gX gW start yes no with hM
  set N := (Verifier.pairEncode (x, w)).length with hN
  have hNe : N = x.length + 1 + w.length := by
    simp [hN, Verifier.pairEncode]; omega
  set S₀ : ∀ k, List (HΓ c Verifier.G k) := update (fun _ => []) .inp (Verifier.pairEncode (x, w))
    with hS₀
  -- `x` onto `cX`
  obtain ⟨v₁, S₁, r₁, h1a, -, h1b, h1k⟩ := move2_run (M := M)
    (a := .inp) (t := .X1) (b := .comp cX) (d := dX) (gt := id) (dt := some) (g := gX)
    (l₁ := .ph .m1) (l₂ := .ph .m2) (l₃ := .ph .sep) rfl rfl (by simp) (by simp) (by simp)
    (fun _ => rfl) x (x.map Sum.inl) (Sum.inr none :: w.map fun b => Sum.inr (some b)) false S₀
    (by simp [hS₀, Verifier.pairEncode]) (by simp [IsBitBlock, dX, Function.comp_def]) rfl
    (by simp [hS₀])
  -- drop the separator
  have r₂ : Run M 1 ⟨some (.ph .sep), v₁, S₁⟩
      ⟨some (.ph .m3), v₁, update S₁ .inp (w.map fun b => Sum.inr (some b))⟩ :=
    Run.single (by simp [hM, vprog, TM2.stepAux, h1a])
  -- `w` onto `cW`
  obtain ⟨v₃, S₃, r₃, -, -, h3b, h3k⟩ := move2_run (M := M)
    (a := .inp) (t := .W1) (b := .comp cW) (d := dW) (gt := id) (dt := some) (g := gW)
    (l₁ := .ph .m3) (l₂ := .ph .m4) (l₃ := .ph .go) rfl rfl (by simp) (by simp) (by simp)
    (fun _ => rfl) w (w.map fun b => Sum.inr (some b)) [] v₁
    (update S₁ .inp (w.map fun b => Sum.inr (some b))) (by simp)
    (by simp [IsBitBlock, dW, Function.comp_def]) rfl
    (by rw [update_of_ne (by simp), h1k _ (by simp) (by simp) (by simp)]; simp [hS₀])
  have r₄ : Run M 1 ⟨some (.ph .go), v₃, S₃⟩ ⟨some (φV c yes no start), false, S₃⟩ :=
    Run.single rfl
  have hag : Agree (emb c Verifier.G)
      (update (update (fun _ => []) cX (x.map gX)) cW (w.map gW)) S₃ := by
    rw [agree_emb]
    intro k
    by_cases hW : k = cW
    · subst hW
      rw [update_self, h3b, update_of_ne (by simp),
        h1k _ (by simp) (by simp) (by simpa using hXW.symm)]
      simp [hS₀]
    rw [update_of_ne hW, h3k _ (by simp) (by simp) (by simpa using hW), update_of_ne (by simp)]
    by_cases hX : k = cX
    · subst hX; rw [update_self, h1b]; simp [hS₀]
    · rw [update_of_ne hX, h1k _ (by simp) (by simp) (by simpa using hX)]; simp [hS₀]
  obtain ⟨v, S', hr⟩ := hrun x w
  obtain ⟨T₁, ⟨n₁, hn₁, r₅⟩, -, hfr⟩ :=
    runLe_embed (φV c yes no) (embeds_vprog hyes hno) hr hag
  rw [show φV c yes no (if f x w then yes else no) = .clean (f x w) by
    cases f x w <;> simp [φV, hyn.symm]] at r₅
  have r := (((r₁.trans r₂).trans r₃).trans r₄).trans r₅
  have hl := stk_length_le (vtm c cX cW gX gW start yes no) (N := N)
    (update_length_le (c := c) (α := Verifier.G) .inp _) r
  obtain ⟨n₆, hn₆, r₆⟩ := cleanup_run (M := M) (o := .out) (ans := f x w) rfl _ v T₁ hl
  have hout : T₁ .out = [] := by
    rw [hfr .out (fun k h => by simp [emb] at h), h3k _ (by simp) (by simp) (by simp),
      update_of_ne (by simp), h1k _ (by simp) (by simp) (by simp)]
    simp [hS₀]
  rw [hout, update_eq_self] at r₆
  have r₇ : Run M 1 ⟨some (.fin (f x w)), false, fun _ => []⟩
      ⟨none, false, update (fun _ => []) .out [f x w]⟩ := Run.single rfl
  refine ⟨_, ?_, (r.trans r₆).trans r₇⟩
  rw [vtime_eval]
  have hp := TM2Composition.eval_mono p (show x.length + w.length ≤ N by omega)
  have h2 := Nat.mul_le_mul_left (TM2Composition.pushBound (vtm c cX cW gX gW start yes no))
    (show 2 * x.length + 2 + 1 + (2 * w.length + 2) + 1 + n₁ ≤ 2 * N + 4 + p.eval N by omega)
  omega

/-- **Verifier host.** Let $c$ be a component machine with stacks $c_X \ne c_W$, maps $g_X$ and
$g_W$ from bits to the alphabets of $c_X$ and $c_W$, and labels $\mathit{start}$, $\mathit{yes}$
and $\mathit{no}$ with $\mathit{yes} \ne \mathit{no}$, where the program halts at $\mathit{yes}$
and at $\mathit{no}$. Let $f$ assign a boolean to each pair of bit lists and let $p$ be a
polynomial with natural number coefficients. Suppose that for all bit lists $x$ and $w$, the
component started at $\mathit{start}$ with state false, the bits of $x$ mapped by $g_X$ on $c_X$,
the bits of $w$ mapped by $g_W$ on $c_W$ and every other stack empty reaches the label
$\mathit{yes}$ if $f(x, w)$ is true and $\mathit{no}$ otherwise within $p(|x| + |w|)$ steps. Then
the verifier host machine computes $(x, w) \mapsto f(x, w)$ in polynomial time, with the verifier
host's step bound for $p$ as time bound: on the pair encoding of $(x, w)$, over the pair alphabet,
it outputs the one-element bit list $[f(x, w)]$. -/
noncomputable def verifier (f : List Bool → List Bool → Bool) (p : Polynomial ℕ) (hXW : cX ≠ cW)
    (hyn : yes ≠ no) (hyes : c.prog yes = .halt) (hno : c.prog no = .halt)
    (hrun : ∀ x w, ∃ v S', RunLe c.prog (p.eval (x.length + w.length))
      ⟨some start, false, update (update (fun _ => []) cX (x.map gX)) cW (w.map gW)⟩
      ⟨some (if f x w then yes else no), v, S'⟩) :
    TM2ComputableInPolyTime Verifier.pairEncode (fun b : Bool => [b]) (fun q => f q.1 q.2) where
  tm := vtm c cX cW gX gW start yes no
  inputAlphabet := Equiv.refl Verifier.G
  outputAlphabet := Equiv.refl Bool
  time := vtime c cX cW gX gW start yes no p
  outputsFun := fun q => by
    obtain ⟨x, w⟩ := q
    have h := vprog_run f p hXW hyn hyes hno hrun x w
    unfold RunLe at h
    refine ⟨⟨Classical.choose h, ?_⟩, (Classical.choose_spec h).1⟩
    erw [List.map_id, List.map_id, initList_eq, Option.map_some, haltList_eq]
    exact (Classical.choose_spec h).2

/-- **Verifier host, canonical form.** Let $c$ be a component machine with distinct stacks $c_X$
and $c_W$ and labels $\mathit{start}$, $\mathit{yes}$ and $\mathit{no}$, where
$\mathit{yes} \ne \mathit{no}$ and the statements at $\mathit{yes}$ and $\mathit{no}$ are the
halting statement. Let $g_X$ and $g_W$ map bits to symbols of $c_X$ and $c_W$, let $f$ assign a
boolean $f(x, w)$ to all bit lists $x$ and $w$, and let $p$ be a polynomial with coefficients in
$\mathbb{N}$. Suppose that for all bit lists $x$ and $w$, the component started at
$\mathit{start}$ with internal state false, with $g_X$ applied to each bit of $x$ on $c_X$, $g_W$
applied to each bit of $w$ on $c_W$ and every other stack empty, reaches in at most
$p(|x| + |w|)$ steps the label $\mathit{yes}$ if $f(x, w)$ is true and the label $\mathit{no}$ if
it is false. Then the map $(x, w) \mapsto f(x, w)$ on pairs of bit lists is polynomial-time
computable for the canonical bitstring encodings. -/
theorem isPolyTime_verifier (f : List Bool → List Bool → Bool) (p : Polynomial ℕ)
    (hXW : cX ≠ cW) (hyn : yes ≠ no) (hyes : c.prog yes = .halt) (hno : c.prog no = .halt)
    (hrun : ∀ x w, ∃ v S', RunLe c.prog (p.eval (x.length + w.length))
      ⟨some start, false, update (update (fun _ => []) cX (x.map gX)) cW (w.map gW)⟩
      ⟨some (if f x w then yes else no), v, S'⟩) :
    ComplexityTheory.IsPolyTime fun q : List Bool × List Bool => f q.1 q.2 :=
  tm2ComputableInPolyTime_comp (f := id) (g := fun q : List Bool × List Bool => f q.1 q.2)
    Converter.computable (verifier f p hXW hyn hyes hno hrun)

end Verifier

end Cslib.Complexity.Host
