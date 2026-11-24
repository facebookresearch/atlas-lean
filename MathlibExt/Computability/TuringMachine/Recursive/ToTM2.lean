/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Recursive functions are Turing-computable
-/
module

public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Computability.TuringMachine.ToPartrec
public import Mathlib.Computability.PartrecBasis
public import Mathlib.Data.Num.Lemmas

/-!
# Recursive functions are Turing-computable

The forward half of the Turing–Kleene equivalence for Mathlib's bundled finite multi-stack
machines (the TM2 model): every `Computable` function `f : ℕ → ℕ` is computed by a `FinTM2`
under the binary encoding `Computability.encodeNat`.

Mathlib's `Turing.PartrecToTM2.tr` is a TM2 machine that evaluates any
`ToPartrec.Code` (`tr_eval`), but its label type is infinite and its input and output are
lists of naturals in the alphabet `Γ'`.  `fwdTM c` wraps it into a `FinTM2`:

* stacks `K' ⊕ Bool`: the four stacks of `tr`, an input stack of bits and an output stack of
  bits;
* labels `Phase ⊕ {l // l ∈ codeSupp c halt}`: finitely many labels of `tr`, all it can
  reach (`tr_supports`), and five labels for the adapters;
* a pre-phase copies the input bits onto `tr`'s main stack as `trList [n]`, the main phase
  runs `tr` with `halt` redirected to the post-phase (`restrict`), and the post-phase copies
  `trList [f n]` back as bits.

## Main results

- `tm2Computable_of_computable` : a `Computable` function `ℕ → ℕ` is computed by a `FinTM2`
  under `encodeNat`.
-/

@[expose] public section

set_option autoImplicit false

namespace MetaMathlibExt.TM2Recursive

open Turing Turing.PartrecToTM2 Turing.ToPartrec
open Computability (encodeNat encodeNum encodePosNum)

/-! ### Bits and `Γ'` -/

/-- **Bits as stack symbols.** Let
$\Gamma' = \{\mathtt{cons}_l, \mathtt{cons}, \mathtt{bit0}, \mathtt{bit1}\}$ be the stack alphabet
of Mathlib's multi-stack machine $\mathrm{tr}$ that evaluates partial recursive codes. This is
the map from bits to $\Gamma'$ that sends $\mathrm{true}$ to $\mathtt{bit1}$ and $\mathrm{false}$
to $\mathtt{bit0}$. -/
def boolToΓ' : Bool → Γ'
  | true => Γ'.bit1
  | false => Γ'.bit0

/-- **Reading a stack symbol as a bit.** The map from the stack alphabet $\Gamma'$ of Mathlib's code
evaluator (symbols $\mathrm{cons}_l$, $\mathrm{cons}$, $\mathrm{bit0}$, $\mathrm{bit1}$) to the
booleans sends $\mathrm{bit1}$ to true and every other symbol to false. -/
def Γ'ToBool : Γ' → Bool
  | Γ'.bit1 => true
  | _ => false

@[simp] theorem Γ'ToBool_boolToΓ' (b : Bool) : Γ'ToBool (boolToΓ' b) = b := by
  cases b <;> rfl

theorem trPosNum_eq_map (p : PosNum) : trPosNum p = (encodePosNum p).map boolToΓ' := by
  induction p with
  | one => rfl
  | bit0 p ih => simp [trPosNum, encodePosNum, ih, boolToΓ']
  | bit1 p ih => simp [trPosNum, encodePosNum, ih, boolToΓ']

/-- **The evaluator encodes numbers in binary.** For every natural number $n$, the list of stack
symbols by which Mathlib's code evaluator encodes $n$ is obtained from the binary encoding of $n$
(least significant bit first) by writing each bit as $\mathrm{bit1}$ if it is true and as
$\mathrm{bit0}$ if it is false. -/
theorem trNat_eq_map (n : ℕ) : trNat n = (encodeNat n).map boolToΓ' := by
  unfold trNat encodeNat
  cases (n : Num) with
  | zero => rfl
  | pos p => exact trPosNum_eq_map p

theorem boolToΓ'_ne_cons (b : Bool) : boolToΓ' b ≠ Γ'.cons := by cases b <;> decide

/-! ### The wrapped machine -/

/-- **The stack set $K'$ is finite.** The set
$K' = \{\mathrm{main}, \mathrm{rev}, \mathrm{aux}, \mathrm{stack}\}$ of the four stacks of
Mathlib's multi-stack machine that evaluates partial recursive codes is a finite type whose
elements are exactly these four stacks. -/
@[instance_reducible]
def fintypeK' : Fintype K' :=
  ⟨{K'.main, K'.rev, K'.aux, K'.stack}, fun k ↦ by cases k <;> simp⟩

attribute [local instance] fintypeK'

/-- **Adapter labels.** The type with exactly the five elements pre0, pre1, pre2, post1 and post2,
with decidable equality.

They label the wrapped machine's pre-phase, which copies the input bits onto the main stack of
Mathlib's code-evaluating machine $\mathrm{tr}$, and its post-phase, which copies the result back
to the output stack. -/
inductive Phase
  | pre0 | pre1 | pre2 | post1 | post2
  deriving DecidableEq

instance : Fintype Phase :=
  ⟨{.pre0, .pre1, .pre2, .post1, .post2}, fun p ↦ by cases p <;> simp⟩

/-- **Stack alphabets of the wrapped machine.** Let $\mathrm{tr}$ be Mathlib's multi-stack machine
that evaluates partial recursive codes, with stacks
$K' = \{\mathrm{main}, \mathrm{rev}, \mathrm{aux}, \mathrm{stack}\}$ and alphabet
$\Gamma' = \{\mathtt{cons}_l, \mathtt{cons}, \mathtt{bit0}, \mathtt{bit1}\}$. The stacks of the
wrapped machine are indexed by $K' \sqcup \{\mathrm{false}, \mathrm{true}\}$: each stack in $K'$
has alphabet $\Gamma'$, and the two stacks $\mathrm{false}$ and $\mathrm{true}$ (the input and
output stacks of the wrapped machine) have the alphabet $\{\mathrm{false}, \mathrm{true}\}$ of
bits. -/
abbrev FΓ : K' ⊕ Bool → Type := Sum.elim (fun _ ↦ Γ') (fun _ ↦ Bool)

variable (c : Code)

/-- **Support of a code.** For a code $c$, the support of $c$ is the finite set of labels of
Mathlib's code evaluator $\mathrm{tr}$ that Mathlib associates with evaluating $c$ under the
halting continuation.

It contains the label at which this evaluation starts and is closed under the steps of
$\mathrm{tr}$, so it contains every label reachable from there. -/
abbrev supp : Finset Λ' := codeSupp c Cont'.halt

/-- **Labels of the wrapped machine.** Let $c$ be a partial recursive code and let $\mathrm{tr}$ be
Mathlib's multi-stack machine that evaluates such codes. The labels of the wrapped machine for $c$
form the disjoint union $\mathrm{Phase} \sqcup \mathrm{supp}(c)$, where
$\mathrm{Phase} = \{\mathrm{pre}_0, \mathrm{pre}_1, \mathrm{pre}_2, \mathrm{post}_1,
\mathrm{post}_2\}$ is the set of five adapter labels and $\mathrm{supp}(c)$ is Mathlib's support
of $\mathrm{tr}$ for $c$ with the halting continuation: a finite set of labels of $\mathrm{tr}$
that contains the start label for $c$ and is closed under the steps of $\mathrm{tr}$. -/
abbrev FΛ := Phase ⊕ {l // l ∈ supp c}

/-- **Statements of the wrapped machine.** Let $c$ be a partial recursive code, and let
$\mathrm{tr}$ be Mathlib's multi-stack machine that evaluates such codes, with stacks
$K' = \{\mathrm{main}, \mathrm{rev}, \mathrm{aux}, \mathrm{stack}\}$ and alphabet
$\Gamma' = \{\mathtt{cons}_l, \mathtt{cons}, \mathtt{bit0}, \mathtt{bit1}\}$. A statement of the
wrapped machine for $c$ is a statement of Mathlib's multi-stack (TM2) Turing machine model whose
stacks are indexed by $K' \sqcup \{\mathrm{false}, \mathrm{true}\}$, where each stack in $K'$ has
alphabet $\Gamma'$ and the stacks $\mathrm{false}$ and $\mathrm{true}$ have the alphabet
$\{\mathrm{false}, \mathrm{true}\}$ of bits, whose labels are the labels of the wrapped machine
for $c$, and whose internal states are the optional symbols of $\Gamma'$ (a symbol of $\Gamma'$,
or none). -/
abbrev FStmt := TM2.Stmt FΓ (FΛ c) (Option Γ')

/-- **Restricting a statement of the code evaluator to the wrapped machine.** Let $\mathrm{tr}$ be
Mathlib's four-stack machine that evaluates partial recursive codes, and let $S$ be the support
of a code $c$. A statement $q$ of $\mathrm{tr}$ all of whose jump targets lie in $S$ becomes a
statement of the wrapped machine of $c$ with the same structure: each push, peek and pop acts on
the same stack of $\mathrm{tr}$ inside the wrapped machine with the same function, loads and
branches are kept, each jump goes to the same label of $\mathrm{tr}$, now read as an element of
$S$, and halting becomes a jump to the first post-phase label. -/
noncomputable def restrict :
    (q : TM2.Stmt (fun _ : K' ↦ Γ') Λ' (Option Γ')) → TM2.SupportsStmt (supp c) q → FStmt c
  | .push k f q, hq => .push (Sum.inl k) f (restrict q hq)
  | .peek k f q, hq => .peek (Sum.inl k) f (restrict q hq)
  | .pop k f q, hq => .pop (Sum.inl k) f (restrict q hq)
  | .load a q, hq => .load a (restrict q hq)
  | .branch p q₁ q₂, hq => .branch p (restrict q₁ hq.1) (restrict q₂ hq.2)
  | .goto l, hq => .goto fun v ↦ Sum.inr ⟨l v, hq v⟩
  | .halt, _ => .goto fun _ ↦ Sum.inl Phase.post1

/-- **The start label lies in the support.** For every code $c$, the label at which Mathlib's code
evaluator $\mathrm{tr}$ begins evaluating $c$ with the halting continuation belongs to the
support of $c$. -/
theorem start_mem : trNormal c Cont'.halt ∈ supp c := (tr_supports c Cont'.halt).1

/-- **The program of the wrapped machine.** Let $c$ be a partial recursive code and let
$\mathrm{tr}$ be Mathlib's multi-stack machine that evaluates such codes, with stacks
$\mathrm{main}, \mathrm{rev}, \mathrm{aux}, \mathrm{stack}$ and alphabet
$\Gamma' = \{\mathtt{cons}_l, \mathtt{cons}, \mathtt{bit0}, \mathtt{bit1}\}$. The program of the
wrapped machine for $c$ assigns a statement to each of its labels, namely the five adapter labels
$\mathrm{pre}_0, \mathrm{pre}_1, \mathrm{pre}_2, \mathrm{post}_1, \mathrm{post}_2$ and the labels
in Mathlib's finite support $\mathrm{supp}(c)$ of $\mathrm{tr}$ for $c$ with the halting
continuation. The internal state $v$ is a symbol of $\Gamma'$ or none, the input stack is the bit
stack $\mathrm{false}$ and the output stack is the bit stack $\mathrm{true}$.

At $\mathrm{pre}_0$: push $\mathtt{cons}$ onto $\mathrm{main}$ and go to $\mathrm{pre}_1$.

At $\mathrm{pre}_1$: pop the input stack and set $v$ to the popped bit as a symbol of $\Gamma'$
($\mathtt{bit1}$ for $\mathrm{true}$, $\mathtt{bit0}$ for $\mathrm{false}$), or to none if the
input stack is empty; if $v$ is a symbol, push it onto $\mathrm{rev}$ and go to $\mathrm{pre}_1$,
otherwise go to $\mathrm{pre}_2$.

At $\mathrm{pre}_2$: pop $\mathrm{rev}$ and set $v$ to the popped symbol (none if $\mathrm{rev}$
is empty); if $v$ is a symbol, push it onto $\mathrm{main}$ and go to $\mathrm{pre}_2$, otherwise
go to the start label of $\mathrm{tr}$ for $c$ with the halting continuation, which lies in
$\mathrm{supp}(c)$.

At a label $l \in \mathrm{supp}(c)$: execute the statement of $\mathrm{tr}$ at $l$, acting on the
stacks of $\mathrm{tr}$, where every jump of $\mathrm{tr}$ becomes a jump to the same label in
$\mathrm{supp}(c)$ and every halt becomes a jump to $\mathrm{post}_1$.

At $\mathrm{post}_1$: pop $\mathrm{main}$ and set $v$ to the popped symbol (none if
$\mathrm{main}$ is empty); if $v$ is none or $\mathtt{cons}$, go to $\mathrm{post}_2$, otherwise
push $v$ onto $\mathrm{rev}$ and go to $\mathrm{post}_1$.

At $\mathrm{post}_2$: pop $\mathrm{rev}$ and set $v$ to the popped symbol (none if $\mathrm{rev}$
is empty); if $v$ is a symbol, push onto the output stack the bit that is $\mathrm{true}$ if
$v = \mathtt{bit1}$ and $\mathrm{false}$ otherwise, and go to $\mathrm{post}_2$; otherwise halt. -/
noncomputable def fwdProg : FΛ c → FStmt c
  | Sum.inl Phase.pre0 =>
    .push (Sum.inl K'.main) (fun _ ↦ Γ'.cons) (.goto fun _ ↦ Sum.inl Phase.pre1)
  | Sum.inl Phase.pre1 =>
    .pop (Sum.inr false) (fun _ ob ↦ ob.map boolToΓ')
      (.branch Option.isSome
        (.push (Sum.inl K'.rev) (fun v ↦ v.getD default) (.goto fun _ ↦ Sum.inl Phase.pre1))
        (.goto fun _ ↦ Sum.inl Phase.pre2))
  | Sum.inl Phase.pre2 =>
    .pop (Sum.inl K'.rev) (fun _ o ↦ o)
      (.branch Option.isSome
        (.push (Sum.inl K'.main) (fun v ↦ v.getD default) (.goto fun _ ↦ Sum.inl Phase.pre2))
        (.goto fun _ ↦ Sum.inr ⟨trNormal c Cont'.halt, start_mem c⟩))
  | Sum.inr l => restrict c (tr l.1) ((tr_supports c Cont'.halt).2 l.1 l.2)
  | Sum.inl Phase.post1 =>
    .pop (Sum.inl K'.main) (fun _ o ↦ o)
      (.branch (fun v ↦ v.elim true fun g ↦ g = Γ'.cons)
        (.goto fun _ ↦ Sum.inl Phase.post2)
        (.push (Sum.inl K'.rev) (fun v ↦ v.getD default) (.goto fun _ ↦ Sum.inl Phase.post1)))
  | Sum.inl Phase.post2 =>
    .pop (Sum.inl K'.rev) (fun _ o ↦ o)
      (.branch Option.isSome
        (.push (Sum.inr true) (fun v ↦ Γ'ToBool (v.getD default))
          (.goto fun _ ↦ Sum.inl Phase.post2))
        .halt)

/-- **The wrapped machine of a code.** Let $c$ be a code for a partial recursive function on lists
of natural numbers, and let $\mathrm{tr}$ be Mathlib's multi-stack machine that evaluates such
codes, with stacks $K' = \{\mathrm{main}, \mathrm{rev}, \mathrm{aux}, \mathrm{stack}\}$ and
alphabet $\Gamma' = \{\mathtt{cons}_l, \mathtt{cons}, \mathtt{bit0}, \mathtt{bit1}\}$. The
wrapped machine of $c$ is the finite multi-stack machine whose stacks are indexed by
$K' \sqcup \{\mathrm{false}, \mathrm{true}\}$, with alphabet $\Gamma'$ on each stack in $K'$ and
the alphabet of bits on the stacks $\mathrm{false}$ and $\mathrm{true}$; its input stack is
$\mathrm{false}$ and its output stack is $\mathrm{true}$; its labels are the labels of the
wrapped machine for $c$, with main label the first pre-phase adapter label $\mathrm{pre}_0$;
its internal states are the optional symbols of $\Gamma'$ (a symbol of $\Gamma'$, or none), with
initial state none; and its program is the program of the wrapped machine for $c$. -/
noncomputable def fwdTM : FinTM2 where
  K := K' ⊕ Bool
  k₀ := Sum.inr false
  k₁ := Sum.inr true
  Γ := FΓ
  Λ := FΛ c
  main := Sum.inl Phase.pre0
  σ := Option Γ'
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := fwdProg c

/-! ### Stacks -/

/-- **Stack contents of the wrapped machine.** Given lists $a, b, c, d$ of symbols of $\Gamma'$
and lists $i, o$ of bits, the stack contents of the wrapped machine with $a$, $b$, $c$ and $d$ on
the stacks main, rev, aux and stack, $i$ on the input stack and $o$ on the output stack. -/
def mkStk (a b c' d : List Γ') (i o : List Bool) : ∀ k, List (FΓ k)
  | Sum.inl K'.main => a
  | Sum.inl K'.rev => b
  | Sum.inl K'.aux => c'
  | Sum.inl K'.stack => d
  | Sum.inr false => i
  | Sum.inr true => o

@[simp] theorem mkStk_update_main (a b c' d : List Γ') (i o : List Bool) (x : List Γ') :
    Function.update (mkStk a b c' d i o) (Sum.inl K'.main) x = mkStk x b c' d i o := by
  funext k; rcases k with (_ | _ | _ | _) | (_ | _) <;> rfl

@[simp] theorem mkStk_update_rev (a b c' d : List Γ') (i o : List Bool) (x : List Γ') :
    Function.update (mkStk a b c' d i o) (Sum.inl K'.rev) x = mkStk a x c' d i o := by
  funext k; rcases k with (_ | _ | _ | _) | (_ | _) <;> rfl

@[simp] theorem mkStk_update_aux (a b c' d : List Γ') (i o : List Bool) (x : List Γ') :
    Function.update (mkStk a b c' d i o) (Sum.inl K'.aux) x = mkStk a b x d i o := by
  funext k; rcases k with (_ | _ | _ | _) | (_ | _) <;> rfl

@[simp] theorem mkStk_update_stack (a b c' d : List Γ') (i o : List Bool) (x : List Γ') :
    Function.update (mkStk a b c' d i o) (Sum.inl K'.stack) x = mkStk a b c' x i o := by
  funext k; rcases k with (_ | _ | _ | _) | (_ | _) <;> rfl

@[simp] theorem mkStk_update_in (a b c' d : List Γ') (i o : List Bool) (x : List Bool) :
    Function.update (mkStk a b c' d i o) (Sum.inr false) x = mkStk a b c' d x o := by
  funext k; rcases k with (_ | _ | _ | _) | (_ | _) <;> rfl

@[simp] theorem mkStk_update_out (a b c' d : List Γ') (i o : List Bool) (x : List Bool) :
    Function.update (mkStk a b c' d i o) (Sum.inr true) x = mkStk a b c' d i x := by
  funext k; rcases k with (_ | _ | _ | _) | (_ | _) <;> rfl

/-- **Configurations of the wrapped machine.** Let $c$ be a partial recursive code, and let
$\Gamma' = \{\mathtt{cons}_l, \mathtt{cons}, \mathtt{bit0}, \mathtt{bit1}\}$ be the alphabet of
Mathlib's multi-stack machine $\mathrm{tr}$ that evaluates such codes. A configuration of the
wrapped machine for $c$ is a configuration of Mathlib's multi-stack (TM2) Turing machine model
with the stack alphabets and labels of the wrapped machine for $c$ and internal states the
optional symbols of $\Gamma'$: it consists of an optional current label (none once the machine
has halted), an internal state that is a symbol of $\Gamma'$ or none, and for each stack $k$ a
finite list of symbols of the alphabet of $k$. -/
abbrev FCfg := TM2.Cfg FΓ (FΛ c) (Option Γ')

/-- **One step of the wrapped machine.** For a partial recursive code $c$, the step function of the
wrapped machine for $c$ is Mathlib's multi-stack (TM2) step function for the program of the
wrapped machine for $c$. It sends a configuration without a current label (a halted one) to
none, and a configuration with current label $l$ to the configuration obtained by executing the
statement that the program assigns to $l$ on its internal state and stacks. -/
noncomputable abbrev fstep : FCfg c → Option (FCfg c) := TM2.step (fwdProg c)

/-- **Iterated steps of the wrapped machine.** Let $c$ be a partial recursive code and let $s$ be
the map that sends none to none and a configuration $d$ of the wrapped machine for $c$ to the
result of one step of the wrapped machine on $d$ (which is none if $d$ has halted). For
$j \in \mathbb{N}$ and $x$ either a configuration of the wrapped machine for $c$ or none, the
$j$-fold run from $x$ is $s^{j}(x)$, the result of applying $s$ to $x$ $j$ times. -/
noncomputable abbrev frun (j : ℕ) (x : Option (FCfg c)) : Option (FCfg c) :=
  (flip bind (fstep c))^[j] x

theorem frun_add (j₁ j₂ : ℕ) (x : Option (FCfg c)) :
    frun c (j₁ + j₂) x = frun c j₁ (frun c j₂ x) := Function.iterate_add_apply _ _ _ _

theorem frun_succ (j : ℕ) (d : FCfg c) :
    frun c (j + 1) (some d) = frun c j (fstep c d) := Function.iterate_succ_apply _ _ _

theorem frun_zero (x : Option (FCfg c)) : frun c 0 x = x := rfl

theorem frun_one (d : FCfg c) : frun c 1 (some d) = fstep c d := rfl

/-! ### The pre-phase -/

/-- **The first pre-phase loop of the wrapped machine.** Write $\Gamma'$ for the stack alphabet of
Mathlib's code evaluator. Let $c$ be a code, $a$, $r$, $x$ and $y$ lists of symbols of $\Gamma'$,
$b$ a list of bits of length $k$ and $v$ an internal state (a symbol of $\Gamma'$ or none), and
write $\beta(b)$ for $b$ with each bit $\mathrm{true}$ replaced by the symbol bit1 and each bit
$\mathrm{false}$ by the symbol bit0 of $\Gamma'$. Started at the adapter label pre1 with internal
state $v$, the lists $a$, $r$, $x$ and $y$ on the stacks main, rev, aux and stack, $b$ on the
input stack and the output stack empty, the wrapped machine of $c$ is after exactly $k + 1$ steps
at the adapter label pre2 with internal state none, the reversal of $\beta(b)$ followed by $r$ on
the rev stack, $a$, $x$ and $y$ still on the stacks main, aux and stack, and the input and output
stacks empty. -/
theorem pre1_loop (a b c' d : List Γ') (bits : List Bool) (v : Option Γ') :
    frun c (bits.length + 1) (some ⟨some (Sum.inl Phase.pre1), v, mkStk a b c' d bits []⟩) =
      some ⟨some (Sum.inl Phase.pre2), none,
        mkStk a ((bits.map boolToΓ').reverse ++ b) c' d [] []⟩ := by
  induction bits generalizing b v with
  | nil =>
    rw [List.length_nil, frun_one]
    simp [fwdProg, TM2.step, TM2.stepAux, mkStk]
  | cons x bits ih =>
    rw [List.length_cons, frun_succ]
    have : fstep c ⟨some (Sum.inl Phase.pre1), v, mkStk a b c' d (x :: bits) []⟩ =
        some ⟨some (Sum.inl Phase.pre1), some (boolToΓ' x),
          mkStk a (boolToΓ' x :: b) c' d bits []⟩ := by
      simp [fwdProg, TM2.step, TM2.stepAux, mkStk]
    rw [this, ih]
    simp

theorem pre2_loop (a r c' d : List Γ') (v : Option Γ') :
    frun c (r.length + 1) (some ⟨some (Sum.inl Phase.pre2), v, mkStk a r c' d [] []⟩) =
      some ⟨some (Sum.inr ⟨trNormal c Cont'.halt, start_mem c⟩), none,
        mkStk (r.reverse ++ a) [] c' d [] []⟩ := by
  induction r generalizing a v with
  | nil =>
    rw [List.length_nil, frun_one]
    simp [fwdProg, TM2.step, TM2.stepAux, mkStk]
  | cons x r ih =>
    rw [List.length_cons, frun_succ]
    have : fstep c ⟨some (Sum.inl Phase.pre2), v, mkStk a (x :: r) c' d [] []⟩ =
        some ⟨some (Sum.inl Phase.pre2), some x, mkStk (x :: a) r c' d [] []⟩ := by
      simp [fwdProg, TM2.step, TM2.stepAux, mkStk]
    rw [this, ih]
    simp

/-- **Pre-phase of the wrapped machine.** Let $c$ be a code and $b$ a list of bits of length $k$,
and write $\beta(b)$ for $b$ with each bit $0$ replaced by the symbol bit0 and each bit $1$ by the
symbol bit1 of $\Gamma'$. Started at the adapter label pre0 with empty local state, $b$ on the
input stack and all other stacks empty, the wrapped machine is after exactly $2(k + 1) + 1$ steps
at the label $\mathrm{trNormal}(c, \mathrm{halt})$ at which Mathlib's code-evaluating machine
$\mathrm{tr}$ starts evaluating $c$, with empty local state, $\beta(b)$ followed by the symbol
cons on the main stack and all other stacks empty. -/
theorem pre_phase (bits : List Bool) :
    frun c (bits.length + 1 + (bits.length + 1) + 1)
        (some ⟨some (Sum.inl Phase.pre0), none, mkStk [] [] [] [] bits []⟩) =
      some ⟨some (Sum.inr ⟨trNormal c Cont'.halt, start_mem c⟩), none,
        mkStk (bits.map boolToΓ' ++ [Γ'.cons]) [] [] [] [] []⟩ := by
  rw [frun_succ]
  have h0 : fstep c ⟨some (Sum.inl Phase.pre0), none, mkStk [] [] [] [] bits []⟩ =
      some ⟨some (Sum.inl Phase.pre1), none, mkStk [Γ'.cons] [] [] [] bits []⟩ := by
    simp [fwdProg, TM2.step, TM2.stepAux, mkStk]
  rw [h0, frun_add, pre1_loop]
  have hlen : bits.length = ((bits.map boolToΓ').reverse ++ []).length := by simp
  rw [hlen, pre2_loop]
  simp

/-! ### The post-phase -/

/-- **The first post-phase loop of the wrapped machine.** Write $\Gamma'$ for the stack alphabet of
Mathlib's code evaluator. Let $c$ be a code, $b$ a list of bits of length $k$, $r$ a list of
symbols of $\Gamma'$, $o$ a list of bits and $v$ an internal state (a symbol of $\Gamma'$ or
none), and write $\beta(b)$ for $b$ with each bit $\mathrm{true}$ replaced by the symbol bit1 and
each bit $\mathrm{false}$ by the symbol bit0 of $\Gamma'$. Started at the adapter label post1
with internal state $v$, $\beta(b)$ followed by the symbol cons on the main stack, $r$ on the rev
stack, $o$ on the output stack and all other stacks empty, the wrapped machine of $c$ is after
exactly $k + 1$ steps at the adapter label post2 with internal state cons, the reversal of
$\beta(b)$ followed by $r$ on the rev stack, $o$ on the output stack and all other stacks
empty. -/
theorem post1_loop (bits : List Bool) (r : List Γ') (o : List Bool) (v : Option Γ') :
    frun c (bits.length + 1) (some ⟨some (Sum.inl Phase.post1), v,
        mkStk (bits.map boolToΓ' ++ [Γ'.cons]) r [] [] [] o⟩) =
      some ⟨some (Sum.inl Phase.post2), some Γ'.cons,
        mkStk [] ((bits.map boolToΓ').reverse ++ r) [] [] [] o⟩ := by
  induction bits generalizing r v with
  | nil =>
    rw [List.length_nil, frun_one]
    simp [fwdProg, TM2.step, TM2.stepAux, mkStk]
  | cons x bits ih =>
    rw [List.length_cons, frun_succ]
    have : fstep c ⟨some (Sum.inl Phase.post1), v,
        mkStk ((x :: bits).map boolToΓ' ++ [Γ'.cons]) r [] [] [] o⟩ =
        some ⟨some (Sum.inl Phase.post1), some (boolToΓ' x),
          mkStk (bits.map boolToΓ' ++ [Γ'.cons]) (boolToΓ' x :: r) [] [] [] o⟩ := by
      simp [fwdProg, TM2.step, TM2.stepAux, mkStk, boolToΓ'_ne_cons]
    rw [this, ih]
    simp

theorem post2_loop (r : List Γ') (o : List Bool) (v : Option Γ') :
    frun c (r.length + 1) (some ⟨some (Sum.inl Phase.post2), v, mkStk [] r [] [] [] o⟩) =
      some ⟨none, none, mkStk [] [] [] [] [] ((r.map Γ'ToBool).reverse ++ o)⟩ := by
  induction r generalizing o v with
  | nil =>
    rw [List.length_nil, frun_one]
    simp [fwdProg, TM2.step, TM2.stepAux, mkStk]
  | cons x r ih =>
    rw [List.length_cons, frun_succ]
    have : fstep c ⟨some (Sum.inl Phase.post2), v, mkStk [] (x :: r) [] [] [] o⟩ =
        some ⟨some (Sum.inl Phase.post2), some x, mkStk [] r [] [] [] (Γ'ToBool x :: o)⟩ := by
      simp [fwdProg, TM2.step, TM2.stepAux, mkStk]
    rw [this, ih]
    simp

/-- **Post-phase of the wrapped machine.** Let $c$ be a code and $b$ a list of bits of length
$k$, and write $\beta(b)$ for $b$ with each bit $0$ replaced by the symbol bit0 and each bit $1$ by
the symbol bit1 of $\Gamma'$. Started at the adapter label post1 with empty local state, $\beta(b)$
followed by the symbol cons on the main stack and all other stacks empty, the wrapped machine is
after exactly $2(k + 1)$ steps in the halting configuration (no label) with empty local state,
$b$ on the output stack and all other stacks empty. -/
theorem post_phase (bits : List Bool) :
    frun c ((bits.length + 1) + (bits.length + 1))
        (some ⟨some (Sum.inl Phase.post1), none,
          mkStk (bits.map boolToΓ' ++ [Γ'.cons]) [] [] [] [] []⟩) =
      some ⟨none, none, mkStk [] [] [] [] [] bits⟩ := by
  rw [frun_add, post1_loop]
  have hlen : bits.length = ((bits.map boolToΓ').reverse ++ []).length := by simp
  rw [hlen, post2_loop]
  simp [List.map_reverse, Function.comp_def]

/-! ### The main phase simulates `tr` -/

/-- **Lifting stacks of tr.** Given contents $s$ of the four stacks main, rev, aux and stack of
Mathlib's code-evaluating machine $\mathrm{tr}$, the stack contents of the wrapped machine that
agree with $s$ on these four stacks and have empty input and output stacks. -/
def liftStk (s : ∀ _ : K', List Γ') : ∀ k, List (FΓ k) :=
  mkStk (s K'.main) (s K'.rev) (s K'.aux) (s K'.stack) [] []

theorem liftStk_inl (s : ∀ _ : K', List Γ') (k : K') : liftStk s (Sum.inl k) = s k := by
  cases k <;> rfl

theorem liftStk_update (s : ∀ _ : K', List Γ') (k : K') (x : List Γ') :
    liftStk (Function.update s k x) = Function.update (liftStk s) (Sum.inl k) x := by
  cases k <;> simp [liftStk]

/-- **Correspondence of labels between the code evaluator and the wrapped machine.** Let $c$ be a
code for a partial recursive function on lists of natural numbers and let $\mathrm{tr}$ be
Mathlib's multi-stack machine that evaluates such codes. An optional label $o$ of $\mathrm{tr}$
(a label, or none for halting) corresponds to an optional label $o'$ of the wrapped machine for
$c$ when either $o$ is none and $o'$ is the first post-phase label $\mathrm{post}_1$, or $o$ is a
label $l$ of $\mathrm{tr}$ that lies in the support $\mathrm{supp}(c)$ of $c$ and $o'$ is $l$,
read as a label of the wrapped machine. -/
def LabelRel : Option Λ' → Option (FΛ c) → Prop
  | none, o' => o' = some (Sum.inl Phase.post1)
  | some l, o' => ∃ h : l ∈ supp c, o' = some (Sum.inr ⟨l, h⟩)

theorem stepAux_restrict (q : TM2.Stmt (fun _ : K' ↦ Γ') Λ' (Option Γ'))
    (hq : TM2.SupportsStmt (supp c) q) (v : Option Γ') (s : ∀ _ : K', List Γ') :
    (TM2.stepAux (restrict c q hq) v (liftStk s)).var = (TM2.stepAux q v s).var ∧
      (TM2.stepAux (restrict c q hq) v (liftStk s)).stk = liftStk (TM2.stepAux q v s).stk ∧
      LabelRel c (TM2.stepAux q v s).l (TM2.stepAux (restrict c q hq) v (liftStk s)).l := by
  induction q generalizing v s with
  | push k f q ih =>
    have hq' : TM2.SupportsStmt (supp c) q := hq
    rw [show restrict c (.push k f q) hq = .push (Sum.inl k) f (restrict c q hq') from rfl]
    simp only [TM2.stepAux]
    rw [liftStk_inl]
    have := ih hq' v (Function.update s k (f v :: s k))
    rw [liftStk_update] at this
    exact this
  | peek k f q ih =>
    have hq' : TM2.SupportsStmt (supp c) q := hq
    rw [show restrict c (.peek k f q) hq = .peek (Sum.inl k) f (restrict c q hq') from rfl]
    simp only [TM2.stepAux]
    rw [liftStk_inl]
    exact ih hq' _ s
  | pop k f q ih =>
    have hq' : TM2.SupportsStmt (supp c) q := hq
    rw [show restrict c (.pop k f q) hq = .pop (Sum.inl k) f (restrict c q hq') from rfl]
    simp only [TM2.stepAux]
    rw [liftStk_inl]
    have := ih hq' (f v (s k).head?) (Function.update s k (s k).tail)
    rw [liftStk_update] at this
    exact this
  | load a q ih =>
    have hq' : TM2.SupportsStmt (supp c) q := hq
    rw [show restrict c (.load a q) hq = .load a (restrict c q hq') from rfl]
    simp only [TM2.stepAux]
    exact ih hq' _ s
  | branch p q₁ q₂ ih₁ ih₂ =>
    rw [show restrict c (.branch p q₁ q₂) hq =
      .branch p (restrict c q₁ hq.1) (restrict c q₂ hq.2) from rfl]
    simp only [TM2.stepAux]
    cases p v
    · exact ih₂ hq.2 v s
    · exact ih₁ hq.1 v s
  | goto l => exact ⟨rfl, rfl, hq v, rfl⟩
  | halt => exact ⟨rfl, rfl, rfl⟩

/-- **Simulation relation between the code evaluator and the wrapped machine.** A configuration $x$
of Mathlib's code evaluator $\mathrm{tr}$ is related to a configuration $d$ of the wrapped machine
of a code $c$ when $d$ has the same internal state as $x$, the stacks of $d$ are the four stacks
of $x$ together with empty input and output stacks, and the labels correspond: if $x$ has halted
then $d$ is at the first post-phase label, and if $x$ is at a label $l$ then $l$ lies in the
support of $c$ and $d$ is at $l$. -/
def TrRel (x : Cfg') (d : FCfg c) : Prop :=
  d.var = x.var ∧ d.stk = liftStk x.stk ∧ LabelRel c x.l d.l

theorem step_rel {x : Cfg'} {d : FCfg c} (hxd : TrRel c x d) {x' : Cfg'}
    (hx' : TM2.step tr x = some x') : ∃ d', fstep c d = some d' ∧ TrRel c x' d' := by
  obtain ⟨l, v, s⟩ := x
  obtain ⟨hv, hs, hl⟩ := hxd
  cases l with
  | none => simp [TM2.step] at hx'
  | some l =>
    obtain ⟨h, hdl⟩ := hl
    obtain ⟨dl, dv, ds⟩ := d
    simp only at hv hs hdl
    subst hv hs hdl
    simp only [TM2.step] at hx'
    obtain rfl := Option.some.inj hx'
    obtain ⟨h₁, h₂, h₃⟩ := stepAux_restrict c (tr l) ((tr_supports c Cont'.halt).2 l h) dv s
    exact ⟨_, rfl, h₁, h₂, h₃⟩

theorem run_rel {x₀ : Cfg'} {d₀ : FCfg c} (h₀ : TrRel c x₀ d₀) :
    ∀ (j : ℕ) {x : Cfg'}, (flip bind (TM2.step tr))^[j] (some x₀) = some x →
      ∃ d, frun c j (some d₀) = some d ∧ TrRel c x d := by
  intro j
  induction j with
  | zero =>
    intro x hx
    obtain rfl := Option.some.inj hx
    exact ⟨d₀, rfl, h₀⟩
  | succ j ih =>
    intro x hx
    rw [Function.iterate_succ_apply'] at hx
    cases hj : (flip bind (TM2.step tr))^[j] (some x₀) with
    | none => rw [hj] at hx; cases hx
    | some x₁ =>
      rw [hj] at hx
      obtain ⟨d₁, hd₁, hrel⟩ := ih hj
      obtain ⟨d, hd, hrel'⟩ := step_rel c hrel hx
      refine ⟨d, ?_, hrel'⟩
      rw [frun, Function.iterate_succ_apply', ← frun, hd₁]
      exact hd

/-- **Reachability gives an iteration count.** Let $\alpha$ be a type, let $\bot \notin \alpha$,
and let $f : \alpha \to \alpha \cup \{\bot\}$ be a partial step function, where $f(x) = \bot$
means that no step is possible from $x$. Extend $f$ to
$\bar f : \alpha \cup \{\bot\} \to \alpha \cup \{\bot\}$ by $\bar f(\bot) = \bot$. If $b \in \alpha$
is reachable from $a \in \alpha$ under $f$, that is, $b$ is obtained from $a$ by finitely many
(possibly zero) steps $x \mapsto f(x)$ none of which gives $\bot$, then there is $N \in \mathbb{N}$
with $\bar f^{N}(a) = b$. -/
theorem exists_iterate_eq_of_reaches {α : Type*} {f : α → Option α} {a b : α}
    (h : StateTransition.Reaches f a b) : ∃ N, (flip bind f)^[N] (some a) = some b := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hbc ih =>
    obtain ⟨N, hN⟩ := ih
    exact ⟨N + 1, by rw [Function.iterate_succ_apply', hN]; exact hbc⟩

/-- **Main phase of the wrapped machine.** Let $c$ be a code and $f : \mathbb{N} \to \mathbb{N}$
such that $c$ evaluates to $[f(n)]$ on input $[n]$ for every $n$. Then for every $n$ there is
$N$ such that the wrapped machine, started at the label $\mathrm{trNormal}(c, \mathrm{halt})$ with
empty local state, the encoding $\mathrm{trList}([n])$ on the main stack and all other stacks
empty, is after exactly $N$ steps at the adapter label post1 with empty local state,
$\mathrm{trList}([f(n)])$ on the main stack and all other stacks empty. -/
theorem main_phase {f : ℕ → ℕ} (hc : ∀ n, c.eval [n] = pure [f n]) (n : ℕ) :
    ∃ N, frun c N (some ⟨some (Sum.inr ⟨trNormal c Cont'.halt, start_mem c⟩), none,
        mkStk (trList [n]) [] [] [] [] []⟩) =
      some ⟨some (Sum.inl Phase.post1), none, mkStk (trList [f n]) [] [] [] [] []⟩ := by
  have heval := tr_eval c [n]
  rw [hc n] at heval
  have hmem : halt [f n] ∈ StateTransition.eval (TM2.step tr) (init c [n]) := by
    rw [heval]
    exact Part.mem_map _ (Part.mem_some _)
  obtain ⟨N, hN⟩ := exists_iterate_eq_of_reaches (StateTransition.mem_eval.mp hmem).1
  have h₀ : TrRel c (init c [n]) ⟨some (Sum.inr ⟨trNormal c Cont'.halt, start_mem c⟩), none,
      mkStk (trList [n]) [] [] [] [] []⟩ := ⟨rfl, rfl, start_mem c, rfl⟩
  obtain ⟨⟨dl, dv, ds⟩, hd, hv, hs, hl⟩ := run_rel c h₀ N hN
  refine ⟨N, hd.trans ?_⟩
  simp only [halt] at hv hs hl
  simp only [LabelRel] at hl
  subst hv hs hl
  rfl

/-! ### Assembly -/

/-- **The evaluator's encoding of a one-element list.** For every natural number $m$, the list of
stack symbols by which Mathlib's code evaluator encodes the one-element list $[m]$ is the binary
encoding of $m$ (least significant bit first) with each bit written as $\mathrm{bit1}$ if it is
true and as $\mathrm{bit0}$ if it is false, followed by the symbol $\mathrm{cons}$. -/
theorem trList_singleton (m : ℕ) : trList [m] = (encodeNat m).map boolToΓ' ++ [Γ'.cons] := by
  simp [trList, trNat_eq_map]

/-- **The wrapped machine computes the function a code evaluates.** Let $c$ be a code and
$f : \mathbb{N} \to \mathbb{N}$ a function such that, for every $n$, evaluating $c$ on the
one-element list $[n]$ returns $[f(n)]$. Then the wrapped machine of $c$, with input and output
alphabet the booleans, computes $f$ under the binary encoding of natural numbers (least
significant bit first): for every $n$, started with the encoding of $n$ on its input stack and
all other stacks empty, it eventually halts in its initial internal state with the encoding of
$f(n)$ on its output stack and all other stacks empty. -/
noncomputable def tm2ComputableOfCode {f : ℕ → ℕ} (hc : ∀ n, c.eval [n] = pure [f n]) :
    TM2Computable encodeNat encodeNat f where
  tm := fwdTM c
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  outputsFun n :=
    ⟨((encodeNat (f n)).length + 1 + ((encodeNat (f n)).length + 1)) +
        ((main_phase c hc n).choose +
          ((encodeNat n).length + 1 + ((encodeNat n).length + 1) + 1)), by
      have hinit : initList (fwdTM c) ((encodeNat n).map (Equiv.refl Bool).invFun) =
          (⟨some (Sum.inl Phase.pre0), none, mkStk [] [] [] [] (encodeNat n) []⟩ : FCfg c) := by
        simp only [initList]
        congr 1
        funext k
        rcases k with (_ | _ | _ | _) | (_ | _)
        all_goals first
          | rfl
          | (simp only [fwdTM, mkStk, Equiv.refl, ↓reduceDIte]
             change List.map (id : Bool → Bool) _ = _
             exact List.map_id _)
      have hhalt : haltList (fwdTM c) ((encodeNat (f n)).map (Equiv.refl Bool).invFun) =
          (⟨none, none, mkStk [] [] [] [] [] (encodeNat (f n))⟩ : FCfg c) := by
        simp only [haltList]
        congr 1
        funext k
        rcases k with (_ | _ | _ | _) | (_ | _)
        all_goals first
          | rfl
          | (simp only [fwdTM, mkStk, Equiv.refl, ↓reduceDIte]
             change List.map (id : Bool → Bool) _ = _
             exact List.map_id _)
      have key : frun c (((encodeNat (f n)).length + 1 + ((encodeNat (f n)).length + 1)) +
          ((main_phase c hc n).choose +
            ((encodeNat n).length + 1 + ((encodeNat n).length + 1) + 1)))
          (some ⟨some (Sum.inl Phase.pre0), none, mkStk [] [] [] [] (encodeNat n) []⟩) =
          some ⟨none, none, mkStk [] [] [] [] [] (encodeNat (f n))⟩ := by
        rw [frun_add c ((encodeNat (f n)).length + 1 + ((encodeNat (f n)).length + 1)),
          frun_add c (main_phase c hc n).choose, pre_phase, ← trList_singleton,
          (main_phase c hc n).choose_spec, trList_singleton, post_phase]
      rw [hinit, Option.map_some, hhalt]
      exact key⟩

/-- **Recursive functions are Turing-computable.** Every computable function
$f : \mathbb{N} \to \mathbb{N}$ is computed by a finite multi-stack Turing machine (finitely
many stacks, labels and internal states) whose input and output alphabets are identified with
the booleans, under the binary encoding of natural numbers (least significant bit first, with
$0$ encoded as the empty list): for every $n$, the machine started with the encoding of $n$ on
its input stack and all other stacks empty eventually halts in its initial internal state with
the encoding of $f(n)$ on its output stack and all other stacks empty. -/
theorem tm2Computable_of_computable {f : ℕ → ℕ} (hf : Computable f) :
    Nonempty (TM2Computable encodeNat encodeNat f) := by
  have hp : Nat.Partrec' fun v : List.Vector ℕ 1 ↦ (f v.head : Part ℕ) :=
    Nat.Partrec'.part_iff₁.mpr hf.partrec
  obtain ⟨c, hc⟩ := Code.exists_code hp
  refine ⟨tm2ComputableOfCode c (f := f) fun n ↦ ?_⟩
  have := hc ⟨[n], rfl⟩
  simp only [Part.coe_some, Part.map_eq_map, Part.map_some] at this
  exact this

end MetaMathlibExt.TM2Recursive
