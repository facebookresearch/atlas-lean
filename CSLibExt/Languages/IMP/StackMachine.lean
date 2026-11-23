/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Stack machine and compilation correctness for IMP
-/
module

public import CSLibExt.Languages.IMP.BigStep
public import Mathlib.Logic.Relation

/-!
# Stack machine and compilation

A flat-code stack machine with an absolute program counter, together with a
compiler from IMP commands and expressions to machine code.

The correctness result proved here is forward compilation correctness: every
terminating big-step execution `BigStep c s s'` is simulated by the compiled
code `compile c 0`, which runs from the initial configuration `(0, [], s)` to
the halt program counter `(codeLength c, [], s')` with the same final state
and empty net stack effect. The converse simulation (every halting machine
run of compiled code corresponds to a big-step execution) is not claimed.

Boolean values are represented on the stack as `1` for true and `0` for false.
For binary instructions the top of the stack is the right operand and the
value below it is the left operand, matching the left-to-right compilation of
expressions. Subtraction is truncated natural subtraction, as in `AExp.sub`.
-/

@[expose] public section

namespace Cslib.IMP.StackMachine

/-- **Stack machine instructions.** An instruction of the stack machine is one of
$\mathsf{push}\ n$, $\mathsf{load}\ x$ and $\mathsf{store}\ x$ for natural numbers $n$ and $x$;
the arithmetic instructions $\mathsf{add}$, $\mathsf{sub}$ and $\mathsf{mul}$; the comparison and
Boolean instructions $\mathsf{eq}$, $\mathsf{le}$, $\mathsf{not}$ and $\mathsf{and}$; and the
jumps $\mathsf{jump}\ t$ and $\mathsf{jumpIfZero}\ t$ for a natural number $t$. Jump targets are
absolute program counters. -/
inductive Instr where
  | push (n : Nat)
  | load (x : Nat)
  | store (x : Nat)
  | add
  | sub
  | mul
  | eqI
  | leI
  | notI
  | andI
  | jump (target : Nat)
  | jumpIfZero (target : Nat)
  deriving DecidableEq, Repr

/-- **Stack machine configurations.** A configuration of the stack machine is a triple
$(pc, \sigma, s)$ of a program counter $pc \in \mathbb{N}$, a stack $\sigma$, which is a finite list
of natural numbers whose head is the top of the stack, and a state $s$ assigning a natural number
to each variable. -/
abbrev Config := Nat × List Nat × State

/-- **Step relation of the stack machine.** Let $P$ be a program, that is a list of instructions,
and write $a :: \sigma$ for the stack with top $a$ above the stack $\sigma$. A configuration
$(pc, \sigma, s)$ steps to a configuration $c'$ under $P$ exactly when $pc < |P|$ and, for the
instruction at position $pc$ of $P$ (counted from $0$), one of the following holds, where
$s[x \mapsto v]$ is the state $s$ with variable $x$ set to $v$.

- $\mathsf{push}\ n$: $c' = (pc + 1, n :: \sigma, s)$.
- $\mathsf{load}\ x$: $c' = (pc + 1, s(x) :: \sigma, s)$.
- $\mathsf{store}\ x$: $\sigma = v :: \tau$ and $c' = (pc + 1, \tau, s[x \mapsto v])$.
- $\mathsf{add}$, $\mathsf{sub}$, $\mathsf{mul}$: $\sigma = a :: b :: \tau$ and
  $c' = (pc + 1, r :: \tau, s)$, where $r$ is $b + a$, $\max(b - a, 0)$ or $b \cdot a$ respectively.
- $\mathsf{eq}$, $\mathsf{le}$: $\sigma = a :: b :: \tau$ and $c' = (pc + 1, r :: \tau, s)$,
  where $r$ is $1$ if $b = a$, respectively $b \le a$, and $r = 0$ otherwise.
- $\mathsf{not}$: $\sigma = a :: \tau$ and $c' = (pc + 1, r :: \tau, s)$, where $r = 1$ if $a = 0$
  and $r = 0$ otherwise.
- $\mathsf{and}$: $\sigma = a :: b :: \tau$ and $c' = (pc + 1, r :: \tau, s)$, where $r = 1$ if
  $b \ne 0$ and $a \ne 0$, and $r = 0$ otherwise.
- $\mathsf{jump}\ t$: $c' = (t, \sigma, s)$.
- $\mathsf{jumpIfZero}\ t$: either $\sigma = 0 :: \tau$ and $c' = (t, \tau, s)$, or
  $\sigma = (n + 1) :: \tau$ for some $n$ and $c' = (pc + 1, \tau, s)$.

For binary instructions the top of the stack $a$ is thus the right operand and the value below it
$b$ is the left operand. -/
inductive Step (prog : List Instr) : Config → Config → Prop
  | push {pc n : Nat} {stack : List Nat} {s : State}
      (hfetch : prog[pc]? = some (.push n)) :
      Step prog (pc, stack, s) (pc + 1, n :: stack, s)
  | load {pc x : Nat} {stack : List Nat} {s : State}
      (hfetch : prog[pc]? = some (.load x)) :
      Step prog (pc, stack, s) (pc + 1, s x :: stack, s)
  | store {pc x v : Nat} {stack : List Nat} {s : State}
      (hfetch : prog[pc]? = some (.store x)) :
      Step prog (pc, v :: stack, s) (pc + 1, stack, Function.update s x v)
  | add {pc a b : Nat} {stack : List Nat} {s : State}
      (hfetch : prog[pc]? = some .add) :
      Step prog (pc, a :: b :: stack, s) (pc + 1, (b + a) :: stack, s)
  | sub {pc a b : Nat} {stack : List Nat} {s : State}
      (hfetch : prog[pc]? = some .sub) :
      Step prog (pc, a :: b :: stack, s) (pc + 1, (b - a) :: stack, s)
  | mul {pc a b : Nat} {stack : List Nat} {s : State}
      (hfetch : prog[pc]? = some .mul) :
      Step prog (pc, a :: b :: stack, s) (pc + 1, (b * a) :: stack, s)
  | eqI {pc a b : Nat} {stack : List Nat} {s : State}
      (hfetch : prog[pc]? = some .eqI) :
      Step prog (pc, a :: b :: stack, s)
        (pc + 1, (if b = a then 1 else 0) :: stack, s)
  | leI {pc a b : Nat} {stack : List Nat} {s : State}
      (hfetch : prog[pc]? = some .leI) :
      Step prog (pc, a :: b :: stack, s)
        (pc + 1, (if b ≤ a then 1 else 0) :: stack, s)
  | notI {pc a : Nat} {stack : List Nat} {s : State}
      (hfetch : prog[pc]? = some .notI) :
      Step prog (pc, a :: stack, s)
        (pc + 1, (if a = 0 then 1 else 0) :: stack, s)
  | andI {pc a b : Nat} {stack : List Nat} {s : State}
      (hfetch : prog[pc]? = some .andI) :
      Step prog (pc, a :: b :: stack, s)
        (pc + 1, (if b ≠ 0 ∧ a ≠ 0 then 1 else 0) :: stack, s)
  | jump {pc target : Nat} {stack : List Nat} {s : State}
      (hfetch : prog[pc]? = some (.jump target)) :
      Step prog (pc, stack, s) (target, stack, s)
  | jumpIfZeroZero {pc target : Nat} {stack : List Nat} {s : State}
      (hfetch : prog[pc]? = some (.jumpIfZero target)) :
      Step prog (pc, 0 :: stack, s) (target, stack, s)
  | jumpIfZeroSucc {pc target n : Nat} {stack : List Nat} {s : State}
      (hfetch : prog[pc]? = some (.jumpIfZero target)) :
      Step prog (pc, (n + 1) :: stack, s) (pc + 1, stack, s)

/-- **Multi-step execution of the stack machine.** For a program $P$, the multi-step relation on
configurations is the reflexive transitive closure of the step relation of the stack machine
running $P$: it relates $c$ to $c'$ when $c'$ is obtained from $c$ by zero or more steps. -/
abbrev Steps (prog : List Instr) : Config → Config → Prop :=
  Relation.ReflTransGen (Step prog)

/-- **Determinism of the stack machine.** For every program $P$, the step relation of the stack
machine running $P$ is deterministic: if a configuration $x$ steps to $y$ and to $z$, then
$y = z$. The fetched instruction and the shape of the stack determine the next configuration. -/
theorem Step.deterministic {prog : List Instr} {x y z : Config}
    (h1 : Step prog x y) (h2 : Step prog x z) : y = z := by
  cases h1 <;> cases h2 <;> simp_all

/-- **No step past the end of the program.** Let $P$ be a program, that is a list of instructions,
and let $(pc, \sigma, s)$ be a configuration with $|P| \le pc$. Then the stack machine running $P$
has no step from $(pc, \sigma, s)$ to any configuration, since there is no instruction at
position $pc$ to fetch.

Hence the length of the code compiled from a command at base address $0$ is a halt address for
that code. -/
theorem no_step_of_length_le {prog : List Instr} {pc : Nat} {stack : List Nat}
    {s : State} (h : prog.length ≤ pc) (y : Config) :
    ¬ Step prog (pc, stack, s) y := by
  intro hstep
  have hnone : prog[pc]? = none := List.getElem?_eq_none_iff.mpr h
  cases hstep <;> simp_all

/-- **Instruction count of an arithmetic expression.** The instruction count $\ell(a)$ of an
arithmetic expression $a$ is defined by recursion on $a$: a constant or a variable has count $1$,
and if $a$ is the sum, difference or product of $a_1$ and $a_2$, then
$\ell(a) = \ell(a_1) + \ell(a_2) + 1$.

It is the number of stack-machine instructions generated when $a$ is compiled. -/
def alen : AExp → Nat
  | .const _ => 1
  | .var _ => 1
  | .add left right => alen left + alen right + 1
  | .sub left right => alen left + alen right + 1
  | .mul left right => alen left + alen right + 1

/-- **Instruction count of a Boolean expression.** The instruction count $\ell(b)$ of a Boolean
expression $b$ is defined by recursion on $b$, using the instruction count $\ell(a)$ of
arithmetic expressions $a$: a truth value has count $1$; the tests $a_1 = a_2$ and $a_1 \le a_2$
have count $\ell(a_1) + \ell(a_2) + 1$; the negation of $b_1$ has count $\ell(b_1) + 1$; and the
conjunction of $b_1$ and $b_2$ has count $\ell(b_1) + \ell(b_2) + 1$.

It is the number of stack-machine instructions generated when $b$ is compiled. -/
def blen : BExp → Nat
  | .truth _ => 1
  | .eq left right => alen left + alen right + 1
  | .le left right => alen left + alen right + 1
  | .not body => blen body + 1
  | .and left right => blen left + blen right + 1

/-- **Instruction count of a command.** The instruction count $\ell(c)$ of an IMP command $c$ is
defined by recursion on $c$, using the instruction counts $\ell(a)$ and $\ell(b)$ of arithmetic
and Boolean expressions: $\ell(\mathbf{skip}) = 0$; $\ell(x := a) = \ell(a) + 1$;
$\ell(c_1; c_2) = \ell(c_1) + \ell(c_2)$;
$\ell(\mathbf{if}\ b\ \mathbf{then}\ c_1\ \mathbf{else}\ c_2) =
\ell(b) + 1 + \ell(c_1) + 1 + \ell(c_2)$;
and $\ell(\mathbf{while}\ b\ \mathbf{do}\ c_1) = \ell(b) + 1 + \ell(c_1) + 1$.

It is the number of stack-machine instructions generated when $c$ is compiled. -/
def codeLength : Cmd → Nat
  | .skip => 0
  | .assign _ value => alen value + 1
  | .seq first second => codeLength first + codeLength second
  | .ite guard thenBranch elseBranch =>
      blen guard + 1 + codeLength thenBranch + 1 + codeLength elseBranch
  | .while guard body => blen guard + 1 + codeLength body + 1

/-- **Compilation of arithmetic expressions.** The compiled code of an arithmetic expression is
the list of stack-machine instructions defined by recursion: a constant $n$ compiles to the
single instruction push $n$, a variable $x$ to the single instruction load $x$, and the sum,
difference or product of $a_1$ and $a_2$ to the code of $a_1$, then the code of $a_2$, then the
single instruction add, sub or mul respectively.

Running this code leaves the value of the expression on top of the stack. -/
def compileA : AExp → List Instr
  | .const value => [.push value]
  | .var name => [.load name]
  | .add left right => compileA left ++ compileA right ++ [.add]
  | .sub left right => compileA left ++ compileA right ++ [.sub]
  | .mul left right => compileA left ++ compileA right ++ [.mul]

/-- **Compilation of Boolean expressions.** The compiled code of a Boolean expression is the list
of stack-machine instructions defined by recursion, using the compiled code of arithmetic
expressions: the truth value true compiles to the single instruction push $1$ and false to push
$0$; the test $a_1 = a_2$ (respectively $a_1 \le a_2$) compiles to the code of $a_1$, then the
code of $a_2$, then the equality (respectively order) test instruction; the negation of $b_1$
compiles to the code of $b_1$ followed by the negation instruction; and the conjunction of $b_1$
and $b_2$ compiles to the code of $b_1$, then the code of $b_2$, then the conjunction instruction.

Running this code leaves $1$ (true) or $0$ (false) on top of the stack. -/
def compileB : BExp → List Instr
  | .truth value => [.push (cond value 1 0)]
  | .eq left right => compileA left ++ compileA right ++ [.eqI]
  | .le left right => compileA left ++ compileA right ++ [.leI]
  | .not body => compileB body ++ [.notI]
  | .and left right => compileB left ++ compileB right ++ [.andI]

/-- **Compilation of commands.** The compiled code $C_p(c)$ of an IMP command $c$ at base program
counter $p$ is the list of stack-machine instructions defined by recursion on $c$, where jump
targets are absolute program counters and $\ell$ denotes instruction counts:
$C_p(\mathbf{skip})$ is empty; $C_p(x := a)$ is the code of $a$ followed by the instruction
store $x$; $C_p(c_1; c_2)$ is $C_p(c_1)$ followed by $C_{p + \ell(c_1)}(c_2)$. For the
conditional $\mathbf{if}\ b\ \mathbf{then}\ c_1\ \mathbf{else}\ c_2$, put $q = p + \ell(b) + 1$
and $r = q + \ell(c_1) + 1$; its code is the code of $b$, then jump-if-zero to $r$, then
$C_q(c_1)$, then jump to $r + \ell(c_2)$, then $C_r(c_2)$. For the loop
$\mathbf{while}\ b\ \mathbf{do}\ c_1$, put $q = p + \ell(b) + 1$; its code is the code of $b$,
then jump-if-zero to $q + \ell(c_1) + 1$, then $C_q(c_1)$, then jump to $p$. -/
def compile : Cmd → Nat → List Instr
  | .skip, _ => []
  | .assign name value, _ => compileA value ++ [.store name]
  | .seq first second, pc =>
      compile first pc ++ compile second (pc + codeLength first)
  | .ite guard thenBranch elseBranch, pc =>
      compileB guard ++
        [.jumpIfZero (pc + blen guard + 1 + codeLength thenBranch + 1)] ++
        compile thenBranch (pc + blen guard + 1) ++
        [.jump (pc + blen guard + 1 + codeLength thenBranch + 1 +
          codeLength elseBranch)] ++
        compile elseBranch (pc + blen guard + 1 + codeLength thenBranch + 1)
  | .while guard body, pc =>
      compileB guard ++
        [.jumpIfZero (pc + blen guard + 1 + codeLength body + 1)] ++
        compile body (pc + blen guard + 1) ++ [.jump pc]

theorem compileA_length (a : AExp) : (compileA a).length = alen a := by
  induction a <;> simp_all [compileA, alen, List.length_append] <;> omega

theorem compileB_length (b : BExp) : (compileB b).length = blen b := by
  induction b <;> simp_all [compileB, blen, List.length_append, compileA_length] <;>
    omega

theorem compile_length (c : Cmd) (pc : Nat) :
    (compile c pc).length = codeLength c := by
  induction c generalizing pc with
  | skip => rfl
  | assign name value =>
      simp [compile, codeLength, List.length_append, compileA_length]
  | seq first second ihFirst ihSecond =>
      simp [compile, codeLength, List.length_append, ihFirst, ihSecond]
  | ite guard thenBranch elseBranch ihThen ihElse =>
      simp [compile, codeLength, List.length_append, compileB_length, ihThen,
        ihElse]
      omega
  | «while» guard body ihBody =>
      simp [compile, codeLength, List.length_append, compileB_length, ihBody]
      omega

/-- **Fetching from an embedded code segment.** Let $B$, $S$ and $A$ be lists of instructions and
let $i < |S|$ be a natural number. Then the instruction at position $|B| + i$ of the concatenation
$B\,S\,A$ of the three lists equals the instruction at position $i$ of $S$, positions being
counted from $0$. -/
theorem fetch_segment {before seg after : List Instr} {i : Nat}
    (hi : i < seg.length) :
    (before ++ seg ++ after)[before.length + i]? = seg[i]? := by
  have h1 : before.length + i < (before ++ seg).length := by
    rw [List.length_append]
    exact Nat.add_lt_add_left hi _
  rw [List.getElem?_append_left h1,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-- Fetch the first instruction after a prefix `X` in `X ++ (op :: Y)`. -/
private theorem fetch_cons {X : List Instr} {op : Instr} {Y : List Instr}
    {k : Nat} (hk : X.length = k) : (X ++ (op :: Y))[k]? = some op := by
  rw [← hk, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

/-- Fetch the first instruction after prefixes `X` and `Y` in
`X ++ (Y ++ (op :: Z))`. -/
private theorem fetch_append_cons {X Y : List Instr} {op : Instr}
    {Z : List Instr} {k : Nat} (hk : X.length + Y.length = k) :
    (X ++ (Y ++ (op :: Z)))[k]? = some op := by
  rw [← hk, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left]
  exact fetch_cons rfl

private theorem compile_assign_fetch {x : Nat} {a : AExp} {pc : Nat} :
    (compile (.assign x a) pc)[alen a]? = some (.store x) := by
  simp only [compile]
  exact fetch_cons (compileA_length a)

private theorem compile_ite_fetch_jiz {b : BExp} {t e : Cmd} {pc : Nat} :
    (compile (.ite b t e) pc)[blen b]? =
      some (.jumpIfZero (pc + blen b + 1 + codeLength t + 1)) := by
  simp only [compile, List.append_assoc]
  exact fetch_cons (compileB_length b)

private theorem compile_ite_fetch_jump {b : BExp} {t e : Cmd} {pc : Nat} :
    (compile (.ite b t e) pc)[blen b + 1 + codeLength t]? =
      some (.jump (pc + blen b + 1 + codeLength t + 1 + codeLength e)) := by
  simp only [compile, List.append_assoc]
  have hk : (compileB b).length +
        ([Instr.jumpIfZero (pc + blen b + 1 + codeLength t + 1)] ++
          compile t (pc + blen b + 1)).length =
      blen b + 1 + codeLength t := by
    simp only [List.length_append, compileB_length, compile_length,
      List.length_cons, List.length_nil]
    omega
  exact fetch_append_cons hk

private theorem compile_while_fetch_jiz {b : BExp} {c : Cmd} {pc : Nat} :
    (compile (.while b c) pc)[blen b]? =
      some (.jumpIfZero (pc + blen b + 1 + codeLength c + 1)) := by
  simp only [compile, List.append_assoc]
  exact fetch_cons (compileB_length b)

private theorem compile_while_fetch_jump {b : BExp} {c : Cmd} {pc : Nat} :
    (compile (.while b c) pc)[blen b + 1 + codeLength c]? =
      some (.jump pc) := by
  simp only [compile, List.append_assoc]
  have hk : (compileB b).length +
        ([Instr.jumpIfZero (pc + blen b + 1 + codeLength c + 1)] ++
          compile c (pc + blen b + 1)).length =
      blen b + 1 + codeLength c := by
    simp only [List.length_append, compileB_length, compile_length,
      List.length_cons, List.length_nil]
    omega
  exact fetch_append_cons hk

/-- **Compiled arithmetic code pushes the value of the expression.** Let $a$ be an arithmetic
expression with compiled code $C(a)$ and instruction count $\ell(a)$, let $P$ and $Q$ be lists of
instructions, $\sigma$ a stack and $s$ a state, and write $|P|$ for the length of $P$. The stack
machine running the program $P \, C(a) \, Q$ (the concatenation of $P$, $C(a)$ and $Q$) goes in
finitely many steps from program counter $|P|$, stack $\sigma$ and state $s$ to program counter
$|P| + \ell(a)$, the stack obtained from $\sigma$ by pushing the value of $a$ in $s$, and the
same state $s$. -/
theorem compileA_runs {a : AExp} {before after : List Instr} {stack : List Nat}
    {s : State} :
    Steps (before ++ compileA a ++ after) (before.length, stack, s)
      (before.length + alen a, a.eval s :: stack, s) := by
  induction a generalizing before after stack with
  | const n =>
      have hfetch : (before ++ compileA (.const n) ++ after)[before.length]? =
          some (.push n) := by
        simp [compileA]
      have hstep : Step (before ++ compileA (.const n) ++ after)
          (before.length, stack, s) (before.length + 1, n :: stack, s) :=
        Step.push hfetch
      simpa [alen] using Relation.ReflTransGen.single hstep
  | var x =>
      have hfetch : (before ++ compileA (.var x) ++ after)[before.length]? =
          some (.load x) := by
        simp [compileA]
      have hstep : Step (before ++ compileA (.var x) ++ after)
          (before.length, stack, s) (before.length + 1, s x :: stack, s) :=
        Step.load hfetch
      simpa [alen] using Relation.ReflTransGen.single hstep
  | add l r ihl ihr =>
      have hL : Steps (before ++ compileA (.add l r) ++ after)
          (before.length, stack, s)
          (before.length + alen l, l.eval s :: stack, s) := by
        simpa only [compileA, List.append_assoc] using
          ihl (before := before) (after := compileA r ++ [Instr.add] ++ after)
            (stack := stack)
      have hlenL : (before ++ compileA l).length = before.length + alen l := by
        simp [List.length_append, compileA_length]
      have hR : Steps (before ++ compileA (.add l r) ++ after)
          (before.length + alen l, l.eval s :: stack, s)
          (before.length + alen l + alen r, r.eval s :: l.eval s :: stack, s) := by
        simpa only [compileA, List.append_assoc, hlenL] using
          ihr (before := before ++ compileA l) (after := [Instr.add] ++ after)
            (stack := l.eval s :: stack)
      have hklen : (compileA l).length + (compileA r).length =
          alen l + alen r := by
        rw [compileA_length, compileA_length]
      have hseg : (compileA (.add l r))[alen l + alen r]? = some Instr.add := by
        simp only [compileA, List.append_assoc]
        exact fetch_append_cons hklen
      have hk : alen l + alen r < (compileA (.add l r)).length := by
        rw [compileA_length]
        simp only [alen]
        omega
      have hfetch := fetch_segment (before := before)
        (seg := compileA (.add l r)) (after := after) hk
      rw [hseg, show before.length + (alen l + alen r) =
          before.length + alen l + alen r from by omega] at hfetch
      have hstep : Step (before ++ compileA (.add l r) ++ after)
          (before.length + alen l + alen r, r.eval s :: l.eval s :: stack, s)
          (before.length + alen l + alen r + 1, (l.eval s + r.eval s) :: stack,
            s) :=
        Step.add hfetch
      rw [show before.length + alen (.add l r) =
          before.length + alen l + alen r + 1 from by simp only [alen]; omega,
        AExp.eval_add]
      exact (hL.trans hR).trans (Relation.ReflTransGen.single hstep)
  | sub l r ihl ihr =>
      have hL : Steps (before ++ compileA (.sub l r) ++ after)
          (before.length, stack, s)
          (before.length + alen l, l.eval s :: stack, s) := by
        simpa only [compileA, List.append_assoc] using
          ihl (before := before) (after := compileA r ++ [Instr.sub] ++ after)
            (stack := stack)
      have hlenL : (before ++ compileA l).length = before.length + alen l := by
        simp [List.length_append, compileA_length]
      have hR : Steps (before ++ compileA (.sub l r) ++ after)
          (before.length + alen l, l.eval s :: stack, s)
          (before.length + alen l + alen r, r.eval s :: l.eval s :: stack, s) := by
        simpa only [compileA, List.append_assoc, hlenL] using
          ihr (before := before ++ compileA l) (after := [Instr.sub] ++ after)
            (stack := l.eval s :: stack)
      have hklen : (compileA l).length + (compileA r).length =
          alen l + alen r := by
        rw [compileA_length, compileA_length]
      have hseg : (compileA (.sub l r))[alen l + alen r]? = some Instr.sub := by
        simp only [compileA, List.append_assoc]
        exact fetch_append_cons hklen
      have hk : alen l + alen r < (compileA (.sub l r)).length := by
        rw [compileA_length]
        simp only [alen]
        omega
      have hfetch := fetch_segment (before := before)
        (seg := compileA (.sub l r)) (after := after) hk
      rw [hseg, show before.length + (alen l + alen r) =
          before.length + alen l + alen r from by omega] at hfetch
      have hstep : Step (before ++ compileA (.sub l r) ++ after)
          (before.length + alen l + alen r, r.eval s :: l.eval s :: stack, s)
          (before.length + alen l + alen r + 1, (l.eval s - r.eval s) :: stack,
            s) :=
        Step.sub hfetch
      rw [show before.length + alen (.sub l r) =
          before.length + alen l + alen r + 1 from by simp only [alen]; omega,
        AExp.eval_sub]
      exact (hL.trans hR).trans (Relation.ReflTransGen.single hstep)
  | mul l r ihl ihr =>
      have hL : Steps (before ++ compileA (.mul l r) ++ after)
          (before.length, stack, s)
          (before.length + alen l, l.eval s :: stack, s) := by
        simpa only [compileA, List.append_assoc] using
          ihl (before := before) (after := compileA r ++ [Instr.mul] ++ after)
            (stack := stack)
      have hlenL : (before ++ compileA l).length = before.length + alen l := by
        simp [List.length_append, compileA_length]
      have hR : Steps (before ++ compileA (.mul l r) ++ after)
          (before.length + alen l, l.eval s :: stack, s)
          (before.length + alen l + alen r, r.eval s :: l.eval s :: stack, s) := by
        simpa only [compileA, List.append_assoc, hlenL] using
          ihr (before := before ++ compileA l) (after := [Instr.mul] ++ after)
            (stack := l.eval s :: stack)
      have hklen : (compileA l).length + (compileA r).length =
          alen l + alen r := by
        rw [compileA_length, compileA_length]
      have hseg : (compileA (.mul l r))[alen l + alen r]? = some Instr.mul := by
        simp only [compileA, List.append_assoc]
        exact fetch_append_cons hklen
      have hk : alen l + alen r < (compileA (.mul l r)).length := by
        rw [compileA_length]
        simp only [alen]
        omega
      have hfetch := fetch_segment (before := before)
        (seg := compileA (.mul l r)) (after := after) hk
      rw [hseg, show before.length + (alen l + alen r) =
          before.length + alen l + alen r from by omega] at hfetch
      have hstep : Step (before ++ compileA (.mul l r) ++ after)
          (before.length + alen l + alen r, r.eval s :: l.eval s :: stack, s)
          (before.length + alen l + alen r + 1, (l.eval s * r.eval s) :: stack,
            s) :=
        Step.mul hfetch
      rw [show before.length + alen (.mul l r) =
          before.length + alen l + alen r + 1 from by simp only [alen]; omega,
        AExp.eval_mul]
      exact (hL.trans hR).trans (Relation.ReflTransGen.single hstep)

private theorem cond_eval_eq {l r : AExp} {s : State} :
    cond ((BExp.eq l r).eval s) 1 0 =
      (if l.eval s = r.eval s then 1 else 0) := by
  by_cases h : l.eval s = r.eval s <;> simp [BExp.eval, h]

private theorem cond_eval_le {l r : AExp} {s : State} :
    cond ((BExp.le l r).eval s) 1 0 =
      (if l.eval s ≤ r.eval s then 1 else 0) := by
  by_cases h : l.eval s ≤ r.eval s <;> simp [BExp.eval, h]

private theorem cond_eval_not {b : BExp} {s : State} :
    cond ((BExp.not b).eval s) 1 0 =
      (if cond (b.eval s) 1 0 = 0 then 1 else 0) := by
  cases hb : b.eval s <;> simp [BExp.eval, hb]

private theorem cond_eval_and {l r : BExp} {s : State} :
    cond ((BExp.and l r).eval s) 1 0 =
      (if cond (l.eval s) 1 0 ≠ 0 ∧ cond (r.eval s) 1 0 ≠ 0 then 1 else 0) := by
  cases hl : l.eval s <;> cases hr : r.eval s <;> simp [BExp.eval, hl, hr]

/-- **Compiled Boolean code pushes the truth value of the expression.** Let $b$ be a Boolean
expression with compiled code $C(b)$ and instruction count $\ell(b)$, let $P$ and $Q$ be lists of
instructions, $\sigma$ a stack and $s$ a state, and write $|P|$ for the length of $P$. The stack
machine running the program $P \, C(b) \, Q$ (the concatenation of $P$, $C(b)$ and $Q$) goes in
finitely many steps from program counter $|P|$, stack $\sigma$ and state $s$ to program counter
$|P| + \ell(b)$, the stack obtained from $\sigma$ by pushing $1$ if $b$ evaluates to true in $s$
and $0$ otherwise, and the same state $s$. -/
theorem compileB_runs {b : BExp} {before after : List Instr} {stack : List Nat}
    {s : State} :
    Steps (before ++ compileB b ++ after) (before.length, stack, s)
      (before.length + blen b, cond (b.eval s) 1 0 :: stack, s) := by
  induction b generalizing before after stack with
  | truth v =>
      have hfetch : (before ++ compileB (.truth v) ++ after)[before.length]? =
          some (.push (cond v 1 0)) := by
        simp [compileB]
      have hstep : Step (before ++ compileB (.truth v) ++ after)
          (before.length, stack, s)
          (before.length + 1, cond v 1 0 :: stack, s) :=
        Step.push hfetch
      simpa [blen] using Relation.ReflTransGen.single hstep
  | eq l r =>
      have hL : Steps (before ++ compileB (.eq l r) ++ after)
          (before.length, stack, s)
          (before.length + alen l, l.eval s :: stack, s) := by
        simpa only [compileB, List.append_assoc] using
          compileA_runs (a := l) (before := before)
            (after := compileA r ++ [Instr.eqI] ++ after) (stack := stack)
            (s := s)
      have hlenL : (before ++ compileA l).length = before.length + alen l := by
        simp [List.length_append, compileA_length]
      have hR : Steps (before ++ compileB (.eq l r) ++ after)
          (before.length + alen l, l.eval s :: stack, s)
          (before.length + alen l + alen r, r.eval s :: l.eval s :: stack, s) := by
        simpa only [compileB, List.append_assoc, hlenL] using
          compileA_runs (a := r) (before := before ++ compileA l)
            (after := [Instr.eqI] ++ after) (stack := l.eval s :: stack) (s := s)
      have hklen : (compileA l).length + (compileA r).length =
          alen l + alen r := by
        rw [compileA_length, compileA_length]
      have hseg : (compileB (.eq l r))[alen l + alen r]? = some Instr.eqI := by
        simp only [compileB, List.append_assoc]
        exact fetch_append_cons hklen
      have hk : alen l + alen r < (compileB (.eq l r)).length := by
        rw [compileB_length]
        simp only [blen]
        omega
      have hfetch := fetch_segment (before := before)
        (seg := compileB (.eq l r)) (after := after) hk
      rw [hseg, show before.length + (alen l + alen r) =
          before.length + alen l + alen r from by omega] at hfetch
      have hstep : Step (before ++ compileB (.eq l r) ++ after)
          (before.length + alen l + alen r, r.eval s :: l.eval s :: stack, s)
          (before.length + alen l + alen r + 1,
            (if l.eval s = r.eval s then 1 else 0) :: stack, s) :=
        Step.eqI hfetch
      rw [show before.length + blen (.eq l r) =
          before.length + alen l + alen r + 1 from by simp only [blen]; omega,
        cond_eval_eq]
      exact (hL.trans hR).trans (Relation.ReflTransGen.single hstep)
  | le l r =>
      have hL : Steps (before ++ compileB (.le l r) ++ after)
          (before.length, stack, s)
          (before.length + alen l, l.eval s :: stack, s) := by
        simpa only [compileB, List.append_assoc] using
          compileA_runs (a := l) (before := before)
            (after := compileA r ++ [Instr.leI] ++ after) (stack := stack)
            (s := s)
      have hlenL : (before ++ compileA l).length = before.length + alen l := by
        simp [List.length_append, compileA_length]
      have hR : Steps (before ++ compileB (.le l r) ++ after)
          (before.length + alen l, l.eval s :: stack, s)
          (before.length + alen l + alen r, r.eval s :: l.eval s :: stack, s) := by
        simpa only [compileB, List.append_assoc, hlenL] using
          compileA_runs (a := r) (before := before ++ compileA l)
            (after := [Instr.leI] ++ after) (stack := l.eval s :: stack) (s := s)
      have hklen : (compileA l).length + (compileA r).length =
          alen l + alen r := by
        rw [compileA_length, compileA_length]
      have hseg : (compileB (.le l r))[alen l + alen r]? = some Instr.leI := by
        simp only [compileB, List.append_assoc]
        exact fetch_append_cons hklen
      have hk : alen l + alen r < (compileB (.le l r)).length := by
        rw [compileB_length]
        simp only [blen]
        omega
      have hfetch := fetch_segment (before := before)
        (seg := compileB (.le l r)) (after := after) hk
      rw [hseg, show before.length + (alen l + alen r) =
          before.length + alen l + alen r from by omega] at hfetch
      have hstep : Step (before ++ compileB (.le l r) ++ after)
          (before.length + alen l + alen r, r.eval s :: l.eval s :: stack, s)
          (before.length + alen l + alen r + 1,
            (if l.eval s ≤ r.eval s then 1 else 0) :: stack, s) :=
        Step.leI hfetch
      rw [show before.length + blen (.le l r) =
          before.length + alen l + alen r + 1 from by simp only [blen]; omega,
        cond_eval_le]
      exact (hL.trans hR).trans (Relation.ReflTransGen.single hstep)
  | not b ih =>
      have hB : Steps (before ++ compileB (.not b) ++ after)
          (before.length, stack, s)
          (before.length + blen b, cond (b.eval s) 1 0 :: stack, s) := by
        simpa only [compileB, List.append_assoc] using
          ih (before := before) (after := [Instr.notI] ++ after) (stack := stack)
      have hseg : (compileB (.not b))[blen b]? = some Instr.notI := by
        simp only [compileB]
        exact fetch_cons (compileB_length b)
      have hk : blen b < (compileB (.not b)).length := by
        rw [compileB_length]
        simp only [blen]
        omega
      have hfetch := fetch_segment (before := before)
        (seg := compileB (.not b)) (after := after) hk
      rw [hseg] at hfetch
      have hstep : Step (before ++ compileB (.not b) ++ after)
          (before.length + blen b, cond (b.eval s) 1 0 :: stack, s)
          (before.length + blen b + 1,
            (if cond (b.eval s) 1 0 = 0 then 1 else 0) :: stack, s) :=
        Step.notI hfetch
      rw [show before.length + blen (.not b) = before.length + blen b + 1 from by
          simp only [blen]; omega, cond_eval_not]
      exact hB.trans (Relation.ReflTransGen.single hstep)
  | and l r ihl ihr =>
      have hL : Steps (before ++ compileB (.and l r) ++ after)
          (before.length, stack, s)
          (before.length + blen l, cond (l.eval s) 1 0 :: stack, s) := by
        simpa only [compileB, List.append_assoc] using
          ihl (before := before) (after := compileB r ++ [Instr.andI] ++ after)
            (stack := stack)
      have hlenL : (before ++ compileB l).length = before.length + blen l := by
        simp [List.length_append, compileB_length]
      have hR : Steps (before ++ compileB (.and l r) ++ after)
          (before.length + blen l, cond (l.eval s) 1 0 :: stack, s)
          (before.length + blen l + blen r,
            cond (r.eval s) 1 0 :: cond (l.eval s) 1 0 :: stack, s) := by
        simpa only [compileB, List.append_assoc, hlenL] using
          ihr (before := before ++ compileB l) (after := [Instr.andI] ++ after)
            (stack := cond (l.eval s) 1 0 :: stack)
      have hklen : (compileB l).length + (compileB r).length =
          blen l + blen r := by
        rw [compileB_length, compileB_length]
      have hseg : (compileB (.and l r))[blen l + blen r]? = some Instr.andI := by
        simp only [compileB, List.append_assoc]
        exact fetch_append_cons hklen
      have hk : blen l + blen r < (compileB (.and l r)).length := by
        rw [compileB_length]
        simp only [blen]
        omega
      have hfetch := fetch_segment (before := before)
        (seg := compileB (.and l r)) (after := after) hk
      rw [hseg, show before.length + (blen l + blen r) =
          before.length + blen l + blen r from by omega] at hfetch
      have hstep : Step (before ++ compileB (.and l r) ++ after)
          (before.length + blen l + blen r,
            cond (r.eval s) 1 0 :: cond (l.eval s) 1 0 :: stack, s)
          (before.length + blen l + blen r + 1,
            (if cond (l.eval s) 1 0 ≠ 0 ∧ cond (r.eval s) 1 0 ≠ 0 then 1
              else 0) :: stack, s) :=
        Step.andI hfetch
      rw [show before.length + blen (.and l r) =
          before.length + blen l + blen r + 1 from by simp only [blen]; omega,
        cond_eval_and]
      exact (hL.trans hR).trans (Relation.ReflTransGen.single hstep)

/-- **Compiled command code simulates big-step execution.** Let $c$ be a command and $s$, $s'$
states such that $c$ run from $s$ terminates in $s'$ under the big-step semantics. Let $P$ and
$Q$ be lists of instructions, $\sigma$ a stack, $|P|$ the length of $P$, $C_p(c)$ the compiled
code of $c$ at base program counter $p$, and $\ell(c)$ the instruction count of $c$. Then the
stack machine running the program $P \, C_{|P|}(c) \, Q$ (the concatenation of $P$,
$C_{|P|}(c)$ and $Q$) goes in finitely many steps from program counter $|P|$, stack $\sigma$ and
state $s$ to program counter $|P| + \ell(c)$, the same stack $\sigma$ and state $s'$. -/
theorem compile_runs {c : Cmd} {s s' : State} (h : BigStep c s s')
    {before after : List Instr} {stack : List Nat} :
    Steps (before ++ compile c before.length ++ after) (before.length, stack, s)
      (before.length + codeLength c, stack, s') := by
  induction h generalizing before after stack with
  | skip state =>
      exact Relation.ReflTransGen.refl
  | assign state name value =>
      have hA : Steps (before ++ compile (.assign name value) before.length ++ after)
          (before.length, stack, state)
          (before.length + alen value, value.eval state :: stack, state) := by
        simpa only [compile, List.append_assoc] using
          compileA_runs (a := value) (before := before)
            (after := [Instr.store name] ++ after) (stack := stack) (s := state)
      have hk : alen value <
          (compile (.assign name value) before.length).length := by
        rw [compile_length]
        simp only [codeLength]
        omega
      have hfetch := fetch_segment (before := before)
        (seg := compile (.assign name value) before.length) (after := after) hk
      rw [compile_assign_fetch] at hfetch
      have hstep : Step (before ++ compile (.assign name value) before.length ++
            after)
          (before.length + alen value, value.eval state :: stack, state)
          (before.length + alen value + 1, stack,
            Function.update state name (value.eval state)) :=
        Step.store hfetch
      rw [show before.length + codeLength (.assign name value) =
          before.length + alen value + 1 from by simp only [codeLength]; omega]
      exact hA.trans (Relation.ReflTransGen.single hstep)
  | seq firstStep secondStep ihFirst ihSecond =>
      rename_i first second initial middle final
      have h1 : Steps (before ++ compile (.seq first second) before.length ++ after)
          (before.length, stack, initial)
          (before.length + codeLength first, stack, middle) := by
        simpa only [compile, List.append_assoc] using
          ihFirst (before := before)
            (after := compile second (before.length + codeLength first) ++ after)
            (stack := stack)
      have hlen1 : (before ++ compile first before.length).length =
          before.length + codeLength first := by
        simp only [List.length_append, compile_length]
      have h2 : Steps (before ++ compile (.seq first second) before.length ++ after)
          (before.length + codeLength first, stack, middle)
          (before.length + codeLength first + codeLength second, stack, final) := by
        simpa only [compile, List.append_assoc, hlen1] using
          ihSecond (before := before ++ compile first before.length)
            (after := after) (stack := stack)
      rw [show before.length + codeLength (.seq first second) =
          before.length + codeLength first + codeLength second from by
          simp only [codeLength]; omega]
      exact h1.trans h2
  | iteTrue guardTrue branchStep ih =>
      rename_i b t e initial final
      have hB : Steps (before ++ compile (.ite b t e) before.length ++ after)
          (before.length, stack, initial)
          (before.length + blen b, cond (b.eval initial) 1 0 :: stack, initial) := by
        simpa only [compile, List.append_assoc] using
          compileB_runs (b := b) (before := before)
            (after := [Instr.jumpIfZero
                (before.length + blen b + 1 + codeLength t + 1)] ++
              compile t (before.length + blen b + 1) ++
              [Instr.jump
                (before.length + blen b + 1 + codeLength t + 1 + codeLength e)] ++
              compile e (before.length + blen b + 1 + codeLength t + 1) ++ after)
            (stack := stack) (s := initial)
      rw [guardTrue] at hB
      have hkB : blen b < (compile (.ite b t e) before.length).length := by
        rw [compile_length]
        simp only [codeLength]
        omega
      have hfetchB := fetch_segment (before := before)
        (seg := compile (.ite b t e) before.length) (after := after) hkB
      rw [compile_ite_fetch_jiz] at hfetchB
      have hstepB : Step (before ++ compile (.ite b t e) before.length ++ after)
          (before.length + blen b, 1 :: stack, initial)
          (before.length + blen b + 1, stack, initial) :=
        Step.jumpIfZeroSucc hfetchB
      have hlenT : (before ++ compileB b ++
            [Instr.jumpIfZero (before.length + blen b + 1 + codeLength t + 1)]).length =
          before.length + blen b + 1 := by
        simp only [List.length_append, compileB_length, List.length_cons,
          List.length_nil]
      have hTraw := ih (before := before ++ compileB b ++
          [Instr.jumpIfZero (before.length + blen b + 1 + codeLength t + 1)])
        (after := [Instr.jump
            (before.length + blen b + 1 + codeLength t + 1 + codeLength e)] ++
          compile e (before.length + blen b + 1 + codeLength t + 1) ++ after)
        (stack := stack)
      rw [hlenT] at hTraw
      have hT : Steps (before ++ compile (.ite b t e) before.length ++ after)
          (before.length + blen b + 1, stack, initial)
          (before.length + blen b + 1 + codeLength t, stack, final) := by
        simpa only [compile, List.append_assoc] using hTraw
      have hkJ : blen b + 1 + codeLength t <
          (compile (.ite b t e) before.length).length := by
        rw [compile_length]
        simp only [codeLength]
        omega
      have hfetchJ := fetch_segment (before := before)
        (seg := compile (.ite b t e) before.length) (after := after) hkJ
      rw [compile_ite_fetch_jump, show before.length + (blen b + 1 + codeLength t) =
          before.length + blen b + 1 + codeLength t from by omega] at hfetchJ
      have hstepJ : Step (before ++ compile (.ite b t e) before.length ++ after)
          (before.length + blen b + 1 + codeLength t, stack, final)
          (before.length + blen b + 1 + codeLength t + 1 + codeLength e, stack,
            final) :=
        Step.jump hfetchJ
      rw [show before.length + codeLength (.ite b t e) =
          before.length + blen b + 1 + codeLength t + 1 + codeLength e from by
          simp only [codeLength]; omega]
      exact ((hB.trans (Relation.ReflTransGen.single hstepB)).trans hT).trans
        (Relation.ReflTransGen.single hstepJ)
  | iteFalse guardFalse branchStep ih =>
      rename_i b t e initial final
      have hB : Steps (before ++ compile (.ite b t e) before.length ++ after)
          (before.length, stack, initial)
          (before.length + blen b, cond (b.eval initial) 1 0 :: stack, initial) := by
        simpa only [compile, List.append_assoc] using
          compileB_runs (b := b) (before := before)
            (after := [Instr.jumpIfZero
                (before.length + blen b + 1 + codeLength t + 1)] ++
              compile t (before.length + blen b + 1) ++
              [Instr.jump
                (before.length + blen b + 1 + codeLength t + 1 + codeLength e)] ++
              compile e (before.length + blen b + 1 + codeLength t + 1) ++ after)
            (stack := stack) (s := initial)
      rw [guardFalse] at hB
      have hkB : blen b < (compile (.ite b t e) before.length).length := by
        rw [compile_length]
        simp only [codeLength]
        omega
      have hfetchB := fetch_segment (before := before)
        (seg := compile (.ite b t e) before.length) (after := after) hkB
      rw [compile_ite_fetch_jiz] at hfetchB
      have hstepB : Step (before ++ compile (.ite b t e) before.length ++ after)
          (before.length + blen b, 0 :: stack, initial)
          (before.length + blen b + 1 + codeLength t + 1, stack, initial) :=
        Step.jumpIfZeroZero hfetchB
      have hlenE : (before ++ compileB b ++
            [Instr.jumpIfZero (before.length + blen b + 1 + codeLength t + 1)] ++
            compile t (before.length + blen b + 1) ++
            [Instr.jump
              (before.length + blen b + 1 + codeLength t + 1 + codeLength e)]).length =
          before.length + blen b + 1 + codeLength t + 1 := by
        simp only [List.length_append, compileB_length, compile_length,
          List.length_cons, List.length_nil]
      have hEraw := ih (before := before ++ compileB b ++
          [Instr.jumpIfZero (before.length + blen b + 1 + codeLength t + 1)] ++
          compile t (before.length + blen b + 1) ++
          [Instr.jump
            (before.length + blen b + 1 + codeLength t + 1 + codeLength e)])
        (after := after) (stack := stack)
      rw [hlenE] at hEraw
      have hE : Steps (before ++ compile (.ite b t e) before.length ++ after)
          (before.length + blen b + 1 + codeLength t + 1, stack, initial)
          (before.length + blen b + 1 + codeLength t + 1 + codeLength e, stack,
            final) := by
        simpa only [compile, List.append_assoc] using hEraw
      rw [show before.length + codeLength (.ite b t e) =
          before.length + blen b + 1 + codeLength t + 1 + codeLength e from by
          simp only [codeLength]; omega]
      exact (hB.trans (Relation.ReflTransGen.single hstepB)).trans hE
  | whileFalse guardFalse =>
      rename_i b c state
      have hB : Steps (before ++ compile (.while b c) before.length ++ after)
          (before.length, stack, state)
          (before.length + blen b, cond (b.eval state) 1 0 :: stack, state) := by
        simpa only [compile, List.append_assoc] using
          compileB_runs (b := b) (before := before)
            (after := [Instr.jumpIfZero
                (before.length + blen b + 1 + codeLength c + 1)] ++
              compile c (before.length + blen b + 1) ++
              [Instr.jump before.length] ++ after)
            (stack := stack) (s := state)
      rw [guardFalse] at hB
      have hkB : blen b < (compile (.while b c) before.length).length := by
        rw [compile_length]
        simp only [codeLength]
        omega
      have hfetchB := fetch_segment (before := before)
        (seg := compile (.while b c) before.length) (after := after) hkB
      rw [compile_while_fetch_jiz] at hfetchB
      have hstepB : Step (before ++ compile (.while b c) before.length ++ after)
          (before.length + blen b, 0 :: stack, state)
          (before.length + blen b + 1 + codeLength c + 1, stack, state) :=
        Step.jumpIfZeroZero hfetchB
      rw [show before.length + codeLength (.while b c) =
          before.length + blen b + 1 + codeLength c + 1 from by
          simp only [codeLength]; omega]
      exact hB.trans (Relation.ReflTransGen.single hstepB)
  | whileTrue guardTrue bodyStep loopStep ihBody ihLoop =>
      rename_i b c initial middle final
      have hB : Steps (before ++ compile (.while b c) before.length ++ after)
          (before.length, stack, initial)
          (before.length + blen b, cond (b.eval initial) 1 0 :: stack, initial) := by
        simpa only [compile, List.append_assoc] using
          compileB_runs (b := b) (before := before)
            (after := [Instr.jumpIfZero
                (before.length + blen b + 1 + codeLength c + 1)] ++
              compile c (before.length + blen b + 1) ++
              [Instr.jump before.length] ++ after)
            (stack := stack) (s := initial)
      rw [guardTrue] at hB
      have hkB : blen b < (compile (.while b c) before.length).length := by
        rw [compile_length]
        simp only [codeLength]
        omega
      have hfetchB := fetch_segment (before := before)
        (seg := compile (.while b c) before.length) (after := after) hkB
      rw [compile_while_fetch_jiz] at hfetchB
      have hstepB : Step (before ++ compile (.while b c) before.length ++ after)
          (before.length + blen b, 1 :: stack, initial)
          (before.length + blen b + 1, stack, initial) :=
        Step.jumpIfZeroSucc hfetchB
      have hlenC : (before ++ compileB b ++
            [Instr.jumpIfZero (before.length + blen b + 1 + codeLength c + 1)]).length =
          before.length + blen b + 1 := by
        simp only [List.length_append, compileB_length, List.length_cons,
          List.length_nil]
      have hBodyRaw := ihBody (before := before ++ compileB b ++
          [Instr.jumpIfZero (before.length + blen b + 1 + codeLength c + 1)])
        (after := [Instr.jump before.length] ++ after) (stack := stack)
      rw [hlenC] at hBodyRaw
      have hBody : Steps (before ++ compile (.while b c) before.length ++ after)
          (before.length + blen b + 1, stack, initial)
          (before.length + blen b + 1 + codeLength c, stack, middle) := by
        simpa only [compile, List.append_assoc] using hBodyRaw
      have hkJ : blen b + 1 + codeLength c <
          (compile (.while b c) before.length).length := by
        rw [compile_length]
        simp only [codeLength]
        omega
      have hfetchJ := fetch_segment (before := before)
        (seg := compile (.while b c) before.length) (after := after) hkJ
      rw [compile_while_fetch_jump, show before.length + (blen b + 1 + codeLength c) =
          before.length + blen b + 1 + codeLength c from by omega] at hfetchJ
      have hstepJ : Step (before ++ compile (.while b c) before.length ++ after)
          (before.length + blen b + 1 + codeLength c, stack, middle)
          (before.length, stack, middle) :=
        Step.jump hfetchJ
      have hLoop : Steps (before ++ compile (.while b c) before.length ++ after)
          (before.length, stack, middle)
          (before.length + codeLength (.while b c), stack, final) :=
        ihLoop (before := before) (after := after) (stack := stack)
      exact (((hB.trans (Relation.ReflTransGen.single hstepB)).trans hBody).trans
        (Relation.ReflTransGen.single hstepJ)).trans hLoop

/-- **Correctness of compilation to the stack machine.** Let $c$ be a command and $s$, $s'$ states
such that $c$ run from $s$ terminates in $s'$ under the big-step semantics. Let $C_0(c)$ be the
compiled code of $c$ at base program counter $0$ and $\ell(c)$ the instruction count of $c$.
Then the stack machine running $C_0(c)$ goes in finitely many steps from program counter $0$,
the empty stack and state $s$ to program counter $\ell(c)$, the empty stack and state $s'$.

Since $C_0(c)$ has exactly $\ell(c)$ instructions, no step is possible at program counter
$\ell(c)$, so the machine halts there. Only this forward simulation is claimed, not its
converse. -/
theorem compile_correct {c : Cmd} {s s' : State} (h : BigStep c s s') :
    Steps (compile c 0) (0, [], s) (codeLength c, [], s') := by
  simpa using compile_runs h (before := []) (after := []) (stack := [])

end Cslib.IMP.StackMachine
