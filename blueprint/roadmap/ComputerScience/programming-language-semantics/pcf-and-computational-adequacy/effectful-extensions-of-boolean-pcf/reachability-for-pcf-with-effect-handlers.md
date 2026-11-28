# Reachability for simply typed finitary PCF with effect handlers is undecidable

Reachability is decidable for simply typed finitary PCF, a higher-order language with recursion and finite base types, but adding effect handlers makes it undecidable. A fixed program shape that simulates two-register Minsky machines with one operation and one handler per decrement already suffices.

**The language (Endo and Terauchi).** Untyped finitary PCF with effect handlers, in call-by-push-value style, has values, computations and handlers

$$
v ::= x \mid () \mid \mathtt{true} \mid \mathtt{false} \mid \lambda x.c \mid \mathtt{rec}\,x.v, \qquad c ::= \mathtt{return}\ v \mid \mathit{op}\ v \mid v_1\, v_2 \mid \mathtt{if}\ v\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2 \mid \mathtt{let}\ x = c_1\ \mathtt{in}\ c_2 \mid \mathtt{with}\ h\ \mathtt{handle}\ c,
$$

$$
h ::= \{\mathtt{return}\ x = c,\ \mathit{op}_1\, x_1\, k_1 = c_1, \dots, \mathit{op}_n\, x_n\, k_n = c_n\}.
$$

Evaluation is the usual small-step call-by-value reduction; when the handled computation is $E[\mathit{op}\ v]$ with $E$ an evaluation context $E ::= [\,] \mid \mathtt{let}\ x = E\ \mathtt{in}\ c$, which reaches only up to the nearest enclosing handler, and $h$ contains $\mathit{op}\, x\, k = c$, the step goes to $c[v/x, (\lambda y.\, \mathtt{with}\ h\ \mathtt{handle}\ E[\mathtt{return}\ y])/k]$ (deep handlers). A program is a closed computation, and the *reachability problem* asks, given a program $c$, whether $c \to^* \mathtt{return\ true}$. A program is simply typed if it is typable in the paper's simple type system $\vdash_{\mathrm{st}}$, in which operations have types.

**Theorem (Endo and Terauchi).** Reachability is undecidable for the class $\mathit{MM}$ of programs of the form

$$
\mathtt{mrec}\ f_0 = \lambda x_0.\lambda x_1.\, c_0\ \mathtt{and} \dots \mathtt{and}\ f_n = \lambda x_0.\lambda x_1.\, c_n\ \mathtt{in}\ (f_0\, (\lambda x.())\, (\lambda x.()));\ \mathtt{true},
$$

where $n \ge 0$, each $c_i$ is either $c^{i',j}_{\mathit{inc}} = \mathtt{let}\ x_{i'} = \lambda y.\, \mathit{succ}\ x_{i'}\ \mathtt{in}\ f_j\, x_0\, x_1$ or $c^{i',j,m}_{\mathit{dec}} = \mathtt{with}\ \{\mathtt{return}\ x = f_j\, x_0\, x_1,\ \mathit{succ}\ x_{i'}\ k = f_m\, x_0\, x_1\}\ \mathtt{handle}\ x_{i'}\, ()$ with $i' \in \{0, 1\}$, $j \in \{0, \dots, n\}$ in $c^{i',j}_{\mathit{inc}}$, and $j, m \in \{0, \dots, n\} \cup \{()\}$ in $c^{i',j,m}_{\mathit{dec}}$, where a target $()$ puts the computation $()$ in place of the call $f_j\, x_0\, x_1$ (respectively $f_m\, x_0\, x_1$), so that the program halts there; $\mathtt{mrec}$ is mutual recursion encoded with $\mathtt{rec}$ and $\mathtt{let}$. Every program in $\mathit{MM}$ is $\vdash_{\mathrm{st}}$-typable.

In particular reachability for $\vdash_{\mathrm{st}}$-typable finitary PCF with effect handlers is undecidable, as Dal Lago and Ghyselen proved for operations on base types ([reachability for Boolean PCF with algebraic effects](reachability-with-algebraic-effects-undecidable.md)); the operation $\mathit{succ}$ in $\mathit{MM}$ takes a function argument, which their setting excludes. Without effect handlers reachability for simply typed finitary PCF is decidable, and the paper shows that it becomes decidable again for programs typable in its type system with answer-type modification.

## Depends on

- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

A program in $\mathit{MM}^n$ implements an $(n+1)$-state two-register Minsky machine: the recursive function $f_j$ is state $j$, $f_0$ the initial one; each $c^{i',j}_{\mathit{inc}}$ increments register $r_{i'}$, held in the variable $x_{i'}$ as a function that performs the operation $\mathit{succ}$, and goes to state $j$; each $c^{i',j,m}_{\mathit{dec}}$ checks $r_{i'}$ by running $x_{i'}$ under a handler, going to state $j$ if the register is $0$ and otherwise decrementing it and going to state $m$; the halting instruction is the target $()$ of a decrement. The program returns $\mathtt{true}$ exactly when the machine halts. A good expansion adds a page that defines finitary PCF with effect handlers and its type system $\vdash_{\mathrm{st}}$, and a lemma stating that a program of $\mathit{MM}^n$ returns $\mathtt{true}$ exactly when its machine halts (Appendix G of the source). The construction adapts a proof of Kobayashi for finitary PCF with exceptions ([reachability with exceptions](reachability-with-exceptions-is-undecidable.md), stated for [Boolean PCF](boolean-pcf-and-its-reachability-problem.md), whose reachability target is $\mathtt{fail}$ rather than $\mathtt{return\ true}$).

## Sources

- Ryunosuke Endo and Tachio Terauchi, "Reachability is Decidable for ATM-Typable Finitary PCF with Effect Handlers", Programming Languages and Systems, Lecture Notes in Computer Science, pp. 67–87, Springer, 2025, <https://doi.org/10.1007/978-981-95-3585-9_4>; the syntax and semantics figures, Definition 1 (reachability) and Theorems 1 and 2 (the decidable and undecidable cases recalled from earlier work) in Section 2, Theorem 3 (decidability for ATM-typable programs) and Theorem 7 (the class $\mathit{MM}$) with its definition in the subsection "Number of Active Effect Handlers Does Not Capture Decidability" of Section 3, and the proof of Theorem 7 in the appendix of arXiv:2508.12572v2 (the copy read), <https://arxiv.org/abs/2508.12572v2>.
