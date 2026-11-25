# Translation of a while language to a control-flow-graph IR

A *control-flow-graph IR* for the while language [IMP](../operational-semantics-of-imp/cmd.md) is a finite graph whose nodes are labelled by instructions over variables and fresh temporaries:
- $x := a$ with an atomic right-hand side, and $t := t_1 \mathbin{op} t_2$, each with one successor;
- a conditional branch $\mathbf{if}\ t\ \mathbf{then}\ \ell_1\ \mathbf{else}\ \ell_2$;
- $\mathbf{nop}$ with one successor;
- $\mathbf{return}$.

Its small-step semantics acts on configurations (current node, store). A node with one successor executes its instruction and moves to that successor, and $\mathbf{return}$ halts.

The structural translation emits the graph backwards from a given successor node:
- *Expressions.* An arithmetic or boolean expression becomes a chain of three-address instructions computing it into a fresh temporary.
- *Skip.* $\mathbf{skip}$ emits no node: its translation is the given successor itself.
- *Assignment.* $x := a$ becomes the chain for $a$ followed by $x := t$.
- *Sequence.* $c_1; c_2$ translates $c_2$ first and uses its entry as the successor of $c_1$.
- *Conditional.* $\mathbf{if}\ b$ evaluates $b$ and branches to the translations of the two arms, which share the successor.
- *Loop.* $\mathbf{while}\ b\ \mathbf{do}\ c$ allocates a $\mathbf{nop}$ node as the loop head. The head is followed by the test of $b$, which branches to the translation of $c$ (whose successor is the head) or to the loop's successor.

**Theorem (semantic preservation).** Let $g$ be the translation of a command $c$, with its exit at a $\mathbf{return}$ node. For every initial store $\sigma_0$:
- $c$ terminates from $\sigma_0$ in a store $\sigma$ if and only if $g$ reaches $\mathbf{return}$ from its entry with a store that agrees with $\sigma$ on the variables of $c$;
- $c$ diverges from $\sigma_0$ if and only if $g$ runs forever.

**Proof.** Relate an IMP configuration $\langle c', \sigma\rangle$ to a CFG configuration $(\ell, \rho)$ when $\ell$ is the entry of the translation of $c'$ with the current continuation, and $\rho$ agrees with $\sigma$ on the source variables. Every IMP step is matched by one or more CFG steps that preserve the relation:
- an assignment runs its expression chain and its final move;
- a conditional evaluates its test and branches;
- a loop unfolding passes through the head and its test.

A configuration whose command is $\mathbf{skip}$ is related to the successor node itself, since $\mathbf{skip}$ emits no node. Steps that IMP takes without a matching CFG step, such as discarding $\mathbf{skip}$ in a sequence, strictly decrease the size of the command, so no infinite sequence of them exists. This is a forward simulation in the sense of [simulation diagrams](../compiler-correctness/simulation-diagrams-for-compiler-correctness.md): terminating executions map to terminating executions with related final states, and diverging executions to diverging ones. Both semantics are deterministic and the CFG never gets stuck before $\mathbf{return}$, so the forward simulation also gives the converse directions.

## Depends on

- [IMP small-step relation](../operational-semantics-of-imp/step.md)
- [Simulation diagrams for compiler correctness](../compiler-correctness/simulation-diagrams-for-compiler-correctness.md)

## Proof depends on

- [Determinism of IMP small-step semantics](../operational-semantics-of-imp/deterministic-3.md)

## Sources

- X. Leroy, "Formal verification of a realistic compiler", *Communications of the ACM* 52(7):107–115, 2009, <https://xavierleroy.org/publi/compcert-CACM.pdf>:
    - Section 2.1 (notions of semantic preservation, covering termination, divergence and going wrong);
    - Section 3.2 (the translation from CminorSel to RTL, a control-flow graph of instructions over temporaries);
    - Section 4.1 (RTL's control-flow graphs and small-step semantics);
    - Section 4.3 (proof by simulation diagram); the translation and proof above instantiate this method for a while language.
- A. W. Appel, *Modern Compiler Implementation in ML*, Cambridge University Press, 1998.
