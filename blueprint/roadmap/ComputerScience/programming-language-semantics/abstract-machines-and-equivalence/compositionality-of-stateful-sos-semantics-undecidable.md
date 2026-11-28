# Compositionality of stateful SOS trace and termination semantics is undecidable

Stateful SOS specifies imperative languages by rules in which a program and a state step to a new state and program. Their natural trace and termination equivalences can fail to be congruences, and whether they are congruences for a given specification is undecidable.

**Setting (Goncharov, Milius, Schröder, Tsampas and Urbat).** Fix a countable set $S$ of states and an algebraic signature $\Sigma$; programs are closed $\Sigma$-terms. A *literal* is either progressing, $s, p \to s', q$, or terminating, $s, p \downarrow s'$, with input state $s$, output state $s'$ and terms $p, q$ over variables. A *stateful SOS rule* for an $n$-ary operator $f$ has premisses $l_1, \dots, l_n$, where $l_j$ has source $x_j$ (and target $y_j$ if progressing), and a conclusion with source $f(x_1, \dots, x_n)$, all with the same input state $s$; its *trigger* is $s$ together with the output states of the premisses and whether each premiss progresses or terminates. A *stateful SOS specification* contains exactly one rule for each operator and each trigger. Running a program $p$ on a state $s$ gives the possibly infinite sequence of states $s, p \to s_1, p_1 \to s_2, p_2 \to \cdots$ of its steps, possibly ending in termination. Two programs are *trace equivalent*, $p \simeq q$, if they produce the same sequence of states on every input state, and *termination equivalent*, $p \approx q$, if on every input state either both diverge or both terminate with the same final state. The trace (respectively termination) semantics is *compositional* if $\simeq$ (respectively $\approx$) is a congruence for the operators of $\Sigma$. A specification is regarded as the total function mapping an operator, an input state and the premisses to the conclusion's target and output state, encoded as finite strings; as an input, a primitive recursive specification is given by a primitive recursive definition of this function.

**Theorem (Goncharov, Milius, Schröder, Tsampas and Urbat).** It is undecidable whether the trace semantics induced by a primitive recursive stateful SOS specification is compositional, and likewise whether its termination semantics is compositional.

In contrast, the same paper shows that the finer resumption semantics of every stateful SOS specification is compositional, and gives easily checked syntactic formats, streamlined and cool specifications, under which the trace and the termination semantics are compositional.

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

From a Turing machine $M$ the proof builds a primitive recursive specification whose states include the configurations of $M$. Two constants $i$ and $j$ first simulate $M$ on the empty tape, step by step through the configurations, and on reaching the halting configuration continue as two programs that behave identically on their own but differ under a unary operator $u$ that overwrites the state after one step, in the manner of a store-erasing operator. If $M$ halts, $i$ and $j$ are equivalent while $u(i)$ and $u(j)$ are not; if $M$ never halts, the equivalence relates only the pairs $u^n(i), u^n(j)$ and is therefore a congruence. So compositionality fails exactly when $M$ halts on the empty tape.

## Sources

- Sergey Goncharov, Stefan Milius, Lutz Schröder, Stelios Tsampas and Henning Urbat, *Stateful Structural Operational Semantics*, 7th International Conference on Formal Structures for Computation and Deduction (FSCD 2022), LIPIcs 228, Schloss Dagstuhl, 2022, article 30, https://doi.org/10.4230/LIPIcs.FSCD.2022.30; Definitions 3.1–3.3, 4.8 and 4.11 and Theorem 4.12, read in the open-access copy at https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2022.30, with the full proof read in arXiv:2202.10866v3.
