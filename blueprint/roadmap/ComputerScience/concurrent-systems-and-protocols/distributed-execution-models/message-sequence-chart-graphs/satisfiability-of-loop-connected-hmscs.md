# Satisfiability of loop-connected high-level message sequence charts is undecidable

Whether a high-level message sequence chart over FIFO channels generates any complete message sequence chart is undecidable, already for loop-connected charts over two processes, for flat loop-connected charts over three processes, and for charts with a single message.

**Setting (Bollig, Fortin and Gastin).** Fix a finite set of processes $\mathcal P$ with peer-to-peer FIFO channels between distinct processes, and a finite set of messages $\mathcal M$. A *compositional message sequence chart* (cMSC) is a finite or infinite set of send and receive events, totally ordered on each process, together with a FIFO matching of some sends with receives; the remaining events are *unmatched* and carry messages from $\mathcal M$, so that later charts can match them. An *MSC* is a cMSC with no unmatched events. Concatenating cMSCs places the second after the first on every process and matches unmatched sends with later unmatched receives on the same channel and with the same message. A *high-level message sequence chart* (HMSC) $\mathcal H = (S, \iota, \mathcal M, R, F, F_\omega)$ is a finite automaton with states $S$, initial state $\iota$ and transitions $R \subseteq S \times \mathrm{cMSC} \times S$ labeled by finite cMSCs; its accepting paths end in $F$ (finite paths) or visit $F_\omega$ infinitely often (infinite paths), and its language $L(\mathcal H)$ is the set of MSCs obtained by concatenating the labels along accepting paths. A cMSC is *connected* if its events form a connected graph under the order and its inverse, and $\mathcal H$ is *loop-connected* if every concatenation along a cycle is connected. *Satisfiability* asks whether $L(\mathcal H) \ne \emptyset$.

**Theorem (Bollig, Fortin and Gastin).**
1. Satisfiability of loop-connected HMSCs with at least two processes is undecidable; it remains undecidable for flat loop-connected HMSCs, in the sense of the source, with three processes.
2. Satisfiability of HMSCs whose message set $\mathcal M$ is a singleton is undecidable.

In contrast, the same paper shows that every loop-connected HMSC can be effectively translated into an equivalent communicating finite-state machine, which extends the realizability of globally cooperative HMSCs by Genest, Kuske and Muscholl to behaviors with unbounded channels. HMSCs whose labels are complete MSCs are the [MSC graphs](msc-graphs-and-weak-realizability.md) of earlier work.

## Depends on

None.

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)
- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

For flat charts with processes $p, q, r$ and a Post correspondence instance given by morphisms $f, g : A^\ast \to B^\ast$, the HMSC lets $p$ send each chosen letter $a \in A$ to both $q$ and $r$; $q$ answers with the letters of $f(a)$ and $r$ with those of $g(a)$, and $p$ finally receives the letters of $B$ one at a time from both channels in the same order. Each label has events on a single process and is therefore connected, and the HMSC is flat, so it is loop-connected; a complete MSC exists exactly when some nonempty word $u$ has $f(u) = g(u)$. The two-process case reduces from the halting problem of a Turing machine on the empty word, with a non-flat HMSC, and the singleton-message case reduces from the halting problem of two-counter machines and uses four processes.

## Sources

- Benedikt Bollig, Marie Fortin and Paul Gastin, "High-Level Message Sequence Charts: Satisfiability and Realizability Revisited", in *Application and Theory of Petri Nets and Concurrency (PETRI NETS 2025)*, Lecture Notes in Computer Science, Springer, 2025, pp. 109–129, doi:[10.1007/978-3-031-94634-9_6](https://doi.org/10.1007/978-3-031-94634-9_6); read in arXiv:2504.19814v1 ([arXiv](https://arxiv.org/abs/2504.19814v1)), whose numbering is used: Section 2 (cMSCs, concatenation, HMSCs, loop-connectedness), Theorem 2 (realizability of loop-connected HMSCs), Theorems 4 and 5 (Section 3), and their proofs in Section 6.
