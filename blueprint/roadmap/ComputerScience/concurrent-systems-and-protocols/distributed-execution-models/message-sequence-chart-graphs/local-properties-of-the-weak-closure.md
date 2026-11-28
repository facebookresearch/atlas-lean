# Checking local properties of the weak closure of an MSC graph is undecidable

For a fixed disjunction of two simple properties, each about the messages one process sends, it is undecidable whether every scenario implied by a given bounded MSC graph satisfies it, whereas checking such properties on the graph's own scenarios is decidable.

**Local properties.** A property of MSCs is *local* if it refers only to the events of one process $P_i$; local properties and their Boolean combinations do not depend on the chosen linearization of an MSC. The source makes this precise by fixing a specification logic, for example Boolean combinations of atomic properties, each a regular language over the events of a single process given by a deterministic finite automaton, and its negative results use only properties of a very limited form, such as "event $x$ never occurs on $P_i$" (Section 4.2). The theorem below uses two such properties of MSCs over processes $P_1, \dots, P_4$ whose message alphabet contains the pairs $(i, b)$ with $i \in \mathbb N$ and $b \in \{0, 1\}$, besides arbitrary other messages: $\psi_1$ says that every message sent by $P_1$ to $P_2$ is a pair $(i, 1)$, and $\psi_2$ that every message sent by $P_4$ to $P_3$ is a pair $(i, 0)$. Each is local ($\psi_1$ depends only on the events of $P_1$, $\psi_2$ only on those of $P_4$).

**Theorem (Alur, Etessami and Yannakakis).** Given a bounded [MSC graph](msc-graphs.md) $G$ over the processes $P_1, \dots, P_4$ whose message alphabet contains the pairs $(i, b)$ as above, its other messages being unrestricted, it is undecidable whether every MSC in the weak closure $L^w(G)$ satisfies $\neg\psi_1 \vee \neg\psi_2$ (Theorem 9 and its proof).

The property is fixed and the graph is the input. By contrast, checking LTL properties of $L(G)$ itself is PSPACE-complete for bounded graphs, and there are local properties $\varphi_1, \varphi_2$ such that, for a finite set of MSCs, checking $\varphi_1 \vee \varphi_2$ on every MSC of the weak closure is coNP-complete (Theorem 8).

## Depends on

- [MSC graphs](msc-graphs.md)
- [Weak closure and weak realizability of sets of MSCs](weak-closure-and-weak-realizability.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Weak realizability of bounded MSC graphs is undecidable](weak-realizability-of-bounded-msc-graphs.md)

## Expansion

The proof reuses the MSC graphs of the undecidability proof for weak realizability. When an implied but unspecified MSC exists, there is one in which the two strings use words from different lists, which shows up as local properties of the messages sent by two of the processes. Hence $\neg\psi_1 \vee \neg\psi_2$ holds on all of $L^w(G)$ iff the relaxed Post correspondence instance has no solution. The proof thus uses more than the statement of the weak-realizability theorem: it uses the relaxed Post correspondence problem (Lemma 2 of the source) and the particular MSC graphs built from its instances in the proof of Theorem 1, with their property that an implied MSC whose two strings use words from different lists exists iff the instance has a solution. A good expansion links pages for the undecidability of the relaxed Post correspondence problem (Lemma 2) and for that construction.

## Sources

- Rajeev Alur, Kousha Etessami and Mihalis Yannakakis, "Realizability and verification of MSC graphs", *Theoretical Computer Science* 331(1):97–114, 2005, doi:10.1016/j.tcs.2004.09.034; read in the authors' open-access copy at <https://www.cis.upenn.edu/~alur/Icalp01.pdf>, the authors' manuscript of the journal version: Section 4.2 (local properties and their specification logic, Theorems 8 and 9 and the proof of Theorem 9) of that copy.
