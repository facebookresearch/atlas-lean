# Checking local properties of the weak closure of an MSC graph is undecidable

There is a fixed Boolean combination of local properties of message sequence charts for which it is undecidable whether every scenario implied by a given bounded MSC graph satisfies it, whereas the same check on the graph's own scenarios is decidable.

**Local properties.** A property of MSCs is *local* if it refers only to the events of one process $P_i$, such as "event $x$ eventually occurs on $P_i$" or "event $x$ never occurs on $P_i$"; local properties and their Boolean combinations do not depend on the chosen linearization of an MSC.

**Theorem (Alur, Etessami and Yannakakis).** There is a Boolean combination $\varphi$ of local properties such that, given a bounded [MSC graph](msc-graphs.md) $G$, it is undecidable whether every MSC in the weak closure $L^w(G)$ satisfies $\varphi$ (Theorem 9).

The property is fixed and the graph is the input. By contrast, checking LTL properties of $L(G)$ itself is PSPACE-complete for bounded graphs, and there are local properties $\varphi_1, \varphi_2$ such that, for a finite set of MSCs, checking $\varphi_1 \vee \varphi_2$ on every MSC of the weak closure is coNP-complete (Theorem 8).

## Depends on

- [MSC graphs](msc-graphs.md)
- [Weak closure and weak realizability of sets of MSCs](weak-closure-and-weak-realizability.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Weak realizability of bounded MSC graphs is undecidable](weak-realizability-of-bounded-msc-graphs.md)

## Expansion

The proof reuses the MSC graphs of the undecidability proof for weak realizability. When an implied but unspecified MSC exists, there is one in which the two strings use words from different lists, which shows up as local properties of the messages sent by two of the processes. A fixed Boolean combination of these local properties therefore holds on all of $L^w(G)$ iff the relaxed Post correspondence instance has no solution.

## Sources

- Rajeev Alur, Kousha Etessami and Mihalis Yannakakis, "Realizability and verification of MSC graphs", *Theoretical Computer Science* 331(1):97–114, 2005, doi:10.1016/j.tcs.2004.09.034; read in the authors' open-access copy at <https://www.cis.upenn.edu/~alur/Icalp01.pdf>, which carries the journal text: Section 4.2 (local properties, Theorems 8 and 9 and the proof of Theorem 9) of that copy.
