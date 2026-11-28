# Satisfiability of the logic of subintervals over discrete orders is undecidable

Satisfiability of formulas with only the modality "during" is undecidable over finite linear orders, and also over the class of all discrete orders, although it is decidable over dense orders.

**Theorem (Marcinkowski and Michaliszyn).** For the [logic of subintervals](logic-of-subintervals.md):

1. it is undecidable whether a formula is satisfiable in some model over a suborder of $(\mathbb Z, \le)$; equivalently, since the truth of a formula on an interval depends only on its subintervals, whether it is satisfiable over some finite linear order (Theorem 1 of the source);
2. it is undecidable whether a formula is satisfiable in some model over a discrete linear order (Theorem 2).

This settles the last open case of the classification of fragments of Halpern–Shoham logic by decidability of satisfiability over the classes of orders discussed in the source (finite and discrete orders), and subsumes earlier undecidability results over discrete orders for the fragments with modalities ABE, BE, BD, ADB and AĀD.

## Depends on

- [Logic of subintervals](logic-of-subintervals.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces the halting problem for two-counter (Minsky) machines. For a machine $A$ one defines a regular language $L_A$ whose words almost encode computations of $A$ from empty counters: a word is a sequence of configurations, each starting with a state, in which the value of a counter is the number of symbols before a marked counter symbol, and each counter mark has a *shadow* in the next configuration. For every finite automaton there is a formula of the logic of subintervals that is satisfiable over finite orders exactly when the length-$0$ intervals (the leaves of the interval graph, where each interval $[a, b]$ with $a < b$ has the immediate subintervals $[a + 1, b]$ and $[a, b - 1]$) spell a word of the automaton's language (Lemma 2). Further formulas use intervals above the leaves to force each counter and its shadow to sit at the same offset in consecutive configurations, which is the non-regular part of a correct computation; the resulting formula is satisfiable iff $A$ halts.

For part 2, arXiv:1010.4529v1 states the theorem but leaves the proof of its Section 4 unfinished; the undecidability over discrete structures is the main result of the refereed LICS 2011 version.

## Sources

- J. Marcinkowski and J. Michaliszyn, "The Ultimate Undecidability Result for the Halpern–Shoham Logic", in *2011 IEEE 26th Annual Symposium on Logic in Computer Science (LICS 2011)*, IEEE, 2011, pp. 377–386, <https://doi.org/10.1109/LICS.2011.21>; read as arXiv:1010.4529v1 ("The Last Paper on the Halpern–Shoham Interval Temporal Logic"), <https://arxiv.org/abs/1010.4529v1>: Section 1 (main theorems, Theorems 1 and 2), Section 3 (proof of Theorem 1, Lemma 2) and Section 4 (proof of Theorem 2, unfinished in this version); the LICS 2011 abstract states the undecidability over discrete structures.
