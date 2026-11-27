# Model checking weighted MTL on priced timed automata is undecidable

Model checking weighted MTL over priced timed automata is decidable for one clock and one stopwatch cost, but becomes undecidable as soon as the cost is general, a second clock is added, or a second stopwatch cost is added.

**Theorem (Bouyer, Larsen and Markey).** The model-checking problem for [weighted MTL over priced timed automata](priced-timed-automata-and-weighted-mtl.md), whether a given automaton has a finite run from its initial state satisfying a given formula, is undecidable for each of the following classes of automata:

1. one-clock priced timed automata with one cost variable (with arbitrary rates in $\mathbb{N}$);
2. two-clock priced timed automata with one stopwatch cost;
3. one-clock priced timed automata with two stopwatch costs.

The source proves that the problem is decidable for one-clock automata with one stopwatch cost, so each clause adds one resource to a decidable case.

## Depends on

- [Priced timed automata and weighted MTL](priced-timed-automata-and-weighted-mtl.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

All three clauses reduce the halting problem for two-counter machines. For clause 1 the single clock stores both counter values, encoding $(c_1, c_2)$ by a clock value such as $2^{-c_1} 3^{-c_2}$ when entering a module, and each instruction is simulated by a module of the automaton in which locations with different cost rates let the formula, through cost-constrained until operators, check that the clock value has been multiplied or divided correctly. Clause 2 uses the same encoding with an extra clock replacing the locations of rate $2$, and clause 3 replaces them by a second stopwatch cost; in both cases the modified automaton still lets the formula check each step.

## Sources

- P. Bouyer, K. G. Larsen and N. Markey, "Model checking one-clock priced timed automata", *Logical Methods in Computer Science* 4(2), Paper 9, 2008, doi:10.2168/LMCS-4(2:9)2008; read as arXiv:0805.1457v2, <https://arxiv.org/abs/0805.1457v2>: the three theorems of the subsection "Undecidability Results" (one-clock automata with one cost, two-clock automata with one stopwatch cost, one-clock automata with two stopwatch costs) and their proofs, and the decidability theorem preceding them.
