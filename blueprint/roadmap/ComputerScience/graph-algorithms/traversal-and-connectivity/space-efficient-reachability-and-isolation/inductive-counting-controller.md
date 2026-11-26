# A bounded-register inductive-counting controller for non-reachability

For a digraph on vertex identifiers below $N$ written with $w$ bits and a set of bad vertices, there is a nondeterministic controller with binary choices, a fixed number of natural-number registers and Boolean flags, and access to edge and badness oracles only in explicit query phases, that accepts on some branch if and only if no bad vertex is reachable from the source. Every branch halts within $O\big((N+1)^4 (w + 1)\big)$ instructions, and every register stays below $N + 2^{w} + w + 2$, so the state fits in $O(\log N + w)$ bits.

## Proof sketch

Immerman-Szelepcsényi inductive counting: in round $k$ the controller re-guesses the members of $R_{k-1}$ in increasing order, certifying each by a padded walk, and checks that it found exactly the previous count; honest choices reach the final count check, where the absence of a reachable bad vertex is verified.

## Depends on

- [Immerman-Szelepcsenyi theorem: NL = coNL](../../../../TheoryOfComputation/complexity-classes/immerman-szelepcsenyi.md)
- [The complexity class NL](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/nl.md)

## Sources

- N. Immerman, "Nondeterministic Space is Closed under Complementation", SIAM Journal on Computing 17(5), 1988.
- R. Szelepcsényi, "The Method of Forced Enumeration for Nondeterministic Automata", Acta Informatica 26(3), 1988.
- M. Sipser, "Introduction to the Theory of Computation", 3rd ed., Cengage Learning, 2013.
