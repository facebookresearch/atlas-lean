# Full timed opacity emptiness is undecidable for parametric timed automata

It is undecidable whether some parameter valuation makes a parametric timed automaton fully opaque, that is, gives equal sets of execution times with and without the private location, already for automata with four clocks and two parameters.

**Theorem.** The full timed opacity emptiness problem (given a PTA $\mathcal{A}$, a private location $\ell_{priv}$ and a target location $\ell_f$, is the set of parameter valuations $v$ for which $v(\mathcal{A})$ is fully opaque with respect to $\ell_{priv}$ on the way to $\ell_f$ empty?) is undecidable for [parametric timed automata](timed-opacity-of-parametric-timed-automata.md) with at least 4 clocks and 2 parameters.

## Depends on

- [Timed opacity of parametric timed automata](timed-opacity-of-parametric-timed-automata.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof first shows that reachability emptiness in constant time is undecidable for PTAs with 4 clocks and 2 parameters (Lemma 4 of the source): it is undecidable whether some valuation lets a run reach a given location in exactly $T = 1$ time unit. This follows from the undecidability of reachability emptiness within bounded time for PTAs with 3 clocks and 2 parameters (André, Lime and Markey), by adding a new clock that is never reset and an exit edge guarded by $x = 1$. Full opacity is then reduced from it: a new urgent initial location leads into $\mathcal{A}$ and to a public location from which the final location $\ell'_f$ is reachable exactly at time $1$, and $\ell_f$ leads to $\ell'_f$ through the urgent private location. The automaton is fully opaque for a valuation iff $\ell_f$ is reached at time $1$ under it.

## Sources

- Étienne André, Didier Lime, Dylan Marinho and Jun Sun, "Guaranteeing timed opacity using parametric timed model checking", *ACM Transactions on Software Engineering and Methodology* 31(4), 36 pages, 2022, <https://doi.org/10.1145/3502851>; read as arXiv:2206.05438v1, <https://arxiv.org/abs/2206.05438v1>: Lemma 4 and Theorem 3 of that version, with their proofs (Section 7.1).
