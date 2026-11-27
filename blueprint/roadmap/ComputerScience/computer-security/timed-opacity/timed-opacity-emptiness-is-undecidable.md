# Timed opacity emptiness is undecidable for parametric timed automata

It is undecidable whether some parameter valuation makes a parametric timed automaton opaque, with respect to a private location on the way to a final location, for at least one execution time.

**Theorem.** The timed opacity emptiness problem for [parametric timed automata](timed-opacity-of-parametric-timed-automata.md) (given a PTA $\mathcal{A}$, a private location $\ell_{priv}$ and a target location $\ell_f$, is the set of parameter valuations $v$ for which $v(\mathcal{A})$ is opaque with respect to $\ell_{priv}$ on the way to $\ell_f$ for a nonempty set of execution times empty?) is undecidable.

## Depends on

- [Timed opacity of parametric timed automata](timed-opacity-of-parametric-timed-automata.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces reachability emptiness for PTAs (is there a valuation for which some run reaches a given location $\ell_f$?), undecidable by Alur, Henzinger and Vardi and later refinements, all by encodings of two-counter machines. Given $\mathcal{A}$ and $\ell_f$, add a new urgent initial location with unguarded edges to $\ell_0$ and to a new location $\ell_{pub}$, a new urgent private location $\ell_{priv}$ entered from $\ell_f$ (made urgent), and a new final location $\ell'_f$ entered from $\ell_{priv}$ and from $\ell_{pub}$. Every duration is realized by a run avoiding $\ell_{priv}$, and $\ell_{priv}$ is reached on the way to $\ell'_f$ exactly at the durations at which $\ell_f$ is reachable in $\mathcal{A}$; so some valuation gives opacity for some execution time iff $\ell_f$ is reachable in $\mathcal{A}$ for some valuation. With the refinement of Beneš, Bezděk, Larsen and Srba, the result holds already for PTAs with three clocks and one parameter, as the source remarks.

## Sources

- Étienne André, Didier Lime, Dylan Marinho and Jun Sun, "Guaranteeing timed opacity using parametric timed model checking", *ACM Transactions on Software Engineering and Methodology* 31(4), 36 pages, 2022, <https://doi.org/10.1145/3502851>; read as arXiv:2206.05438v1, <https://arxiv.org/abs/2206.05438v1>: Theorem 1 of that version and its proof (Section 6.1).
