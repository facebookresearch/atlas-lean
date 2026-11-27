# Full timed opacity emptiness is undecidable for L/U parametric timed automata

Full timed opacity emptiness stays undecidable for L/U parametric timed automata, where each parameter is used only as a lower or only as an upper bound, already with four clocks and four parameters; plain timed opacity emptiness is decidable for this class.

**Theorem.** The full timed opacity emptiness problem (given an L/U-PTA $\mathcal{A}$, a private location $\ell_{priv}$ and a target location $\ell_f$, is the set of parameter valuations $v$ for which $v(\mathcal{A})$ is fully opaque with respect to $\ell_{priv}$ on the way to $\ell_f$ empty?) is undecidable for [L/U-PTAs](timed-opacity-of-parametric-timed-automata.md) with at least 4 clocks and 4 parameters.

## Depends on

- [Timed opacity of parametric timed automata](timed-opacity-of-parametric-timed-automata.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof again starts from the undecidability of reachability emptiness within bounded time for PTAs with 3 clocks and 2 parameters (André, Lime and Markey). Each parameter $p_i$ of the given PTA is split into a lower-bound parameter $p_i^l$ and an upper-bound parameter $p_i^u$, guards $x = p_i$ becoming $p_i^l \le x \le p_i^u$, so that the result is an L/U-PTA equivalent to the original exactly when $p_i^l = p_i^u$. A gadget with a fresh clock makes every valuation with $p_i^l > p_i^u$ or $p_i^l < p_i^u$ for some $i$ not fully opaque, and for the remaining valuations full opacity holds iff the target is reachable within the time bound. The contrast with timed opacity emptiness, decidable for L/U-PTAs (the source's Theorem 2), places L/U-PTAs at the boundary of decidability.

## Sources

- Étienne André, Didier Lime, Dylan Marinho and Jun Sun, "Guaranteeing timed opacity using parametric timed model checking", *ACM Transactions on Software Engineering and Methodology* 31(4), 36 pages, 2022, <https://doi.org/10.1145/3502851>; read as arXiv:2206.05438v1, <https://arxiv.org/abs/2206.05438v1>: Theorem 4 of that version and its proof (Section 7.2), with Theorem 2 (decidability of timed opacity emptiness for L/U-PTAs).
