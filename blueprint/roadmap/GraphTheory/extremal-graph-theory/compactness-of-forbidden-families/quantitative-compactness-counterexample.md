# Quantitative counterexample to extremal compactness

There exist a nonempty finite family $\mathcal F$ of connected bipartite simple graphs each containing a cycle, and reals $c,C>0$, satisfying all of the following:

- For every $F\in\mathcal F$ and all sufficiently large $n$, $\operatorname{ex}(n,F)\ge c n^{4/3}$; $c$ is common to all members.
- For every natural $n$ and every $\mathcal F$-free simple graph $H$ on $n$ vertices, $|E(H)|^{16}\le C n^{21}$, with the powers taken in the reals.
- For every natural $n$, $\operatorname{ex}(n,\mathcal F)^{16}\le C n^{21}$ with the same $C$. Here $21/16=4/3-1/48$ and $1/48>0$.
- The exhibited family is not compact; in particular the universal compactness conjecture is false.

## Depends on

- [Extremal number and compactness of a forbidden family](extremal-number-of-a-forbidden-family.md)

## Expansion

Specify the finite forbidden family and check connectedness, bipartiteness and cycles of each member. Prove the common singleton lower estimate and the host bound, pass the latter to the finite maximum with the same constant, and compare the distinct powers to rule out a compactness witness.

## Sources

- [OpenAI, *Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 10](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)
- [Pinned source: `quantitativeCompactnessCounterexample`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/J_CompactnessConjecture.lean#L52-L69)
