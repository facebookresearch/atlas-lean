# Prokhorov's theorem on a Polish space

Let $S$ be a Polish space with its Borel $\sigma$-algebra, and let $\Pi$ be a set of Borel probability measures on $S$. Then the following are equivalent:

1. $\Pi$ is tight: for every $\varepsilon>0$ there is a compact $K\subseteq S$ with $\mu(S\setminus K)\le\varepsilon$ for every $\mu\in\Pi$;
2. $\Pi$ is relatively compact for weak convergence: every sequence in $\Pi$ has a subsequence that converges weakly to a Borel probability measure on $S$, that is, $\int f\,d\mu_{n_j}\to\int f\,d\mu$ for every bounded continuous $f:S\to\mathbb R$.

The implication from 1 to 2 holds on every metric space. In particular, if $S$ is a compact metric space, every set of Borel probability measures on $S$ is tight, so the space of Borel probability measures on $S$ with the topology of weak convergence is sequentially compact.

## Depends on

- [Tight family of probability measures](tightness-of-probability-measures/is-tight-family.md)

## Expansion

A proof page must establish the direct half by a diagonal argument on a countable family of compact sets and a countable algebra of their finite unions, producing a limit measure through a Carathéodory-type extension (or, on a compactification, through the Riesz representation theorem); and the converse on a Polish space by covering $S$, for each $m$, with finitely many balls of radius $1/m$ of uniformly large measure, using completeness and separability to obtain a totally bounded closed, hence compact, set. It should record the compact-metric corollary and that the real-line form is the [sequential form on $\mathbb R$](prokhorov-theorem/prokhorov-sequential.md).

## Sources

- P. Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley, 1999, Chapter 1, Section 5.
- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, <https://doi.org/10.1002/9780470316658>, Chapter 3, Section 2.
