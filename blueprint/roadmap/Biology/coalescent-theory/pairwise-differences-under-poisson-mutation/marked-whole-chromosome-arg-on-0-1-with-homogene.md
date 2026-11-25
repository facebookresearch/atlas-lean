# Marked whole-chromosome ARG on [0,1) with homogeneous recombination: construction

Fix $n \ge 1$ samples and $\rho \ge 0$. A state is a finite multiset of lineages. Each lineage is a whole chromosome $[0, 1)$ carrying marks: for each $x \in [0, 1)$, the subset of the $n$ samples to which it is ancestral at $x$, which as a function of $x$ is constant on the cells of a finite partition of $[0, 1)$ into half-open intervals. The initial state is $n$ lineages with singleton marks.

The dynamics are:

- each pair of lineages coalesces at rate $1$, and the marks of the two are united pointwise;
- each lineage recombines at rate $\rho/2$, at a breakpoint $b$ uniform on $[0, 1)$, and splits into two lineages, carrying its marks on $[0, b)$ and on $[b, 1)$. The cut is half-open, so the point $b$ goes to the right part.

The state space, of finite multisets of lineages whose marks are encoded by finite lists of interval endpoints and sample subsets, is a countable disjoint union of open subsets of Euclidean spaces, hence Polish. The process exists as a pure-jump Markov process on it: on the level where there are at most $K$ lineages it is the uniformization with clock rate $c = \binom{K}{2} + \rho K/2$, and these constructions are patched together as $K \to \infty$ using that [the dominating line-count chain](../two-locus-coalescent/lineage-count-birth-death-chain-rho-0-positive-r.md) does not explode.

General finite recombination measures, with atoms, are a separate target: [the continuum ARG with a general recombination measure](../two-locus-coalescent/continuum-arg-with-a-general-finite-recombinatio.md).

## Depends on

- [The ancestral line count with recombination is positive recurrent](../two-locus-coalescent/lineage-count-birth-death-chain-rho-0-positive-r.md)

## Proof depends on

- [A Markov kernel run on a Poisson clock is a pure-jump Markov process](../../../Probability/markov-chains/construction-of-markov-chains/uniformized-pure-jump-markov-process-on-a-polish.md)

## Expansion

1. The state space is Polish: a countable union of finite-dimensional pieces.
2. The construction on each localized level by uniformization of a pure-jump Markov process on a Polish state space, with its clock-event counts (a Lévy system), and the patching over $K$.
3. The number of lineages is exactly [the ancestral line count with recombination](../two-locus-coalescent/lineage-count-birth-death-chain-rho-0-positive-r.md) (coalescence at rate $\binom{k}{2}$, recombination at rate $\rho k/2$), which is positive recurrent for $\rho > 0$ and absorbed at $1$ for $\rho = 0$.
4. The half-open cut convention.

## Sources

- R. C. Griffiths and P. Marjoram, An ancestral recombination graph, in *Progress in Population Genetics and Human Evolution*, IMA Vol. Math. Appl. 87, Springer (1997), 257–270, <https://research.monash.edu/en/publications/an-ancestral-recombination-graph/> (the ancestral recombination graph).
- R. Durrett, *Probability Models for DNA Sequence Evolution*, 2nd ed., Springer (2008), <https://doi.org/10.1007/978-0-387-78168-6>, Chapter 3 (the coalescent with recombination).
