# Finitely many breakpoints and a jointly measurable local-tree field

Consider the [marked whole-chromosome ancestral recombination graph](marked-whole-chromosome-arg-on-0-1-with-homogene.md) of $n$ samples on $[0, 1)$ with homogeneous recombination intensity $\rho\, dx$, run up to the time $T_{\mathrm{GMRCA}}$ of the grand most recent common ancestor. Let $K_s$ be the number of lineages at time $s$. Then:

1. The number of recombination events is finite, with expectation

$$\frac{\rho}{2}\, \mathbb{E} \int_0^{T_{\mathrm{GMRCA}}} K_s\, ds < \infty.$$

The finiteness comes from the occupation estimate $\mathbb{E} \int_0^{T_1} K_s\, ds < \infty$ for [the ancestral line count with recombination](../two-locus-coalescent/lineage-count-birth-death-chain-rho-0-positive-r.md), with $T_1$ its first hitting time of $1$, and not from $\mathbb{E}[T_{\mathrm{GMRCA}}] < \infty$ alone. Hence the set $B$ of breakpoints is finite almost surely.

2. For each $x \in [0, 1)$ let $G_x$ be the local genealogy of the $n$ samples at $x$, a ranked labelled tree with branch lengths. Then $(x, \omega) \mapsto G_x(\omega)$ is jointly measurable, and $G_x$ is constant on each cell $[b_i, b_{i+1})$ of the half-open partition of $[0, 1)$ by $B$.

## Depends on

- [Marked whole-chromosome ARG on [0,1) with homogeneous recombination: construction](marked-whole-chromosome-arg-on-0-1-with-homogene.md)
- [The ancestral line count with recombination is positive recurrent](../two-locus-coalescent/lineage-count-birth-death-chain-rho-0-positive-r.md)

## Proof depends on

- [A Markov kernel run on a Poisson clock is a pure-jump Markov process](../../../Probability/markov-chains/construction-of-markov-chains/uniformized-pure-jump-markov-process-on-a-polish.md)

## Expansion

1. Finiteness of $T_{\mathrm{GMRCA}}$, with finite mean, and the occupation estimate, from [the positive recurrence of the ancestral line count](../two-locus-coalescent/lineage-count-birth-death-chain-rho-0-positive-r.md) for $\rho > 0$ (and its absorption for $\rho = 0$).
2. The expected number of events, from the clock-event count identity for a uniformized pure-jump Markov process on a Polish state space. For $n = 2$, give the bound explicitly.
3. Joint measurability of $(x, \omega) \mapsto T_x$ for $n = 2$, then of $G_x$ in general. $G_x$ is right-continuous in $x$.

## Sources

- R. C. Griffiths and P. Marjoram, An ancestral recombination graph, in *Progress in Population Genetics and Human Evolution*, IMA Vol. Math. Appl. 87, Springer (1997), 257–270, <https://research.monash.edu/en/publications/an-ancestral-recombination-graph/> (local trees).
- C. Wiuf and J. Hein, Recombination as a point process along sequences, *Theor. Popul. Biol.* 55 (1999), 248–259, <https://pubmed.ncbi.nlm.nih.gov/10366550/> (local trees along the sequence).
