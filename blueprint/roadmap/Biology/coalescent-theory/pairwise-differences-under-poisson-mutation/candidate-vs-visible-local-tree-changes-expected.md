# Candidate and visible local-tree changes along the chromosome

Consider the [marked whole-chromosome ancestral recombination graph](marked-whole-chromosome-arg-on-0-1-with-homogene.md) of $n$ samples on $[0, 1)$ with homogeneous recombination intensity $\rho\, dx$. For a position $x$, let $G_x$ be the local tree at $x$ and $L_x$ its total branch length.

A candidate event in a Borel set $A \subseteq [0, 1)$ is a recombination event of the graph whose breakpoint $b$ lies in $A$ and falls on a branch of the local tree $G_b$. Then

$$\mathbb{E}\,\#\{\text{candidate events in } A\} = \frac{\rho}{2} \int_A \mathbb{E}[L_x]\, dx.$$

A visible change is a breakpoint $b$ with $G_b \ne G_{b-}$. Pathwise, every visible change is a candidate event, so the number of visible changes is at most the number of candidates. For $n = 2$ and $\rho > 0$ the inequality of expectations is strict: with positive probability the two parts created by a recombination coalesce with each other before either meets the other sample lineage, and the local tree does not change.

## Depends on

- [Marked whole-chromosome ARG on [0,1) with homogeneous recombination: construction](marked-whole-chromosome-arg-on-0-1-with-homogene.md)

## Proof depends on

- [A Markov kernel run on a Poisson clock is a pure-jump Markov process](../../../Probability/markov-chains/construction-of-markov-chains/uniformized-pure-jump-markov-process-on-a-polish.md)
- [Finitely many breakpoints and a jointly measurable local-tree field](finitely-many-breakpoints-and-a-jointly-measurab.md)

## Expansion

1. The expected count of candidates, from the clock-event count identity for a uniformized pure-jump Markov process on a Polish state space (a Lévy system), applied on the localized levels of the construction.
2. The pathwise inequality and the explicit invisible event for $n = 2$.
3. A check: for $n = 2$ the expected number of candidates in $[0, 1)$ is $\rho\, \mathbb{E}[T] = \rho$, where $T$ is the pair coalescence time.
4. The statement uses the intensity $\rho\, dx$ only. General recombination measures are a separate target: [the continuum ARG with a general recombination measure](../two-locus-coalescent/continuum-arg-with-a-general-finite-recombinatio.md).

## Sources

- C. Wiuf and J. Hein, Recombination as a point process along sequences, *Theor. Popul. Biol.* 55 (1999), 248–259, <https://pubmed.ncbi.nlm.nih.gov/10366550/> (the spatial process).
