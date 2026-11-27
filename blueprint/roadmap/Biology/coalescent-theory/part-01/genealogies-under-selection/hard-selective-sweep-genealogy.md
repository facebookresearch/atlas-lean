# Genealogies under a hard selective sweep

Let a favored allele $B$ at a selected locus sweep through a population of $2N$ chromosomes, with $M(t)$ copies of $B$ at time $t$, and let a neutral locus be at recombination probability $r$ per generation from it. Durrett and Schweinsberg (2004), restating Kaplan, Hudson and Langley (1989), trace $k$ copies of the neutral locus back through the sweep as a coalescent in a population subdivided into the $B$ and $b$ backgrounds: with $i$ lineages in $B$ and $j$ in $b$, the transitions are $(i, j) \to (i - 1, j + 1)$ at rate $ir(2N - M(t) - j)/(2N)$, $(i, j) \to (i - 1, j)$ at rate $i[(1 - r)(i - 1)/M(t) + r(i + j - 1)/(2N)]$, $(i, j) \to (i + 1, j - 1)$ at rate $jr(M(t) - i)/(2N)$, and $(i, j) \to (i, j - 1)$ at rate $j[(1 - r)(j - 1)/(2N - M(t)) + r(i + j - 1)/(2N)]$; unlike Kaplan, Hudson and Langley, these rates keep the event that recombination and coalescence occur in one step. In the logistic sweep model, the fraction $p(t) = M(t)/2N$ follows $dp/dt = sp(1 - p)$ from $p(0) = 1/(2N)$ to $p(\tau) = 1 - 1/(2N)$, so $\tau = (2/s)\log(2N - 1)$. Kaplan, Hudson and Langley's relation $H_\infty/H_0 = p_{22}$, with $p_{22}$ the probability that two lineages sampled in $B$ at the end of the sweep have distinct ancestors at its start, gives the reduction in heterozygosity at the neutral locus. Its strong-selection limit, as $N \to \infty$ with $r\log(2N)/s$ converging and $s(\log N)^2 \to \infty$ (Proposition 2), is the joint escape law of the sampled lineages.

## Depends on

- [Logistic trajectory of a selective sweep](../../../detecting-selection/selective-sweeps/sweep-traj.md)
- [Duration of a complete deterministic sweep](../../../detecting-selection/selective-sweeps/sweep-duration-full.md)
- [Joint escape of sampled lineages from a selective sweep](escape-from-a-sweep-by-recombination.md)

## Expansion

1. The two-background coalescent with the four transition rates for a given path $M(t)$, including simultaneous recombination and coalescence.
2. The logistic sweep model and its duration $\tau = (2/s)\log(2N - 1)$.
3. The relation $H_\infty/H_0 = p_{22}$ between heterozygosity after and before the sweep.
4. The multiple-merger description of the sweep from the joint escape limit, and the limit of $p_{22}$.
5. The three-phase model of Kaplan, Hudson and Langley (branching start, deterministic middle, branching end) as the source of the random path, as a separate statement.

## Sources

- R. Durrett and J. Schweinsberg, Approximating selective sweeps, Theor. Popul. Biol. 66 (2004), 129–138, Introduction, equations (2)–(3), Propositions 1–2. <https://doi.org/10.1016/j.tpb.2004.04.002>
- Original result: N. L. Kaplan, R. R. Hudson and C. H. Langley, The "hitchhiking effect" revisited, Genetics 123 (1989), 887–899. <https://doi.org/10.1093/genetics/123.4.887> The two-background coalescent and the heterozygosity relation follow Durrett and Schweinsberg (2004).
