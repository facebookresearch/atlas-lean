# Balanced bipartite amplifiers with near well-mixed fixation time

Use the Moran birth-death process on graphs with mutant fitness $r > 1$, as in the [absorption-time lower bound](absorption-time-lower-bound-for-the-moran-process-on-graphs.md).

**α-Balanced bipartite graph.** For fixed $\alpha \in (0,1)$, let $B_{N,\alpha}$ be the complete bipartite graph with parts of sizes $N$ and $N^{1-\alpha}$ (offspring of a vertex are placed uniformly at random among the vertices of the opposite part).

**Theorem (uniform initialization).** As $N \to \infty$, the fixation probability of a single uniformly placed mutant on $B_{N,\alpha}$ tends to $1 - 1/r^2$, the same limit as for the star graph and strictly larger than the well-mixed limit $1 - 1/r$. Its fixation time is argued in the source, with numerical support but no proof, to be of order $N^{1+\alpha}\log N$, compared with $N\log N$ for the complete graph and $N^2\log N$ for the star.

**α-Weighted bipartite graph.** Let $W_{N,\alpha}$ be $B_{N,\alpha}$ with a self-loop of weight $N^{1-\alpha/2} - N^{1-\alpha}$ added at each vertex of the larger part, so that an offspring born in the larger part usually replaces its parent and only rarely migrates.

**Theorem (temperature initialization).** As $N \to \infty$, the fixation probability of a single mutant placed by temperature on $W_{N,\alpha}$ tends to $1 - 1/r^2$; its fixation time is again argued, heuristically and numerically, to be of order $N^{1+\alpha}\log N$.

**Effective rate of evolution.** With mutation rate $\mu$ per individual per generation, fixation probability $\rho$ and fixation time $\tau$ in steps, the expected generations until a successful mutant arises is $t_1 = 1/(N\mu\rho)$ and the expected generations for it to fix is $t_2 = \tau/N$; the effective rate of evolution is $1/(t_1 + t_2)$. Large $\rho$ matters when $\mu$ is small and small $\tau$ when $\mu$ is large, and at intermediate mutation rates suitable bipartite graphs give a higher effective rate than both the complete graph and the star.

## Depends on

- [Absorption-time lower bound for the Moran process on graphs](absorption-time-lower-bound-for-the-moran-process-on-graphs.md)
- [Moran Fixation](../../../isothermal-theorem-for-evolutionary-graph-dynami/moran-fixation.md)

## Proof sketch

The fixation probability limit comes from the closed-form fixation probability for complete bipartite graphs, evaluated with the smaller part of size $N^{1-\alpha}$. The time estimate follows the star-graph heuristic: on a star the leaves evolve like a well-mixed population, but an effective step occurs only when the centre reproduces, about once in $N$ steps, giving $N^2\log N$. On $B_{N,\alpha}$ an effective step occurs whenever any of the $N^{1-\alpha}$ small-part vertices reproduces, a speed-up by $N^{1-\alpha}$, giving $N^{2}\log N / N^{1-\alpha} = N^{1+\alpha}\log N$; this order is supported by matching numerical computations. Under temperature initialization unweighted graphs cannot amplify substantially, and the heavy self-loops of $W_{N,\alpha}$ are what lower the temperature of the large part enough to recover star-like amplification. Exhaustive computation over all connected graphs with $N = 8$ shows the complete graph and the star are the two extreme points of the probability–time Pareto front under uniform initialization.

## Sources

- J. Tkadlec, A. Pavlogiannis, K. Chatterjee and M. A. Nowak, "Population structure determines the tradeoff between fixation probability and fixation time", Communications Biology 2 (2019), Results "Tradeoff under uniform initialization", "Tradeoff under temperature initialization" and "Effective rate of evolution", and Methods (Supplementary Note 1, Sections 3.2–3.3), <https://doi.org/10.1038/s42003-019-0373-y>, PMCID PMC6478818.
