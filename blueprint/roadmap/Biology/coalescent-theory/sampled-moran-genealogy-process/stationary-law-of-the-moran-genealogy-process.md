# Stationary law of the Moran genealogy process

**Process.** A Moran population of constant size $n$ undergoes events at rate $\mu$: at each event an ordered pair of distinct individuals is chosen uniformly, the first reproduces and the second dies. The *Moran genealogy process* (MGP) tracks the genealogy of the $n$ living individuals, represented by a discrete tree topology $\mathbf{w}\in\mathcal{W}^n$ together with the durations $\mathbf{s}=(s_1,\dots,s_{n-1})$ of the coalescent intervals, $s_j$ being the time during which the genealogy has $j+1$ lineages.

**Theorem.** The MGP is uniformly and exponentially ergodic: there are $D<\infty$ and $0\le\rho<1$ with $\|\nu K^t-\pi_n\|_{TV}<D\rho^t$ for every initial law $\nu$. Its unique invariant probability measure is
$$\pi_n(d\mathbf{w}\,d\mathbf{s})=\Bigl(\frac{\mu}{\binom n2}\Bigr)^{n-1}\exp\Bigl(-\sum_{j=1}^{n-1}\frac{\binom{j+1}{2}}{\binom n2}\,\mu\,s_j\Bigr)\,d\mathbf{w}\,d\mathbf{s},$$
with counting measure $d\mathbf{w}$ on topologies and Lebesgue measure $d\mathbf{s}$. Equivalently, under stationarity the topology is uniform on $\mathcal{W}^n$ (each with probability $2^{n-1}/(n!(n-1)!)$) and independent of the interval lengths, which are independent exponentials with rates $\binom{j+1}{2}\mu/\binom n2$.

**Theorem (sampling consistency).** For $k\le n$, the genealogy of $k$ individuals sampled from the stationary MGP has marginal law
$$\Bigl(\frac{\mu}{\binom n2}\Bigr)^{k-1}\exp\Bigl(-\sum_{j=1}^{k-1}\frac{\binom{j+1}{2}}{\binom n2}\,\mu\,s_j\Bigr)\,d\mathbf{w}\,d\mathbf{s},$$
i.e. Kingman's coalescent with time scaled by $\mu/\binom n2$, exactly for every finite $n$.

## Expansion

The topology component alone is a finite Markov chain (a "musical chairs with balls" representation), whose stationary law is uniform; at stationarity the expected number of balls held by seat $j$, divided by $n$, equals $j/\binom n2$. Each Moran event resets the most recent coalescent interval and shifts the others, so the interval durations evolve as a piecewise-deterministic process. Verifying that $\pi_n$ is annihilated by the adjoint of the generator gives invariance, and a minorization argument (the whole genealogy is renewed within a bounded time with positive probability) gives uniform exponential ergodicity. Sampling consistency follows by computing the law of the subgenealogy forward in time and integrating out the unsampled lineages.

## Sources

- A. A. King, Q. Lin, E. L. Ionides, "The Sampled Moran Genealogy Process", arXiv:2002.11184 (2020), Theorems 1 and 2 (restated and proved as Theorems 14, 16 and 17), Propositions 11, 12 and 15, Corollary 13, <https://doi.org/10.48550/arXiv.2002.11184>.
