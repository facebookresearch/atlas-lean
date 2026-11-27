# Generalized isothermal theorem and fixation bounds for the two-graph Moran process

**Model.** Individuals occupy the vertices $V = \{1,\dots,n\}$ and are residents (fitness $1$) or mutants (fitness $r > 0$). Residents and mutants use different directed graphs on $V$: the *resident graph* $G_R$ with weight matrix $W_R = [w^R_{ij}]$ and the *mutant graph* $G_M$ with $W_M = [w^M_{ij}]$, both row-stochastic. In each step an individual $i$ is chosen with probability proportional to its fitness and copies its type onto $j$ with probability $w^R_{ij}$ if it is a resident and $w^M_{ij}$ if it is a mutant. Starting from one mutant at a uniform vertex, the fixation probability $f(G_R, G_M; r)$ is the probability that mutants take over (both graphs strongly connected). The classical *Moran fixation probability* is $\frac{1 - 1/r}{1 - 1/r^n}$.

**Theorem (generalized isothermal theorem).** The two-graph process has the Moran fixation probability if

1. $W_R$ and $W_M$ are doubly stochastic, $\sum_{j\ne i} w^R_{ji} = \sum_{j\ne i} w^M_{ji} = 1$ for all $i$, and
2. $w^R_{ij} + w^R_{ji} = w^M_{ij} + w^M_{ji}$ for every pair $i,j$.

Equivalently, $\sum_{i\notin S}\sum_{j\in S} w^R_{ij} = \sum_{i\notin S}\sum_{j\in S} w^M_{ji}$ for every $\emptyset \ne S \subsetneq V$: the expected resident flux into any mutant set equals the expected mutant flux out of it.

**Theorem (general bounds and monotonicity).** For any $G_R, G_M$ and $r > 0$, $f(G_R, G_M; r) \le 1 - \frac{1}{r+n}$, asymptotically tight for constant $r$. The fixation probability is monotone in $r$ and in the initial mutant set, and $f(G_R, G_M; r) \le 1 - f(G_M, G_R; 1/r)$.

**Theorem (extreme pairs).**

- Residents on the star $S_n$, mutants on the clique $K_n$: for $r > (n-4)!^{-1/(n-2)}$, $f \ge 1 - \frac1n - \frac{1}{r(n-2)} - \frac{1}{r^2(n-3)}$.
- Residents on $K_n$, mutants on $S_n$: $f \le \frac{r^{n-1}}{(n-2)!}$.
- Hence there are graph pairs with $f = o(a^{-n})$ for every constant $a > 1$ and constant $r$, and pairs with $f \ge 1 - O(1/n)$.
- If $G_R$ is undirected with $w^R_{xy}/w^R_{yx} \le c$ on every edge and $G_M = K_n$, then for $r > 2c$ the fixation probability is asymptotically at least $1 - c/r$.

**Theorem (approximation).** For undirected $G_R$ with ratio bound $c$ and $G_M = K_n$, $n \ge 3$, and $r \ge 2c\big(1 + \frac{1}{n-2}\big)$, the expected absorption time from any state is at most $\frac{r}{r-c}n^2$, and the fixation probability admits an FPRAS (fully polynomial randomized approximation scheme) by simulation.

## Expansion

The number of mutants is not a Markov chain in general, but its one-step up and down probabilities from a mutant set $S$ are $\frac{r}{W(S)}\sum_{i\in S}\sum_{j\notin S}w^M_{ij}$ and $\frac{1}{W(S)}\sum_{i\notin S}\sum_{j\in S}w^R_{ij}$, with $W(S)$ the total fitness. When the two fluxes coincide for every $S$, the ratio of down to up probabilities is always $1/r$, the mutant count is a birth–death chain with constant bias, and the gambler's-ruin formula gives the Moran probability; comparing backward biases with their extremes gives the domination bounds. The $1 - \frac{1}{r+n}$ bound comes from the first step: the initial mutant is replaced before reproducing with probability at least $\frac{1}{r+n}$ on average. On the star–clique pairs the clique type spreads in one step to most vertices while the star type is confined to its center, which yields the exponential separations. The absorption-time bound follows from a drift argument (expected mutant gain at least $(1 - c/r)/n$ per step) and turns Monte Carlo estimation into an FPRAS.

## Sources

- Themistoklis Melissourgos, Sotiris E. Nikoletseas, Christoforos L. Raptopoulos and Paul G. Spirakis, "An extension of the Moran process using type-specific connection graphs", arXiv:1710.07365 (2017), Section 2 (model), Section 5 (Lemma 2, Corollaries 3, 6–7, Theorem 5, Theorem 8, Theorem 9, Lemma 10), Section 6 (Theorems 11, 14–17, Lemma 12, Corollary 18) and Section 7 (Theorem 19, Lemma 20, Theorem 23), <https://doi.org/10.48550/arXiv.1710.07365>. Published version: Journal of Computer and System Sciences 124 (2022) 77–96, <https://doi.org/10.1016/j.jcss.2021.07.007>.
