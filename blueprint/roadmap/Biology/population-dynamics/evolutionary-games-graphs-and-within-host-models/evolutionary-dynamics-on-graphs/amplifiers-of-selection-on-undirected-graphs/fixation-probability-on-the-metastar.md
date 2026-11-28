# Fixation probability on the Metastar

Consider the generalized Moran process of [Fixation probability on the Star graph](fixation-probability-on-the-star-graph.md).

**Lazy process.** For a graph $G_m$ with a distinguished *attachment vertex* $v$, the $v$-lazy process is the generalized Moran process on $G_m$ except that whenever the individual on $v$ reproduces, with probability $1/(\deg(v)+1)$ it replaces itself (no change); otherwise it replaces a uniformly random neighbour. Let $p = \rho(r, G_m, v)$ be the fixation probability of a uniformly placed single mutant in this process, $\beta = \rho^+(r, G_m, v)$ the fixation probability of a single mutant placed on $v$, and $\alpha = \rho^-(r, G_m, v)$ the extinction probability of mutants when a single resident is placed on $v$ in an otherwise mutant $G_m$.

**Metastar.** For $n \ge 1$, the Metastar $\mathcal{M}^{G_m}_{N(n)}$ on $N(n) = nm + 1$ vertices consists of $n$ disjoint copies of $G_m$ and a root vertex $s$ joined by one edge to the attachment vertex of each copy. With $m = 1$ it is the Star $S_{n+1}$.

**Theorem.** For a fixed graph $G_m$ with attachment vertex $v$ and mutant fitness $r \ge 1$, set $x = r^{-2}(\alpha/\beta)$. Then

$$\rho\big(r, \mathcal{M}^{G_m}_{N(n)}\big) \;\ge\; p\cdot\frac{1}{1 + x + \cdots + x^{n-1}}\,\big(1 + o(1)\big) \quad (n \to \infty),$$

where the factor $1/(1 + x + \cdots + x^{n-1})$ equals $\frac{1 - x}{1 - x^n}$ for $x \ne 1$ and $1/n$ at $x = 1$ (avoiding the $0/0$ indeterminacy of the quotient at neutrality $r = 1$, where $\alpha = \beta$; for a uniformly placed neutral mutant on any connected undirected graph of size $N = nm + 1$, the exact fixation probability is $1/(nm+1)$),

so that

$$\lim_{N\to\infty}\rho\big(r, \mathcal{M}^{G_m}_{N}\big) \;\ge\; p\,\big(1 - r^{-2}\alpha/\beta\big).$$

For a single-vertex leaf ($p = \alpha = \beta = 1$) and fitness $r \ge 1$, this recovers the large-population Star value $1 - r^{-2}$ (equal to $0$ at $r = 1$, the limit of the neutral value $1/N$). No such recovery is claimed for $0 < r < 1$, where $1 - r^{-2} < 0$ (for example $-3$ at $r = 1/2$) cannot be a fixation probability.

The restriction $r \ge 1$ is the source's standing assumption (mutants "are associated with a fitness advantage $r \ge 1$" in its model section), under which its Theorem 1 is stated and proved. The linked Star page allows any $r > 0$, but this page makes no claim for disadvantageous mutants $0 < r < 1$.

## Depends on

- [Fixation probability on the Star graph](fixation-probability-on-the-star-graph.md)

## Proof depends on

- [Hitting probabilities of finite birth–death chains](../../../../../Probability/markov-chains/finite-continuous-time-markov-chains/hitting-times-of-finite-continuous-time-markov-c/hitting-probabilities-and-stationary-laws-of-bir.md)

## Proof sketch

The root has $n$ neighbours and reproduces about once every $N$ steps, so it hits a given leaf only every $\Omega(n^2)$ steps, while a constant-size leaf becomes homogeneous in $O(n)$ steps. Two lemmas make this precise: when the root hits a leaf, that leaf is heterogeneous at the next hit with probability $O(1/n)$, and a heterogeneous leaf transmits to another leaf (a "heterogeneous hit") with probability $O(1/n)$. Hence, up to $o(1)$ errors, the initial mutant first fixes inside its own leaf with probability $p$ (the leaf behaves as a $v$-lazy process because $v$ loses offspring to the root at the same rate as to a neighbour), and afterwards the Metastar behaves like a Star whose leaves flip to mutant with probability $\beta$ and back to resident with probability $\alpha$. The forward bias of the leaf-count chain is thus $r^2\beta/\alpha$ instead of the Star's $r^2$, and the gambler's-ruin formula gives the bound (Theorem 1 and Eqs. (1)–(2) of the source; formal proofs in its Supplementary Information).

## Sources

- A. Pavlogiannis, J. Tkadlec, K. Chatterjee, M. A. Nowak, "Amplification on undirected population structures: Comets beat stars", Scientific Reports (2017), <https://doi.org/10.1038/s41598-017-00107-w> (PMC5427850).
