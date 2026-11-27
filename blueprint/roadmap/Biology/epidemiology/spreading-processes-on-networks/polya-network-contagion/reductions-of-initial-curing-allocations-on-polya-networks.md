# Reductions of initial curing allocations on Pólya contagion networks

**Setting.** Consider the [Pólya network contagion process](minimax-curing-game-on-polya-network-contagion.md) on a connected undirected graph $G = (V, E)$ with closed neighbourhoods $\mathcal{N}_i'$, initial red balls $\mathbf{R} = (R_1, \dots, R_N)$ and black balls $\mathbf{B} = (B_1, \dots, B_N)$, and average infection rate $\tilde I_n = \frac{1}{N}\sum_i P(Z_{i,n} = 1)$. At time $1$,

$$
\tilde I_1 = \frac{1}{N}\sum_{k=1}^{N} \frac{\bar R_k}{\bar R_k + \bar B_k}, \qquad \bar R_k = \sum_{j \in \mathcal{N}_k'} R_j,\quad \bar B_k = \sum_{j \in \mathcal{N}_k'} B_j.
$$

The initialization problem allocates a fixed budget of black balls (curing) to minimize $\tilde I_n$, or a fixed budget of red balls to maximize it.

**Theorem (outer nodes can be ignored).** If $\mathcal{N}_i' \subset \mathcal{N}_j'$ for nodes $i, j$, then, when minimizing $\tilde I_n$ over the curing initialization, one may assume $B_i = 0$; likewise one may assume $R_i = 0$ when maximizing $\tilde I_n$ over the infection initialization. Moving node $i$'s balls to node $j$ never worsens the objective.

**Theorem (symmetrization over an automorphism).** Let $\sigma$ be a graph automorphism of $G$ generating a cyclic group of order $m$, and suppose $R_i = R_{\sigma(i)}$ for all $i$. Define the averaged curing initialization $B_i^* = \frac{1}{m}\sum_{j=1}^{m} B_{\sigma^j(i)}$. Then $\tilde I_1^* \le \tilde I_1$: averaging black balls along the orbits of $\sigma$ does not increase the time-1 infection rate.

**Proposition (convexity at time 1).** If $\bar R_i > 0$ for every $i$, then $\tilde I_1$ is convex in $\mathbf{B}$, and the feasible set $\{\mathbf{B} \in \mathbb{R}_{\ge 0}^N : \sum_i B_i = \mathcal{B}_b\}$ is convex and compact, so projected gradient descent converges to an optimal curing initialization.

## Depends on

- [Minimax curing game on the Pólya network contagion process](minimax-curing-game-on-polya-network-contagion.md)

## Expansion

For the outer-node result at time $1$, moving $B_i$ into $B_j$ leaves $\bar B_k$ unchanged for $k \in \mathcal{N}_i'$ (both nodes lie in its super urn), increases it for $k \in \mathcal{N}_j' \setminus \mathcal{N}_i'$, and leaves the rest alone, so every term of $\tilde I_1$ weakly decreases. For later times a coupling lemma shows that red draws raise every later conditional infection probability (monotonicity of the process in past draws), and a pathwise comparison of super-urn proportions extends the conclusion to $\tilde I_n$. For symmetrization, each term $\bar R_k/(\bar R_k + \bar B_k)$ is convex in $\bar B_k$ and $\bar R$ is constant on $\sigma$-orbits, so Jensen's inequality on the orbit average gives the bound.

## Sources

- Greg Harrington, Fady Alajaji, Bahman Gharesifard, "Initialization and Curing Policies for Pólya Contagion Networks", SIAM Journal on Control and Optimization 60 (2022), S170–S195, <https://doi.org/10.1137/20m1358803>. Published version of arXiv:2008.01782, cited next; locators there refer to the arXiv version.
- Greg Harrington, Fady Alajaji, Bahman Gharesifard, *Initialization and Curing Policies for Polya Contagion Networks*, arXiv 2020. Lemma 1 and Theorem 1 (outer nodes), Lemma 4 and Theorem 2 (automorphism averaging), Proposition 1 (gradient descent conditions), Section 3. <https://doi.org/10.48550/arXiv.2008.01782>
