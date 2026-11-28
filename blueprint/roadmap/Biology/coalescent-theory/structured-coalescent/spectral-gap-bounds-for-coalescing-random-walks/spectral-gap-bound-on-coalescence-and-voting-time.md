# Spectral-gap bound on the coalescence time of random walks and the voter model

Let $G = (V,E)$ be a connected undirected graph with $n$ vertices, $m$ edges, maximum degree $\Delta$ and degrees $d(v)$. Let $1 - \lambda_2$ be the eigenvalue gap of the lazy random walk on $G$, and set

$$
\nu = \frac{n \sum_{v \in V} d(v)^2}{(2m)^2} \ \ (\ge 1, \text{ with equality for regular graphs}).
$$

In **coalescing random walks**, one particle starts at every vertex and each makes an independent lazy random walk; particles that meet at a vertex merge. The **coalescence time** $C(n)$ is the expected time until one particle remains. By duality, this equals the expected time for the discrete-time voter model, started with distinct opinions, to reach consensus. It is also the time back to the most recent common ancestor of a neutral haploid population on $G$.

**Theorem (coalescence time).**

$$
C(n) = O\left( \frac{1}{1 - \lambda_2} \Big( \log^4 n + \frac{n}{\nu} \Big) \right),
$$

and the expected completion time of voting on $G$ obeys the same bound.

**Theorem (first meeting of $k$ walks).** Let $k^* = \max\{2, \min\{(n/\nu)^{1/2}, m/(2\Delta), \log n\}\}$. For $2 \le k \le k^*$ particles started from arbitrary vertices, the expected time $M_k$ until two of them first meet satisfies

$$
\mathbb{E}(M_k) = O\left( \frac{1}{1 - \lambda_2} \Big( k \log n + \frac{n}{\nu k^2} \Big) \right).
$$

For expanders ($1 - \lambda_2 = \Omega(1)$) of bounded degree ratio this gives $C(n) = O(n)$.

## Depends on

- [Coalescing random walks dual to the voter model on a finite graph](../coalescing-random-walks-dual-to-the-voter-moran.md)
- [Spectral gap of a finite Markov kernel, in Dirichlet-form terms](../../../../Probability/markov-chains/dirichlet-forms/spectral-gap.md)

## Expansion

The $k$ walks are viewed as one walk on the product graph $Q = G^k$. Contracting the set $S_k$ of states in which some two walks coincide into a single vertex $\gamma$ gives a graph $\Gamma$. All three graphs have mixing times $O(k \log n/(1 - \lambda_2))$, and the stationary mass of $\gamma$ is at least $k^2\nu/(8n)$ for $k \le k^*$. The hitting time of a vertex $v$ from stationarity is at most $Z_{vv}/\pi_v \le 1/((1-\lambda_2)\pi_v)$, which gives the meeting bound. The coalescence bound is obtained by applying the meeting-time estimate repeatedly while the number of surviving particles shrinks: when many particles remain, meetings are frequent, so the total time is dominated by a geometric-type sum giving the $n/\nu$ term, with the polylogarithmic term coming from mixing overheads.

## Sources

- Colin Cooper, Robert Elsässer, Hirotaka Ono and Tomasz Radzik, *Coalescing random walks and voting on connected graphs*, SIAM J. Discrete Math. 27(4) (2013), 1748–1758. <https://doi.org/10.1137/120900368> Theorem 1, Theorem 2, Lemmas 1–4. Locators use the numbering of the preprint arXiv:1204.4106.
