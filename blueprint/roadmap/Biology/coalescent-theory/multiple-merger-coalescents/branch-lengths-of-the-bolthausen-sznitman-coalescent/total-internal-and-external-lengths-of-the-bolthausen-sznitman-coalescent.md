# Total internal and external lengths of the Bolthausen–Sznitman coalescent

**Setting.** The Bolthausen–Sznitman coalescent restricted to $n$ individuals is the $\Lambda$-coalescent with $\Lambda$ uniform on $[0,1]$, whose [merger rates](../../coalescents/merger-rate-volume.md) $\lambda_{b,k}$ give, when there are $b$ blocks, the total merger rate $\lambda_b = \sum_{k=2}^{b}\binom bk\lambda_{b,k} = b - 1$. It arises as the genealogy of populations under strong selection (for example rapidly adapting populations and branching random walks with selection). Let $L^{(n)}$, $E^{(n)}$ and $I^{(n)} = L^{(n)} - E^{(n)}$ be the total, total external and total internal branch lengths of the $n$-coalescent tree. Let $Z$ be the strictly $1$-stable random variable with characteristic exponent

$$-\log\mathbb E\bigl[e^{i\theta Z}\bigr] = \frac\pi2|\theta| - i\theta\log|\theta|, \qquad \theta \in \mathbb R .$$

**Theorem.**

1. (Internal length.) $\dfrac{(\log n)^2}{n}\,I^{(n)} \xrightarrow{\ \mathbb P\ } 1$.
2. (External length.)

$$\frac{(\log n)^2}{n}\,E^{(n)} - \log n - \log\log n \xrightarrow{\ d\ } Z - 1 .$$

Since the total length satisfies $\frac{(\log n)^2}{n}L^{(n)} - \log n - \log\log n \Rightarrow Z$, the external length carries the stable fluctuations, while the internal length, although of the same order $n/(\log n)^2$ as the correction term, is asymptotically deterministic. This explains the shift by $-1$.

3. (Mutations.) If mutations fall on the tree as a Poisson process of rate $\mu$ per unit branch length, then the numbers $M_I^{(n)}$ of internal mutations (shared by at least two sampled individuals) and $M_E^{(n)}$ of external mutations (singletons) satisfy

$$\frac{(\log n)^2}{n}M_I^{(n)} \xrightarrow{\ \mathbb P\ } \mu, \qquad \frac{(\log n)^2}{n}M_E^{(n)} - \mu\log n - \mu\log\log n \xrightarrow{\ d\ } \mu(Z - 1).$$

## Depends on

- [Merger rates of the Bolthausen–Sznitman coalescent](../../coalescents/merger-rate-volume.md)

## Expansion

Given $b$ blocks, the number $U$ of blocks lost at the next merger has law $\mathbb P(U = l) = \frac{b}{b-1}\frac{1}{l(l+1)}$, which is heavy-tailed. The number of collision events $\tau_n$ satisfies the same stable limit as $L^{(n)}$. Writing $I^{(n)} = \sum_{k<\tau_n} Y_k\,\mathbf e_k/(X_k - 1)$, with $X_k$ the number of blocks and $Y_k$ the number of internal blocks after $k$ mergers, the proof shows that $Y_k/X_k$ follows a deterministic profile on the relevant time scale. Before time $\theta_n^{(\gamma)}$, the time at which $X_k$ drops to order $n/(\log n)^\gamma$, the increments of $X$ are of size about $X/\log n$ (a concentration estimate). Summing gives $(\log n)^2 I^{(n)}/n \to 1$, and subtracting from the known limit of $L^{(n)}$ gives the law of $E^{(n)}$. The mutation counts follow because a Poisson process time-changed by a length that diverges obeys a law of large numbers.

## Sources

- Götz Kersting, Juan Carlos Pardo, Arno Siri-Jégousse, "Total internal and external lengths of the Bolthausen-Sznitman coalescent", *Journal of Applied Probability* 51A (2014), 73–86, <https://doi.org/10.1239/jap/1417528468>; preprint arXiv:1302.1463, <https://doi.org/10.48550/arXiv.1302.1463>. Numbering of the arXiv version: Section 1 (Theorem 1.1, Corollary 1.2), Section 2 (Proposition 2.2), Section 3 (Proposition 3.1).
