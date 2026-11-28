# Group privacy for Gaussian differential privacy

If a mechanism is $\mu$-GDP with respect to datasets differing in one record, then for every $k \ge 1$ it is $k\mu$-GDP with respect to datasets differing in at most $k$ records. More generally, $f$-DP implies $\big(1 - (1 - f)^{\circ k}\big)$-DP for groups of size $k$, where $\circ k$ denotes $k$-fold composition of functions, and for $G_\mu$ this evaluates exactly to $G_{k\mu}$.

## Proof sketch

Connect two datasets $S_0, S_k$ at distance $k$ by a chain $S_0, S_1, \dots, S_k$ of neighbouring steps and fix a rejection rule $\phi$ with type I error $\alpha$ on $S_0$. Since $T(M(S_{j-1}), M(S_j)) \ge f$, the rejection probability on the next dataset satisfies $\mathbb{E}_{M(S_j)}[\phi] \le (1 - f)\bigl(\mathbb{E}_{M(S_{j-1})}[\phi]\bigr)$, and $1 - f$ is nondecreasing. By induction the rejection probability on $S_k$ is at most $(1 - f)^{\circ k}(\alpha)$, so the type II error at the endpoint is at least $1 - (1 - f)^{\circ k}(\alpha)$. The induction propagates the bound on the rejection probability, not iterates of $1 - G_\mu(1 - \cdot)$. For Gaussians, $(1 - G_\mu)(\alpha) = \Phi\bigl(\Phi^{-1}(\alpha) + \mu\bigr)$ is a shift by $\mu$ in the probit scale, so its $k$-fold composition is $\Phi\bigl(\Phi^{-1}(\alpha) + k\mu\bigr) = 1 - G_{k\mu}(\alpha)$.

## Depends on

- [Gaussian differential privacy](gaussian-differential-privacy.md)

## Sources

- J. Dong, A. Roth, W. J. Su, "Gaussian Differential Privacy", Journal of the Royal Statistical Society Series B 84 (2022), arXiv:1905.02383v3, Theorem 2.14.
