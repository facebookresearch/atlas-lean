# Statistical query lower bound from almost uncorrelated concepts

Let concepts $f_i \in C$, $i \in \kappa$, have pairwise correlations $|\mathrm{corr}_D(f_i, f_j)| \le \gamma$ under $D$, and let a learner learn $C$ under $D$ (statelessly) with tolerance $\tau \ge 0$ and error $\varepsilon \in [0, 1/2]$ using at most $q$ queries, where $\gamma < \tau^2$ and $\gamma < (1-2\varepsilon)^2$. Then

$$
|\kappa| \le \frac{q(1-\gamma)}{\tau^2 - \gamma} + \frac{1-\gamma}{(1-2\varepsilon)^2 - \gamma}.
$$

If only $\mathrm{corr}_D(f_i, f_j) \le \gamma$ is assumed, the same holds with $2q$ in place of $q$.

## Proof sketch

Write a query as $\phi(x, y) = g(x) + k(x)\,y^{\pm}$ with $|k| \le 1$ and answer it by $\mathbb{E}_D g$, ignoring the target. This answer is valid for every $f_i$ except those with $|\mathbb{E}_D[k f_i]| > \tau$, and Bessel's inequality for almost orthogonal vectors $(\sqrt{D(x)} f_i(x))_x$ bounds their number by $(1-\gamma)/(\tau^2 - \gamma)$. Running the learner against these answers, at most $q(1-\gamma)/(\tau^2-\gamma)$ concepts are exceptional, and the single output hypothesis must have correlation at least $1 - 2\varepsilon$ with all others, which by the same inequality bounds them by $(1-\gamma)/((1-2\varepsilon)^2 - \gamma)$.

## Depends on

- [Statistical query model with tolerance and the SQ dimension](statistical-query-dimension.md)

## Sources

- A. Blum, M. Furst, J. Jackson, M. Kearns, Y. Mansour and S. Rudich, "Weakly Learning DNF and Characterizing Statistical Query Learning Using Fourier Analysis", Proceedings of the Twenty-Sixth Annual ACM Symposium on Theory of Computing (STOC), 1994.
- B. Szorenyi, "Characterizing Statistical Query Learning: Simplified Notions and Proofs", Algorithmic Learning Theory (ALT), 2009.
- L. Reyzin, "Statistical Queries and Statistical Algorithms: Foundations and Applications", arXiv preprint, 2020.
