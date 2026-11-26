# Statistical query model with tolerance and the SQ dimension

Fix a domain $X$, a distribution $D$ on $X$ and a target $c : X \to \{0,1\}$. A statistical query is a function $\phi : X \times \{0,1\} \to [-1, 1]$, with expectation $\mathbb{E}_{x \sim D}[\phi(x, c(x))]$; an oracle of tolerance $\tau \ge 0$ may answer any value within $\tau$ of it, possibly depending on earlier calls. A deterministic learner making at most $q$ queries learns a class $C$ under $D$ with tolerance $\tau$ and error $\varepsilon$ if for every $c \in C$ and every such oracle its hypothesis $h$ satisfies $\Pr_D[h \ne c] \le \varepsilon$ (stateless learning requires this only for oracles that answer each query by a fixed value). Reading concepts as $\pm 1$-valued functions, the correlation is $\mathrm{corr}_D(f, g) = \mathbb{E}_D[f g] = 1 - 2\Pr_D[f \ne g]$. The statistical query dimension $\mathrm{SQdim}_D(C)$ is the largest $d$ such that $C$ contains $d$ distinct concepts with pairwise $|\mathrm{corr}_D| \le 1/d$; the one-sided dimension $\mathrm{SQdim}^{+}_D(C)$ only requires $\mathrm{corr}_D \le 1/d$.

## Depends on

- [Statistical-query learning implies noise-tolerant PAC learning](../statistical-query-learning-implies-noise-tolerant-pac-learni.md)

## Sources

- M. Kearns, "Efficient Noise-Tolerant Learning from Statistical Queries", Journal of the ACM, 1998.
- A. Blum, M. Furst, J. Jackson, M. Kearns, Y. Mansour and S. Rudich, "Weakly Learning DNF and Characterizing Statistical Query Learning Using Fourier Analysis", Proceedings of the Twenty-Sixth Annual ACM Symposium on Theory of Computing (STOC), 1994.
- L. Reyzin, "Statistical Queries and Statistical Algorithms: Foundations and Applications", arXiv preprint, 2020.
