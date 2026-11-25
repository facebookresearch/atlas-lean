# Fisher's exact conditional law

Let $n_1, n_2 \in \mathbb{N}$, $p \in (0, 1)$, and let $X, Y$ be independent measurable $\mathbb{N}$-valued random variables on $(\Omega, \mu)$ with laws $\mathrm{Bin}(n_1, p)$ and $\mathrm{Bin}(n_2, p)$. Given the margin $X + Y = t$ with $t \le n_1 + n_2$, the cell $X$ is hypergeometric, whatever $p$: for every $k \in \mathbb{N}$,

$$\mu(X = k \mid X + Y = t) = \begin{cases} \dfrac{\binom{n_1}{k}\binom{n_2}{t - k}}{\binom{n_1 + n_2}{t}} & k \le t, \\[1ex] 0 & k > t. \end{cases}$$

## Sources

- R. A. Fisher, *Statistical Methods for Research Workers*, 5th ed., Oliver and Boyd, 1934, §21.02.
- R. A. Fisher, *The logic of inductive inference*, J. Roy. Statist. Soc. 98 (1935), 39–82.
- E. L. Lehmann and J. P. Romano, *Testing Statistical Hypotheses*, 3rd ed., Springer, 2005, §4.5.
