# Contact processes on power-law random graphs have critical value zero

Let $G_n$ be a Newman–Strogatz–Watts random graph (configuration model) on $\{1, \dots, n\}$ whose degrees satisfy $P(d_i = k) \sim Ck^{-\alpha}$ as $k \to \infty$ for some $C > 0$ and $\alpha > 3$, and $P(d_i \le 2) = 0$. Let $\xi^1_t$ be the contact process on $G_n$ with infection rate $\lambda$ and recovery rate $1$, started with every vertex infected. Chatterjee and Durrett (2009, Theorem 1) prove that for every $\lambda > 0$ there is $p(\lambda) > 0$ such that for every $\delta > 0$,
$$\inf_{t \le \exp(n^{1-\delta})} P\bigl(|\xi^1_t|/n \ge p(\lambda)\bigr) \to 1 \quad (n \to \infty).$$
So for every positive infection rate the process keeps a positive density of infected vertices for a time at least $\exp(n^{1-\delta})$: the critical value is $0$ for every $\alpha > 3$, whereas mean-field calculations suggest a positive critical value in this range (abstract of the source).

## Expansion

1. The model: the configuration model with power-law degrees, the condition $P(d_i \le 2) = 0$, which makes $G_n$ connected with high probability and of diameter at most $(1 + \varepsilon)\log n/\log\nu$ with probability tending to $1$, for every $\varepsilon > 0$ (Lemma 1.2; here the size-biased mean $\nu$ is finite), and the contact process.
2. Survival on a star: on a star with $k$ leaves and $k\lambda^2 \to \infty$, the infection started at the centre survives until time $\exp(k\lambda^2/10)$ with probability tending to $1$ (Lemma 1.1, after Berger et al.).
3. Transmission of the infection between high-degree vertices through short paths, and the bootstrapping argument giving a positive density.
4. The lower bound on the survival time and the conclusion $\lambda_c = 0$; the quasi-stationary density $\rho(\lambda)$ and the bounds $\alpha - 1 \le \beta \le 2\alpha - 3$ on its exponent, as separate statements.

## Sources

- S. Chatterjee and R. Durrett, Contact processes on random graphs with power law degree distributions have critical value 0, Ann. Probab. 37 (2009), 2332–2356, Theorem 1 and Lemmas 1.1–1.2. <https://arxiv.org/abs/0912.1699>
