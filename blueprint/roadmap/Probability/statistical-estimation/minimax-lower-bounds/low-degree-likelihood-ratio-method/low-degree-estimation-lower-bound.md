# Low-degree lower bounds for estimation and recovery

In the additive Gaussian model $Y = X + Z$, with $Z \sim \mathcal{N}(0, I_N)$ independent of $X$, let $x = x(X)$ be a scalar with $\mathbb{E}[x^2] < \infty$ and assume $\mathbb{E}|X_i|^{2D} < \infty$ for every $i$. Then every $f \in \mathbb{R}[Y]_{\le D}$ has $\mathbb{E}[f(Y)^2]$ finite, and positive unless $f = 0$ since $Y$ has a density, and the mixed moments $\mathbb{E}[x X^\alpha]$ and $\mathbb{E}[X^\alpha]$ with $|\alpha| \le D$ are finite; these hypotheses exclude, for example, $x = 1/X_1$ with $X_1$ uniform on $(0, 1)$, which has no finite mean. With $\mathrm{Corr}_{\le D} = \sup\{\mathbb{E}[f(Y)\,x]/\sqrt{\mathbb{E}[f(Y)^2]} : f \in \mathbb{R}[Y]_{\le D},\ f \ne 0\}$, the best degree-$D$ polynomial estimator of $x$ satisfies

$$
\inf_{f \in \mathbb{R}[Y]_{\le D}} \mathbb{E}\big[(f(Y) - x)^2\big] = \mathbb{E}[x^2] - \mathrm{Corr}_{\le D}^2, \qquad \mathrm{Corr}_{\le D}^2 \le \sum_{|\alpha| \le D} \frac{\kappa_\alpha^2}{\alpha!},
$$

where $\kappa_\alpha = \mathbb{E}[x X^\alpha] - \sum_{\beta \le \alpha,\, \beta \ne \alpha} \kappa_\beta \binom{\alpha}{\beta} \mathbb{E}[X^{\alpha - \beta}]$ with $\binom{\alpha}{\beta} = \prod_i \binom{\alpha_i}{\beta_i}$ (so $\kappa_0 = \mathbb{E}[x]$), the joint cumulant of $x$ and $\alpha_i$ copies of $X_i$ for each $i$ (Schramm-Wein, Theorem 2.2). As applications, the low-degree minimum mean squared error is characterized for planted submatrix and planted dense subgraph recovery, including regimes where detection is easy (for example by summing all entries) but low-degree polynomials cannot recover the planted support, giving the first low-degree hardness results for recovery problems whose detection problem is easy.

## Proof sketch

The optimal degree-$D$ estimator is the projection of $x$ onto low-degree polynomials of $Y$ in $L^2(\mathbb{P})$, and $\mathrm{Corr}_{\le D} = \sup_f \mathbb{E}[f(Y)x]/\sqrt{\mathbb{E}f(Y)^2}$. Expanding $f$ in Hermite polynomials of $Y$, $\mathbb{E}[h_\alpha(Y)x]$ equals $\mathbb{E}[X^\alpha x]$, while $\mathbb{E}[f(Y)^2]$ is lower bounded by a quadratic form whose inverse, combined with a Möbius-inversion argument, replaces moments by cumulants and yields the stated bound.

## Depends on

- [Low-degree advantage of the additive Gaussian model](additive-gaussian-low-degree-advantage.md)

## Sources

- T. Schramm, A. S. Wein, "Computational Barriers to Estimation from Low-Degree Polynomials", Annals of Statistics 50 (2022), arXiv:2008.02269.
