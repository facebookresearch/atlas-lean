# Low-degree lower bounds for estimation and recovery

In the additive Gaussian model $Y = X + Z$, the best degree-$D$ polynomial estimator of a scalar quantity $x = x(X)$ satisfies

$$
\inf_{f \in \mathbb{R}[Y]_{\le D}} \mathbb{E}\big[(f(Y) - x)^2\big] = \mathbb{E}[x^2] - \mathrm{Corr}_{\le D}^2, \qquad \mathrm{Corr}_{\le D}^2 \le \sum_{|\alpha| \le D} \frac{\kappa_\alpha^2}{\alpha!},
$$

where $\kappa_\alpha$ is the joint cumulant of $x$ and the coordinates of $X$ indexed by the multiset $\alpha$. As applications, the low-degree minimum mean squared error is characterized for planted submatrix and planted dense subgraph recovery, including regimes where detection is easy (for example by summing all entries) but low-degree polynomials cannot recover the planted support, giving the first low-degree hardness results for recovery problems whose detection problem is easy.

## Proof sketch

The optimal degree-$D$ estimator is the projection of $x$ onto low-degree polynomials of $Y$ in $L^2(\mathbb{P})$, and $\mathrm{Corr}_{\le D} = \sup_f \mathbb{E}[f(Y)x]/\sqrt{\mathbb{E}f(Y)^2}$. Expanding $f$ in Hermite polynomials of $Y$, $\mathbb{E}[h_\alpha(Y)x]$ equals $\mathbb{E}[X^\alpha x]$, while $\mathbb{E}[f(Y)^2]$ is lower bounded by a quadratic form whose inverse, combined with a Möbius-inversion argument, replaces moments by cumulants and yields the stated bound.

## Depends on

- [Low-degree advantage of the additive Gaussian model](additive-gaussian-low-degree-advantage.md)

## Sources

- T. Schramm, A. S. Wein, "Computational Barriers to Estimation from Low-Degree Polynomials", Annals of Statistics 50 (2022), arXiv:2008.02269.
