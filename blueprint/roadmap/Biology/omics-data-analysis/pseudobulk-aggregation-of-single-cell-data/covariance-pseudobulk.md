# Pseudobulk values are uncorrelated replicates

Let $\delta$ be a set of donors and $\kappa$ a finite nonempty set of $m$ cell slots. Let $\mu$ be a
finite measure on $\Omega$ and let the cell values $Y_i : \Omega \to \mathbb{R}$ form a
[random-intercept model](is-random-intercept.md) under $\mu$ with donor variance $\sigma_b^2$ and
residual variance $\sigma_e^2$, covariances being taken with respect to $\mu$. Then the
[pseudobulk values](pseudobulk.md) $\bar Y_d$ of the donors satisfy

$$
\mathrm{Cov}(\bar Y_d, \bar Y_{d'}) = \begin{cases}
\sigma_b^2 + \sigma_e^2 / m & d = d', \\
0 & d \ne d'.
\end{cases}
$$

Distinct donors' pseudobulk values are uncorrelated, with common variance
$\sigma_b^2 + \sigma_e^2 / m$.
