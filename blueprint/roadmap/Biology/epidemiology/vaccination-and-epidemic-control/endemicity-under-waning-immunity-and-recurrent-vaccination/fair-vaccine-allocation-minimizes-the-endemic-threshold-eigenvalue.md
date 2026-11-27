# Fair vaccine allocation minimizes the endemic-threshold eigenvalue in a two-group model

**Setting.** Extend the [reinfection model with waning immunity and recurrent vaccination](endemic-threshold-and-mean-stationary-susceptibility.md) to $L$ groups with population fractions $p_\ell$, an irreducible symmetric contact matrix $\Gamma = (\gamma_{\ell\ell'})$ and group-specific inter-dose times $T_\ell$. With the same law of susceptibility curves $\sigma$ in all groups, the mean susceptibility of group $\ell$ at the disease-free equilibrium is $\Sigma_\ell = \mathbb{E}[\int_0^{T_\ell}\sigma(a)\,da]/\mathbb{E}[T_\ell]$, and an infective of group $\ell$ causes on average $R_0 m_{\ell\ell'}$ infections in group $\ell'$, with

$$
m_{\ell\ell'} = p_{\ell'}\,\gamma_{\ell\ell'}\,\Sigma_{\ell'} .
$$

The early epidemic is a multitype branching process with mean matrix $R_0 M$, which survives with positive probability iff $R_0\rho > 1$, $\rho$ the leading eigenvalue of $M$.

For $L = 2$ with equal activity levels ($\sum_{\ell'} p_{\ell'}\gamma_{\ell\ell'} = 1$) all symmetric contact matrices are

$$
\Gamma = \begin{pmatrix} \frac{1}{p_1}(1 - p_2\alpha) & \alpha \\ \alpha & \frac{1}{p_2}(1 - p_1\alpha) \end{pmatrix}, \qquad \alpha \in \Bigl[0, \min\bigl(\tfrac{1}{p_1}, \tfrac{1}{p_2}\bigr)\Bigr],
$$

assortative for $\alpha < 1$, well mixed for $\alpha = 1$, disassortative for $\alpha > 1$, and

$$
\rho(\alpha) = \tfrac12\bigl((1-p_2\alpha)\Sigma_1 + (1-p_1\alpha)\Sigma_2\bigr) + \tfrac12\sqrt{\bigl((1-p_2\alpha)\Sigma_1 + (1-p_1\alpha)\Sigma_2\bigr)^2 - 4(1-\alpha)\Sigma_1\Sigma_2}.
$$

**Statement.**

1. *Assortativity.* If $\Sigma_1 = \Sigma_2$ then $\rho = \Sigma_1$ for every $\alpha$. For any $\Sigma_1, \Sigma_2$, $\alpha \mapsto \rho(\alpha)$ is non-increasing and convex, so less assortative mixing makes endemicity harder.
2. *Fair allocation.* Fix a dose budget: $p_1/\mathbb{E}[T_1] + p_2/\mathbb{E}[T_2] = 1/m$. Parametrize allocations by a fairness parameter $\beta \in [-1/p_2, 1/p_1]$ via $T_1(\beta) = T/(1+\beta p_2)$, $T_2(\beta) = T/(1-\beta p_1)$ for a fixed random $T$ with $\mathbb{E}[T] = m$. Then for every $\alpha \in [0,1]$ (assortative or well-mixed contacts), $\beta \mapsto \rho(\beta)$ is minimized at $\beta = 0$: splitting doses evenly between groups minimizes the endemic threshold eigenvalue.
3. *Vaccine hesitancy.* If only group 1 is vaccinated (mean susceptibility $\Sigma$), group 2 not ($\Sigma_2 = 1$), and mixing is homogeneous ($\alpha = 1$), then $\rho = 1 - (1-\Sigma)p_1$, and endemicity is prevented ($R_0\rho \le 1$) iff

$$
p_1 \ge p_c = \frac{1 - 1/R_0}{1 - \Sigma},
$$

the analogue of the classical critical coverage $(1 - 1/R_0)/E$ with vaccine efficacy $E$ replaced by $1 - \Sigma$.

## Depends on

- [Endemic threshold of a reinfection model with waning immunity and recurrent vaccination](endemic-threshold-and-mean-stationary-susceptibility.md)
- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof sketch

When $\Sigma_1 = \Sigma_2$, $M$ is $\Sigma_1$ times a stochastic matrix, so $\rho = \Sigma_1$. Otherwise write $2\rho = (\Sigma_1 + \Sigma_2 - \bar\Sigma\alpha) + \sqrt{z(\alpha)}$ with $\bar\Sigma = p_2\Sigma_1 + p_1\Sigma_2$; a direct computation gives $2z''z - z'^2 = 16p_1p_2(\Sigma_1 - \Sigma_2)^2 > 0$, so $\rho'$ is increasing, and since $\rho' \to 0$ as $\alpha \to \infty$, $\rho' < 0$. For fair allocation, item 1 gives $\rho(\alpha,\beta) \ge \rho(1,\beta) = p_1\Sigma_1(\beta) + p_2\Sigma_2(\beta)$ for $\alpha \le 1$. With $\phi(a) = \int_0^a\sigma$ convex and the dose constraint making the weights $p_\ell\mathbb{E}[T]/\mathbb{E}[T_\ell(\beta)]$ sum to one, Jensen's inequality yields $\rho(1,\beta) \ge \mathbb{E}[\phi(T)]/\mathbb{E}[T] = \rho(\alpha, 0)$, the last equality because $M$ is again a multiple of a stochastic matrix at $\beta = 0$.

## Sources

- Félix Foutel-Rodier, Arthur Charpentier and Hélène Guérin, "Optimal vaccination policy to prevent endemicity: a stochastic model", *Journal of Mathematical Biology* 90 (2025), 10, <https://doi.org/10.1007/s00285-024-02171-z>. Preprint version: arXiv:2306.13633 (2023), Section 5, Propositions 5 and 6 and the critical fraction $p_c$, <https://doi.org/10.48550/arXiv.2306.13633>.
