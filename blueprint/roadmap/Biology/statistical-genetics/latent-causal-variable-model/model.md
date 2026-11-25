# Latent causal variable model

Let $P$ be a measure on a measurable space $\Omega$. A latent causal variable model consists of real numbers $q_1, q_2$ (the normalized effects of the latent variable on the two traits) and real functions $\pi, \gamma_1, \gamma_2$ on $\Omega$ (the effect of a SNP on the latent variable and its non-mediated effects on the two traits) such that

- $\pi$, $\gamma_1$ and $\gamma_2$ have finite fourth moments with respect to $P$;
- $\pi$ is independent of the pair $(\gamma_1, \gamma_2)$ under $P$;
- $(\gamma_1, \gamma_2)$ has the same law under $P$ as $(-\gamma_1, \gamma_2)$ and as $(\gamma_1, -\gamma_2)$;
- $\int \pi \, dP = 0$ and $\int \pi^2 \, dP = 1$;
- $\int (q_1 \pi + \gamma_1)^2 \, dP = 1$ and $\int (q_2 \pi + \gamma_2)^2 \, dP = 1$.

The marginal effects of the SNP on the two traits are $\alpha_k = q_k \pi + \gamma_k$. This is the model of O'Connor and Price (2018); all results about it assume that $P$ is a probability measure.

## Sources

- L. J. O'Connor, A. L. Price, *Distinguishing genetic correlation from causation across 52 diseases and complex traits*, Nat. Genet. 50 (2018), 1728–1734.
