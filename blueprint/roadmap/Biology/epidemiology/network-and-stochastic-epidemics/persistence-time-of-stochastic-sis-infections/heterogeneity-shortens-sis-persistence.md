# Heterogeneity shortens SIS persistence

Use the separable-mixing $k$-group stochastic SIS model and the notation of [the persistence-time exponent](persistence-time-exponent-under-one-sided-heterogeneity.md). For a probability vector $p$ and positive vectors $x, x'$, say $x \prec_p x'$ ($x$ is $p$-majorized by $x'$) if there is a permutation $\sigma$ ordering both vectors decreasingly with $\sum_i p_i x_i = \sum_i p_i x'_i$ and $\sum_{i=1}^{j} p_{\sigma(i)}x_{\sigma(i)} \le \sum_{i=1}^{j} p_{\sigma(i)}x'_{\sigma(i)}$ for $j = 1,\dots,k-1$; intuitively $x'$ is more heterogeneous.

**Theorem.** Consider two populations with the same $\beta$, $\gamma$ and group structure $f$, and let $\tau^{(1)}, \tau^{(2)}$ be their mean persistence times from quasi-stationarity, with $R_0 > 1$.
1. With heterogeneity in infectivity alone, $\lambda^{(1)} \prec_f \lambda^{(2)}$ implies $\lim_N \ln\tau^{(1)}/N \ge \lim_N \ln\tau^{(2)}/N$.
2. With heterogeneity in susceptibility alone, $\mu^{(1)} \prec_f \mu^{(2)}$ implies the same inequality.

In particular, for one-sided heterogeneity the exponent $\lim_N \ln\tau/N$ is maximized by the homogeneous population. On a directed configuration network with fixed in-degree, an out-degree distribution smaller in the convex order gives a larger exponent, so the exponent is maximal when every individual has the same out-degree (and symmetrically for in-degree).

## Depends on

- [Persistence-time exponent of the SIS model under one-sided heterogeneity](persistence-time-exponent-under-one-sided-heterogeneity.md)

## Expansion

For infectivity heterogeneity, $h(x) = x/(1 + xD(\lambda^{(1)}))$ is concave, so majorization gives $\sum_i f_i h(\lambda^{(2)}_i) \le \sum_i f_i h(\lambda^{(1)}_i) = \gamma/\beta$; since $z \mapsto \sum_i f_i\lambda_i/(1+\lambda_i z)$ decreases, $D(\lambda^{(1)}) \ge D(\lambda^{(2)})$. Writing $\psi(z) = \sum_i f_i\ln(1+\lambda^{(1)}_i z) - \gamma z/\beta$, one has $\psi' > 0$ on $(0, D(\lambda^{(1)}))$, so $\psi(D(\lambda^{(2)})) \le \psi(D(\lambda^{(1)})) = A^{(1)}$. Concavity of $x \mapsto \ln(1 + D(\lambda^{(2)})x)$ and majorization give $\sum_i f_i\ln(1+\lambda^{(2)}_i D(\lambda^{(2)})) \le \sum_i f_i\ln(1+\lambda^{(1)}_i D(\lambda^{(2)}))$, and combining the two inequalities yields $A^{(2)} \le A^{(1)}$. Susceptibility follows by interchanging $\lambda$ and $\mu$.

## Sources

- D. Clancy, "Persistence time of SIS infections in heterogeneous populations and networks", Journal of Mathematical Biology (2018), Sect. 5, Theorem 2 and Theorem 4(ii), <https://doi.org/10.1007/s00285-018-1222-1>, PMCID PMC6132977.
