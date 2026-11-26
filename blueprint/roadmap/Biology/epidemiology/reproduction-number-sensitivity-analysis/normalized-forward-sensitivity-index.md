# Normalized forward sensitivity index

For a quantity $R_0(p_1,\dots,p_m)$ that depends differentiably on positive model parameters, the normalized forward sensitivity index (elasticity) of $R_0$ with respect to $p$ is
$$
\Upsilon^{R_0}_{p}=\frac{\partial R_0}{\partial p}\cdot\frac{p}{R_0}=\frac{\partial\ln R_0}{\partial\ln p}.
$$
It is dimensionless and gives the first-order relative change: $\Delta R_0/R_0\approx\Upsilon^{R_0}_p\,\Delta p/p$, so a $1\%$ increase in $p$ changes $R_0$ by about $\Upsilon^{R_0}_p\,\%$. Properties:

1. If $R_0=c\prod_i p_i^{e_i}$ is a monomial, then $\Upsilon^{R_0}_{p_i}=e_i$.
2. $\Upsilon^{R_0}_p$ is additive over products and quotients: $\Upsilon^{fg}_p=\Upsilon^f_p+\Upsilon^g_p$ and $\Upsilon^{f/g}_p=\Upsilon^f_p-\Upsilon^g_p$.
3. For a sum, $\Upsilon^{f+g}_p=\frac{f}{f+g}\Upsilon^f_p+\frac{g}{f+g}\Upsilon^g_p$.

For the SIQ model with $R_0=\dfrac{\Lambda\gamma(d_0+\mu+\sigma)}{d_0\big[(d_0+k)(d_0+\mu+\sigma)+\eta(d_0+\mu)\big]}$, property 1 gives $\Upsilon^{R_0}_\Lambda=\Upsilon^{R_0}_\gamma=1$, and the quotient rule gives
$$
\Upsilon^{R_0}_\sigma=\frac{\sigma}{d_0+\mu+\sigma}-\frac{\sigma(d_0+k)}{(d_0+k)(d_0+\mu+\sigma)+\eta(d_0+\mu)}=\frac{\sigma\,\eta(d_0+\mu)}{(d_0+\mu+\sigma)\big[(d_0+k)(d_0+\mu+\sigma)+\eta(d_0+\mu)\big]}>0 ,
$$
so a higher rate of return from quarantine to the infected class always raises $R_0$, while $\Upsilon^{R_0}_\eta<0$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

The index is the logarithmic derivative, which explains the product, quotient and sum rules. Parameters with the largest $|\Upsilon^{R_0}_p|$ are the most effective control targets, since equal relative changes in them move $R_0$ the most toward the threshold $1$. The indices are local: they depend on the baseline parameter values and do not capture interactions, for which global methods such as partial rank correlation are used.

## Sources

- A. Din, Y. Li, T. Khan, G. Zaman, "Mathematical analysis of spread and control of the novel corona virus (COVID-19) in China", *Chaos, Solitons & Fractals* 141 (2020) 110286. <https://doi.org/10.1016/j.chaos.2020.110286>. PMCID: PMC7510499. (Section 5.1, index $Z_\Pi=\frac{\Pi}{R_0}\frac{\partial R_0}{\partial\Pi}$.)
- N. Chitnis, J. M. Hyman, J. M. Cushing, "Determining important parameters in the spread of malaria through the sensitivity analysis of a mathematical model", *Bulletin of Mathematical Biology* 70 (2008) 1272–1296. <https://doi.org/10.1007/s11538-008-9299-0>
