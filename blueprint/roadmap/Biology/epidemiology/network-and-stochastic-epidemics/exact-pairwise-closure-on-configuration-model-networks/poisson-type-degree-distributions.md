# Poisson-type degree distributions

Let $\psi(u) = \sum_{k\ge 0} p_k u^k$ be the probability generating function (PGF) of a random variable on $\mathbb{Z}_{\ge 0}$, so $\psi(1) = 1$. Say the variable is *Poisson-type* (PT) if its PGF solves

$$\psi'(u) = \alpha\,\psi(u)^{\kappa}$$

for some constants $\alpha > 0$, $\kappa \ge 0$.

**Theorem.** A PGF satisfies $\psi' = \alpha\psi^\kappa$ if and only if the distribution is one of:

| condition | family | parameters |
|---|---|---|
| $\kappa \in [0,1)$ | binomial $\mathrm{Bin}(n,p)$ | $n = 1/(1-\kappa) \in \mathbb{Z}_{>0}$, $p = \alpha(1-\kappa) \le 1$ (the case $\kappa = 0$ is $n = 1$, $p = \alpha$) |
| $\kappa = 1$ | Poisson $\mathrm{Poi}(\lambda)$ | $\lambda = \alpha$ |
| $\kappa > 1$ | negative binomial $\mathrm{NB}(r,p)$ | $r = 1/(\kappa-1)$, $p = \alpha(\kappa-1)/(\alpha(\kappa-1)+1)$ |

Equivalently, when $\psi(0) > 0$ and $\psi'(0) > 0$, the PT laws are exactly those with

$$\frac{\psi''(u)\,\psi(u)}{\psi'(u)^2} = \kappa \quad\text{constant on } [0,1],$$

and the constant is $\kappa = (n-1)/n$ (so $\kappa = 0$ for $\mathrm{Bin}(1,p)$), $1$, $(r+1)/r$ for the three families respectively.

## Expansion

If $\psi''\psi/\psi'^2 = \kappa$ then $\psi''/\psi' = \kappa\,\psi'/\psi$; integrating gives $\psi' = \alpha\psi^\kappa$. For $\kappa = 1$ this with $\psi(1) = 1$ gives $\psi(u) = e^{\alpha(u-1)}$. For $\kappa \ne 1$, separation of variables yields $\psi(u) = [\alpha(1-\kappa)(u-1) + 1]^{1/(1-\kappa)}$. When $\kappa < 1$, nonnegativity of all derivatives at $0$ forces $1/(1-\kappa)$ to be a positive integer and $\alpha(1-\kappa) \le 1$, giving $(1-p+pu)^n$ (the degenerate case $p = 1$ is the $n$-regular graph, $\psi = u^n$). When $\kappa > 1$ the expression is $\big((1-p)/(1-pu)\big)^r$ with $p < 1$.

## Sources

- I. Z. Kiss, E. Kenah, G. A. Rempała, "Necessary and sufficient conditions for exact closures of epidemic equations on configuration model networks", Journal of Mathematical Biology (2023), Eqs. (17)–(23), Table 1 and Theorem 1, <https://doi.org/10.1007/s00285-023-01967-9>, PMCID PMC10397147.
