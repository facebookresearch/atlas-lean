# Mutant fitness heterogeneity suppresses selection

In the large-population limit of the [Moran process with environment-dependent fitness](moran-process-with-environment-dependent-fitness.md), let the mutant rate have distribution $f$ with mean $\bar a$, let the resident mean rate be $\bar b$, and assume $\bar a > \bar b$. Then

$$\rho_A^\infty(f, g) \;\le\; 1 - \frac{\bar b}{\bar a} \;=\; \rho_A^\infty(\bar a, g),$$

with equality if and only if $f$ is a point mass (no mutant heterogeneity). Replacing the mutant's environmental rates by their spatial average can only raise the fixation probability of an advantageous mutant.

For weak heterogeneity, write $a = \bar a + \varepsilon a'$ with $\mathbb{E}_f[a'] = 0$ and the resident rates fixed. Then

$$\rho_A^\infty = \Big(1 - \frac{\bar b}{\bar a}\Big)\Big(1 - \frac{\bar b}{\bar a^{3}}\,\mathbb{E}_f[(a')^2]\,\varepsilon^2\Big) + O(\varepsilon^3),$$

so to leading order the loss is proportional to the variance of the mutant rate across sites. By contrast, heterogeneity in resident fitness leaves $\rho_A^\infty$ unchanged in large populations.

## Depends on

- [Moran process with environment-dependent fitness](moran-process-with-environment-dependent-fitness.md)
- [Large-population fixation probability in a heterogeneous environment](large-population-fixation-probability-in-a-heterogeneous-environment.md)

## Proof depends on

- [Jensen's inequality](../../../../MeasureTheory/integration/jensen-s-inequality-for-integrals/jensen-s-inequality/jensen-inequality.md)

## Expansion

Let $\rho = \rho_A^\infty(f,g) > 0$ and $\psi(a) = a/(\bar b + a\rho)$. Then $\psi''(a) = -2\bar b\rho/(\bar b + a\rho)^3 < 0$, so $\psi$ is strictly concave and Jensen's inequality gives $1 = \mathbb{E}_f[\psi(a)] \le \psi(\bar a) = \bar a/(\bar b + \bar a\rho)$, with equality iff $f$ is degenerate. Rearranging, $\rho \le 1 - \bar b/\bar a$. For the expansion, put $\rho = c_0 + c_2\varepsilon^2 + \dots$ in $\mathbb{E}[\psi(\bar a + \varepsilon a')] = 1$: the zeroth order gives $c_0 = 1 - \bar b/\bar a$; the first order vanishes because $\mathbb{E}[a'] = 0$; at second order, $\partial_\rho \psi(\bar a)|_{c_0} = -1$ and $\tfrac12\psi''(\bar a) = -\bar b c_0/\bar a^3$, giving $c_2 = -c_0\bar b\,\mathbb{E}[(a')^2]/\bar a^3$ (Eq. (3.6) of the source, which also lists the third- and fourth-order terms). The source shows numerically that restricting dispersal, for example to a cycle with periodic fitness, strengthens this suppression.

## Sources

- K. Kaveh, A. McAvoy, M. A. Nowak, "Environmental fitness heterogeneity in the Moran process", Royal Society Open Science (2019), <https://doi.org/10.1098/rsos.181661> (PMC6366185).
