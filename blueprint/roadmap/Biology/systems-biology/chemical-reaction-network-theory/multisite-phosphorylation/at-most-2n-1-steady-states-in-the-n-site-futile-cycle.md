# Number of steady states of the multisite futile cycle

For the mass action model $\Sigma(\kappa, C)$ of the $n$-site sequential distributive phosphorylation–dephosphorylation cycle, with kinetic constants $\kappa$ and conserved totals $C = (E_{tot}, F_{tot}, S_{tot})$ of kinase, phosphatase and substrate, Wang and Sontag (2008, Theorem 3) prove that for every $\kappa$ and $C$ the system has at most $2n - 1$ positive steady states; for $n = 2$ this gives at most three. They also prove (Theorem 1) that for each $S_{tot}$ and ratio of the enzyme totals there are kinetic constants and a threshold such that, when the enzyme totals are small enough relative to the substrate, the system has at least $n + 1$ positive steady states for $n$ even and at least $n$ for $n$ odd; and they bound the number in two regimes, for $\gamma > 0$ and kinetic constants with $\varphi_1^\kappa(\gamma) \ne \varphi_2^\kappa(\gamma)$. Here, writing $k_{\mathrm{on}_i}, k_{\mathrm{off}_i}, k_{\mathrm{cat}_i}$ and $l_{\mathrm{on}_i}, l_{\mathrm{off}_i}, l_{\mathrm{cat}_i}$ ($i = 0, \dots, n - 1$) for the binding, unbinding and catalytic constants of the kinase and phosphatase steps, $K_{M_i} = (k_{\mathrm{cat}_i} + k_{\mathrm{off}_i})/k_{\mathrm{on}_i}$, $L_{M_i} = (l_{\mathrm{cat}_i} + l_{\mathrm{off}_i})/l_{\mathrm{on}_i}$ and $\lambda_i = k_{\mathrm{cat}_i}L_{M_i}/(K_{M_i}l_{\mathrm{cat}_i})$ (their (6)), and $\varphi_1^\kappa(u) = \sum_{i=0}^{n-1}\frac{\lambda_0\cdots\lambda_{i-1}}{K_{M_i}}u^i$, $\varphi_2^\kappa(u) = \sum_{i=1}^{n}\frac{\lambda_0\cdots\lambda_{i-1}}{L_{M_{i-1}}}u^i$ (their (7)), with empty products equal to $1$. For each such $\gamma$ and $\kappa$ and each $S_{tot} > 0$ there is $\varepsilon_2 > 0$ such that for all positive $E_{tot}, F_{tot}$ with $F_{tot} = E_{tot}/\gamma < \varepsilon_2S_{tot}/\gamma$ the system has at most $n + 1$ positive steady states (Theorem 4, small enzyme totals relative to the substrate); and for each such $\gamma$ and $\kappa$ and each $E_{tot} > 0$ there is $\varepsilon_3 > 0$ such that for all positive $F_{tot}, S_{tot}$ with $F_{tot} = E_{tot}/\gamma > S_{tot}/(\varepsilon_3\gamma)$ it has at most one positive steady state (Theorem 5, enzyme in excess). The bound is obtained by reducing the steady-state equations to the positive roots of a single polynomial in one variable.

## Depends on

- [Mass-action vector field](../../../../Dynamics/smooth-dynamics/mass-action-field.md)

## Expansion

1. The model: the $n$-site cycle, its mass action equations and the three conservation laws.
2. The reduction of positive steady states to positive roots of a one-variable polynomial of degree $2n + 1$, and the count giving at most $2n - 1$ (proof of Theorem 3).
3. The lower bound (Theorem 1) by perturbation of a polynomial with prescribed roots, and the regime bounds (Theorems 4 and 5), where $\varphi_1^\kappa(\gamma) \ne \varphi_2^\kappa(\gamma)$ keeps the reduced polynomial from being divisible by $u - \gamma$.
4. Whether the bound $2n - 1$ is attained for every $n$ is the question of [maximal multistationarity of multisite phosphorylation](../../maximal-multistationarity-of-multisite-phosphorylation.md).

## Sources

- L. Wang and E. D. Sontag, On the number of steady states in a multiple futile cycle, J. Math. Biol. 57 (2008), 29–52, Theorems 1, 3, 4 and 5 and equations (6)–(7); theorem and equation numbers as in the arXiv version, arXiv:0704.0036v2, which is titled "A remark on the number of steady states in a multiple futile cycle". <https://arxiv.org/abs/0704.0036>
