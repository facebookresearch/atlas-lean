# Linear constrained integrators of mass-action systems with absolute concentration robustness

Let a mass-action system have $d$ species, $m$ complexes $y_1,\dots,y_m \in \mathbb{Z}_{\ge 0}^d$ collected as the columns of $Y \in \mathbb{R}^{d\times m}$, and rate constants $\kappa$ with Laplacian $A(\kappa) \in \mathbb{R}^{m \times m}$, so that $\dot x = Y A(\kappa) \Lambda(x)$ with $\Lambda_k(x) = x^{y_k}$. For complexes $y_i, y_j$ define

$$
\Gamma_{ij}(\kappa) = \big\{ \gamma \in \mathbb{R}^{d+1} : \big(A(\kappa)^\top Y^\top \,\big|\, e_i\big)\,\gamma = e_j \big\},
$$

and let $\hat\Gamma_{ij}(\kappa)$ be its projection onto the first $d$ coordinates. A function $\phi$ is a *constrained integrator* for the output $x^{y_j - y_i}$ with set point $\bar q$ if $\frac{d}{dt}\phi(x(t)) = r(x(t))\,(x(t)^{y_j-y_i} - \bar q)$ for some function $r$.

**Theorem.**

1. If $\hat\Gamma_{ij}(\kappa) \ne \emptyset$ and $\gamma \in \Gamma_{ij}(\kappa)$, then every steady state $c$ with $c^{y_i} \ne 0$ satisfies $c^{y_j - y_i} = \gamma_{d+1}$: the monomial ratio $x^{y_j-y_i}$ is absolutely concentration robust. Moreover, $\phi(x) = \sum_k \beta_k x_k$ satisfies

$$
\frac{d}{dt}\phi(x(t)) = x(t)^{y_i}\big(x(t)^{y_j - y_i} - \gamma_{d+1}\big)
$$

for every initial condition if and only if $\beta \in \hat\Gamma_{ij}(\kappa)$.
2. If $y_i$ and $y_j$ are distinct non-terminal complexes, the deficiency is $1$, and a steady state with $c^{y_i} \ne 0$ exists (the Shinar–Feinberg setting), then $\hat\Gamma_{ij}(\kappa) \ne \emptyset$, so a linear constrained integrator exists.
3. $\hat\Gamma_{ij}(\kappa)$ contains $\hat\gamma + S^\perp$ for any $\hat\gamma \in \hat\Gamma_{ij}(\kappa)$, where $S$ is the stoichiometric subspace, with equality when some steady state $c$ has $c^{y_i} > 0$ and each linkage class contains exactly one terminal strong component.

## Expansion

For $\gamma \in \Gamma_{ij}(\kappa)$, $\hat\gamma^\top Y A(\kappa) = e_j^\top - \gamma_{d+1} e_i^\top$, so $\frac{d}{dt}\langle \hat\gamma, x\rangle = \Lambda_j(x) - \gamma_{d+1}\Lambda_i(x)$, which vanishes at a steady state only if $x^{y_j - y_i} = \gamma_{d+1}$. The set $\Gamma_{ij}(\kappa)$ is computed by symbolic linear algebra, which also yields the ACR value in closed form. This exhibits the hidden integral-feedback structure behind absolute concentration robustness in biochemical networks such as the EnvZ–OmpR osmoregulation system.

## Sources

- Daniele Cappelletti, Ankit Gupta and Mustafa Khammash, *A hidden integral structure endows Absolute Concentration Robust systems with resilience to dynamical concentration disturbances*, arXiv:1910.05531, Section 4 and Theorems D.1 and D.2 and Proposition C.2 (Appendices C–D). <https://doi.org/10.48550/arXiv.1910.05531> Published version: Journal of The Royal Society Interface 17 (2020) 20200437, <https://doi.org/10.1098/rsif.2020.0437>.
