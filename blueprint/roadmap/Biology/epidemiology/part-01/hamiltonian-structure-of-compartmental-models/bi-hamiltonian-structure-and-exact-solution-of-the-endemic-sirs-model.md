# Bi-Hamiltonian structure and exact solution of the endemic SIRS model

Let $S, I, R \ge 0$ be population fractions obeying the endemic SIRS model with constant rates $\alpha, \beta > 0$, $\mu \ge 0$, in which infected individuals either recover permanently (rate $\alpha$) or return to the susceptible class (rate $\mu$):

$$\dot S = -\beta S I + \mu I, \qquad \dot I = \beta S I - (\alpha + \mu) I, \qquad \dot R = \alpha I,$$

on the region $\beta S > \mu$. Put $g = -\beta S I + \mu I = -(\beta S - \mu) I$.

**Theorem (Proposition 5 and Example 5 of the source).**

1. The system is Hamiltonian for two compatible Poisson structures: $\{\cdot,\cdot\}_1$ with $\{S, I\}_1 = 0$, $\{S, R\}_1 = g$, $\{I, R\}_1 = \beta S I - (\alpha + \mu) I$ and Hamiltonian $H_1 = S + I + R$; and $\{\cdot,\cdot\}_2$ with $\{S, I\}_2 = g$, $\{S, R\}_2 = -g$, $\{I, R\}_2 = g$, Hamiltonian

    $$H_2 = -R - \frac{\alpha}{\beta} \log(\beta S - \mu),$$

    and Casimir $H_1$. The sum $\{\cdot,\cdot\}_1 + \{\cdot,\cdot\}_2$ is again a Poisson structure.

2. Consequently $C = R + \frac{\alpha}{\beta} \log(\beta S - \mu)$ is a first integral. For $S(0) = S_0$ with $\beta S_0 > \mu$, $I(0) = 1 - S_0$, $R(0) = 0$, the solution is

    $$R = \frac{\alpha}{\beta} \log \frac{\beta S_0 - \mu}{\beta S - \mu}, \qquad I = 1 - S - R,$$

    where $S(t)$ is the inverse of the quadrature

    $$t = \int_{S_0}^{S(t)} \frac{d\zeta}{-(\beta \zeta - \mu) \Big( 1 - \zeta - \frac{\alpha}{\beta} \log \frac{\beta S_0 - \mu}{\beta \zeta - \mu} \Big)}.$$

As $\mu \to 0$ this recovers the exact solution of the Kermack-McKendrick SIR model.

## Expansion

The first structure is the general one for [compartmental models with conserved population](compartmental-models-with-conserved-population-are-hamiltonian.md). For the second, writing the brackets as $\{x_i, x_j\} = \varepsilon_{ijk} w_k$ in coordinates $(S, I, R)$ gives $w = g\,(1, 1, 1)$; then $w \cdot \operatorname{curl} w = 0$ (the Jacobi identity in three dimensions) and $\nabla H_1 \parallel w$, so $H_1$ is a Casimir. A direct computation gives $\{S, H_2\}_2 = g$, $\{I, H_2\}_2 = -g + \alpha g / (\beta S - \mu) = \beta S I - (\alpha + \mu) I$ and $\{R, H_2\}_2 = -\alpha g / (\beta S - \mu) = \alpha I$. The sum of the two structures has $w = (-\alpha I, 0, g)$, and $w \cdot \operatorname{curl} w = \alpha (g - I \partial_I g) = 0$ because $g$ is linear in $I$. Equivalently, $\frac{d}{dt} \frac{\alpha}{\beta} \log(\beta S - \mu) = \alpha \dot S / (\beta S - \mu) = -\alpha I = -\dot R$. The printed Eqs. (52) and (68) of the source carry the opposite sign on the logarithmic term; the sign above is the one for which Hamilton's equations reproduce the model, and it agrees with the solution formula (69)-(70) of the source. On the leaf $C = C(0)$ the dynamics reduces to the single equation $\dot S = -(\beta S - \mu)\, I(S)$, integrated by quadrature. The SIR model with vaccination at rate $vI$ is treated in the same way, with first integral $R + \frac{\alpha + v}{\beta} \log(\beta S + v)$.

## Depends on

- [Compartmental models with conserved population are Hamiltonian](compartmental-models-with-conserved-population-are-hamiltonian.md)
- [Solution of the Kermack–McKendrick SIR system](../../kermack-mckendrick-sir-model/is-solution.md)

## Sources

- A. Ballesteros, A. Blasco and I. Gutierrez-Sagredo, *Hamiltonian structure of compartmental epidemiological models*, Physica D 413 (2020), 132656. DOI: <https://doi.org/10.1016/j.physd.2020.132656>. PMCID: PMC7375975.
