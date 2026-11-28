# Global stability of the endemic equilibrium of the SICA HIV/AIDS model

The SICA model divides a population into susceptible $S$, HIV-infected without clinical AIDS symptoms $I$, chronic HIV infection under antiretroviral treatment $C$, and AIDS $A$. With recruitment $\Lambda$ and mass-action incidence it reads

$$
\begin{aligned}
\dot S &= \Lambda - \beta I S - \mu S, \\
\dot I &= \beta I S - (\rho + \phi + \mu) I + \alpha A + \omega C, \\
\dot C &= \phi I - (\omega + \mu) C, \\
\dot A &= \rho I - (\alpha + \mu + d) A,
\end{aligned}
$$

where $\phi$ is the treatment rate, $\omega$ the treatment-failure rate, $\rho$ the progression rate to AIDS, $\alpha$ the rate at which AIDS patients start treatment and return to the $I$ class, and $d$ the AIDS-induced death rate. With $\xi_1 = \alpha + \mu + d$ and $\xi_2 = \omega + \mu$, the basic reproduction number is

$$
R_0 = \frac{\Lambda}{\mu}\cdot\frac{\beta\, \xi_1 \xi_2}{\mathcal D}, \qquad \mathcal D = \mu\big[\xi_2(\rho + \xi_1) + \xi_1\phi + \rho d\big] + \rho\omega d.
$$

The factor $\Lambda/\mu$ is the disease-free susceptible level $S^0$. The source's formula (2), $\beta\xi_1\xi_2/\mathcal D$, is the reproduction number of its model (1) with standard incidence $\beta IS/N$; for the mass-action system above it is correct only when $\Lambda = \mu$.

**Theorem.** The disease-free equilibrium $(\Lambda/\mu, 0, 0, 0)$ is globally asymptotically stable if $R_0 < 1$ and unstable if $R_0 > 1$. For $R_0 > 1$ there is a unique endemic equilibrium $\Sigma^*$, with steady-state force of infection $\lambda^* = \mu(R_0 - 1)$, and it is globally asymptotically stable on the feasible region minus the disease-free face $\{I = C = A = 0\}$. Moreover, $R_0$ increases with $\beta$, $\alpha$ and $\omega$ and decreases with $\phi$ and $\rho$, and its normalized sensitivity index with respect to $\beta$ is $\Upsilon^{R_0}_\beta = 1$.

## Depends on

- [Basic reproduction number from the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)

## Expansion

Global stability uses the Volterra-type Lyapunov function

$$
V = \sum_{X \in \{S, I\}} \Big(X - X^* - X^*\ln\frac{X}{X^*}\Big) + \frac{\omega}{\xi_2}\Big(C - C^* - C^*\ln\frac{C}{C^*}\Big) + \frac{\alpha}{\xi_1}\Big(A - A^* - A^*\ln\frac{A}{A^*}\Big).
$$

After substituting the equilibrium relations, $\dot V$ is a sum of terms of the form $2 - x - 1/x \le 0$, and LaSalle's invariance principle gives convergence to $\Sigma^*$. $R_0$ is linear in $\beta$, which is why its sensitivity index with respect to $\beta$ equals $1$. The treatment parameters enter only through the denominator.

## Sources

- Cristiana J. Silva, Delfim F.M. Torres, "A SICA compartmental model in epidemiology with application to HIV/AIDS in Cape Verde", Ecological Complexity 30 (2017), 70–75, <https://doi.org/10.1016/j.ecocom.2016.12.001>. Published version of arXiv:1612.00732, cited next; locators there refer to the arXiv version.
- Cristiana J. Silva, Delfim F. M. Torres, "A SICA compartmental model in epidemiology with application to HIV/AIDS in Cape Verde", arXiv (2016). Lemma 2.1, Theorem 3.1, Propositions 4.1-4.4, Definition 4.1. <https://doi.org/10.48550/arXiv.1612.00732>
