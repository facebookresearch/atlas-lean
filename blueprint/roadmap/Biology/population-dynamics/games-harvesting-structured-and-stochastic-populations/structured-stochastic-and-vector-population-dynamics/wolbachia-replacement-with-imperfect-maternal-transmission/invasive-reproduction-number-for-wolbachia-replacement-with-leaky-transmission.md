# Invasive reproduction number for Wolbachia replacement with imperfect maternal transmission

Consider *Aedes aegypti* split into Wolbachia-uninfected (WU, $\bar w$) and Wolbachia-infected (WI, $w$) aquatic stages $Q_{\bar w}, Q_w$ and adult females $F_{\bar w}, F_w$, with a 1:1 sex ratio. Cytoplasmic incompatibility is leaky: a fraction $\rho_1$ of offspring of WI females mated with WI males, and a fraction $\rho_2$ of those of WI females mated with WU males, are uninfected. WI adults lose infection at rate $\sigma$. With logistic aquatic regulation (capacity $K$, $Q = Q_{\bar w} + Q_w$),

$$
\begin{aligned}
Q_{\bar w}' &= \frac{\phi_{\bar w}F_{\bar w}^2 + \rho_1\phi_w F_w^2 + \rho_2\phi_w F_w F_{\bar w}}{F_{\bar w} + F_w}\Big(1 - \frac{Q}{K}\Big) - (\mu_a + \psi) Q_{\bar w}, \\
Q_w' &= \frac{(1-\rho_1)\phi_w F_w^2 + (1-\rho_2)\phi_w F_w F_{\bar w}}{F_{\bar w} + F_w}\Big(1 - \frac{Q}{K}\Big) - (\mu_a + \psi) Q_w, \\
F_{\bar w}' &= \tfrac{\psi}{2} Q_{\bar w} + \sigma F_w - \mu_{\bar w} F_{\bar w}, \qquad F_w' = \tfrac{\psi}{2} Q_w - \sigma F_w - \mu_w F_w .
\end{aligned}
$$

The isolated basic offspring numbers are $R_{0\bar w} = \frac{\phi_{\bar w}\psi}{2\mu_{\bar w}(\mu_a + \psi)}$ and $R_{0w} = \frac{\phi_w\psi}{2\mu_w(\mu_a + \psi)}$.

**Invasion threshold ($\rho_1 = \sigma = 0$).** The WU-only equilibrium has $Q_{\bar w}^* = K(1 - 1/R_{0\bar w})$. By the next-generation method, the invasive reproduction number of WI mosquitoes introduced into it is

$$
R_{0w|\bar w} = \frac{R_{0w}(1 - \rho_2)}{R_{0\bar w}} = \frac{\phi_w\mu_{\bar w}(1 - \rho_2)}{\phi_{\bar w}\mu_w}.
$$

The WI-only equilibrium $E_3 = \big(0, K(1 - 1/R_{0w}), 0, \tfrac{\psi K}{2\mu_w}(1 - 1/R_{0w})\big)$ is locally asymptotically stable when $R_{0w} > 1$ and $\mu_{\bar w} > \rho_2\mu_w$, even if $R_{0w|\bar w} < 1$, which gives bistability.

**Theorem.** If $\mu_{\bar w} > \rho_2\mu_w$, $R_{0w|\bar w} > 1$, and $R_{0w}$ exceeds an explicit threshold $R_{0w}^* > 1$, then $E_3$ is globally asymptotically stable: Wolbachia replaces the wild type.

**Theorem (loss of infection).** If $\sigma + \rho_2\mu_w \ge \mu_{\bar w}(1 - \rho_1)$, the adjusted invasive number is $R^1_{0w|\bar w} = \frac{R_{0w}(1 - \rho_2)\mu_w}{R_{0\bar w}(\mu_w + \sigma)}$. When $R^1_{0w|\bar w} < 1$ and $R_{0\bar w} > 1$, the WU-only equilibrium is the only nontrivial equilibrium; there is no WI-only state, since loss of infection keeps replenishing WU mosquitoes.

## Depends on

- [Basic reproduction number from the next-generation matrix](../../../../epidemiology/next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

At the WU equilibrium, linearizing the WI compartments gives $F = \begin{pmatrix} 0 & \phi_w (1-\rho_2)(K - Q_{\bar w}^*)/K \\ 0 & 0 \end{pmatrix}$ and $V = \begin{pmatrix} \mu_a + \psi & 0 \\ -\psi/2 & \mu_w \end{pmatrix}$. The spectral radius of $FV^{-1}$ simplifies using $(K - Q_{\bar w}^*)/K = 1/R_{0\bar w}$. Global stability of $E_3$ follows from the Volterra-type Lyapunov function $V = \frac{\psi}{2\mu_w(\mu_a+\psi)}\int_{Q_w^*}^{Q_w}(1 - Q_w^*/y)\,dy + \frac{1}{\mu_w}\int_{F_w^*}^{F_w}(1 - F_w^*/y)\,dy$. A positive loss rate $\sigma$ divides the invasive number by $1 + \sigma/\mu_w$; imperfect transmission within WI matings ($\rho_1$) leaves it unchanged.

## Sources

- Adeshina I. Adekunle, Michael T. Meehan, Emma S. McBryde, "Mathematical analysis of a Wolbachia invasive model with imperfect maternal transmission and loss of Wolbachia infection", Infectious Disease Modelling 4 (2019), 265–285, <https://doi.org/10.1016/j.idm.2019.10.001>. Published version of arXiv:1809.01538, cited next; locators there refer to the arXiv version.
- Adeshina I. Adekunle, Michael T. Meehan, Emma S. McBryde, "Mathematical analysis of a Wolbachia invasive model with imperfect maternal transmission and loss of Wolbachia infection", arXiv (2018). Section 2, Eqs. (12)-(13), (21), (28), (50a), Theorem 3.1, Theorem 3.2, Theorem A.1. <https://doi.org/10.48550/arXiv.1809.01538>
