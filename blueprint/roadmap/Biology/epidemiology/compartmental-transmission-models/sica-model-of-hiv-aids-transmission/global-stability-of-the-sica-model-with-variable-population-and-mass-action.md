# Global stability of the SICA HIV/AIDS model with variable population size and mass-action incidence

With absolute numbers $S, I, C, A$ (susceptible, HIV-infected pre-AIDS, chronic under antiretroviral treatment, AIDS), constant recruitment $\Lambda$, and mass-action incidence in which treated and AIDS individuals are infectious with relative strengths $\eta_C$ and $\eta_A$,

$$
\begin{aligned}
\dot S &= \Lambda - \beta(I + \eta_C C + \eta_A A) S - \mu S, \\
\dot I &= \beta(I + \eta_C C + \eta_A A) S - (\rho + \phi + \mu) I + \omega C + \alpha A, \\
\dot C &= \phi I - (\omega + \mu) C, \\
\dot A &= \rho I - (\alpha + \mu + d) A .
\end{aligned}
$$

The total population obeys $\dot N = \Lambda - \mu N - dA$, so $\Omega = \{N \le \Lambda/\mu\}$ is positively invariant. With $\xi_1 = \alpha + \mu + d$, $\xi_2 = \omega + \mu$, $S^0 = \Lambda/\mu$,

$$
R_0 = \frac{S^0 \beta\big(\xi_2(\xi_1 + \rho\eta_A) + \eta_C\phi\xi_1\big)}{\mu\big(\xi_2(\rho + \xi_1) + \phi\xi_1 + \rho d\big) + \rho\omega d} = \frac{S^0\mathcal{N}}{\mathcal{D}} .
$$

**Theorem.**

1. The disease-free equilibrium $(\Lambda/\mu, 0, 0, 0)$ is globally asymptotically stable in $\Omega$ when $R_0 < 1$, and unstable when $R_0 > 1$.
2. For $R_0 > 1$ there is a unique endemic equilibrium

$$
S^* = \frac{\mathcal{D}}{\mathcal{N}}, \quad I^* = \frac{\xi_1\xi_2(\Lambda\mathcal{N} - \mu\mathcal{D})}{\mathcal{D}\mathcal{N}}, \quad C^* = \frac{\phi\xi_1(\Lambda\mathcal{N} - \mu\mathcal{D})}{\mathcal{D}\mathcal{N}}, \quad A^* = \frac{\rho\xi_2(\Lambda\mathcal{N} - \mu\mathcal{D})}{\mathcal{D}\mathcal{N}},
$$

and it is globally asymptotically stable on the interior of $\Omega$.

## Depends on

- [Global stability of the endemic equilibrium of the SICA HIV/AIDS model](global-stability-of-the-sica-endemic-equilibrium.md)

## Proof depends on

- [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)

## Expansion

$R_0$ comes from the next-generation matrix of the infected subsystem $(I, C, A)$. The infectiousness of the treated and AIDS classes is weighted by $\eta_C$, $\eta_A$ and by the expected time an infected person spends in each class, which explains the factors $\eta_C\phi\xi_1$ and $\rho\eta_A\xi_2$ in $\mathcal{N}$. Global stability of both equilibria is proved by Lyapunov's direct method combined with LaSalle's invariance principle. The equilibrium formulas show that the endemic state exists exactly when $\Lambda\mathcal{N} > \mu\mathcal{D}$, i.e. when $R_0 > 1$.

## Sources

- SILVA Cristiana J.; TORRES, "Global stability for a HIV/AIDS model", Communications Faculty Of Science University of Ankara Series A1Mathematics and Statistics 67 (2018), 93–101, <https://doi.org/10.1501/commua1_0000000833>. Published version of arXiv:1704.05806, cited next; locators there refer to the arXiv version.
- Cristiana J. Silva, Delfim F. M. Torres, "Global Stability for a HIV/AIDS Model", arXiv (2017). Lemma 1, Theorem 1, Lemma 2, Theorem 2. <https://doi.org/10.48550/arXiv.1704.05806>
