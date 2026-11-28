# Tumour-free threshold of a dendritic-cell–cytokine–anti-PD-L1 tumour model

**Model.** Let $T$ be tumour cells, $C$ CD8$^+$ T cells, $D$ dendritic cells, $I_2$ and $I_{12}$ the cytokines IL-2 and IL-12, and $Z$ an anti-PD-L1 inhibitor. With all parameters positive,

$$\begin{aligned}
\dot T&=\alpha T(1-\beta T)-\gamma T-\phi CT, &\dot C&=\phi CT+\rho CD-\kappa C, &\dot D&=\mu-\rho CD-(\omega+\lambda)D,\\
\dot I_2&=\lambda D-dI_2, &\dot I_{12}&=dI_2-\psi I_{12}, &\dot Z&=\psi I_{12}-aZ .
\end{aligned}$$

Here $\alpha,\beta$ give logistic tumour growth, $\gamma$ and $\phi$ are killing by dendritic and T cells, $\mu$ is the dendritic-cell source, $\rho$ is T-cell expansion on contact with dendritic cells (which inactivates them), and $\kappa,\omega$ are natural death rates. IL-2 is produced from dendritic cells at rate $\lambda$, and the cascade $I_2\to I_{12}\to Z$ is linear.

**Tumour-free equilibrium.** The model has the equilibrium with no tumour and no T cells

$$E_0=\Big(0,\ 0,\ \tfrac{\mu}{\omega+\lambda},\ \tfrac{\lambda\mu}{d(\omega+\lambda)},\ \tfrac{\lambda\mu}{\psi(\omega+\lambda)},\ \tfrac{\lambda\mu}{a(\omega+\lambda)}\Big).$$

Set

$$R_0=\frac{\mu\rho}{\kappa(\lambda+\omega)} .$$

**Proposition.** The Jacobian at $E_0$ is lower triangular with eigenvalues

$$\alpha-\gamma,\quad \frac{\mu\rho}{\lambda+\omega}-\kappa=\kappa(R_0-1),\quad -(\lambda+\omega),\quad -d,\quad -\psi,\quad -a .$$

So $E_0$ is locally asymptotically stable if $\alpha<\gamma$ and $R_0<1$, and unstable if $\alpha>\gamma$ or $R_0>1$.

## Expansion

At $T=C=0$ the $T$-row of the Jacobian reduces to $\alpha-\gamma$ on the diagonal, and the $C$-row to $\phi T+\rho D-\kappa=\rho\mu/(\omega+\lambda)-\kappa$, because both equations carry their own variable as a factor. The remaining block is the linear dendritic-cell–cytokine cascade, with negative diagonal entries. $R_0$ compares T-cell expansion fed by the steady dendritic-cell pool, $\rho\mu/(\omega+\lambda)$, with T-cell death $\kappa$. The tumour eigenvalue $\alpha-\gamma$ does not involve $R_0$: in this model the tumour is cleared near $E_0$ only if dendritic-cell killing outpaces intrinsic growth. The source's Theorem 1 states the threshold in $R_0$ alone. Its own eigenvalue list contains $\alpha-\gamma$, so the condition $\alpha<\gamma$ must be added. The source also replaces $d/dt$ with a fractal-fractional Atangana–Baleanu derivative. The statement here is for the integer-order system.

## Sources

- K. S. Nisar, M. O. Kulachi, A. Ahmad, M. Farman, M. Saqib, M. U. Saleem, "Fractional order cancer model infection in human with CD8+ T cells and anti-PD-L1 therapy: simulations and control strategy", *Scientific Reports* 14 (2024), model (1), equilibrium $D_1$, reproduction number $R_0$ and Theorem 1 (Jacobian and eigenvalues at the tumour-free equilibrium), <https://doi.org/10.1038/s41598-024-66593-x>, PMCID PMC11251283.
