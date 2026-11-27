# The post-outbreak reproduction number is below one

**Setting.** In a trait-structured epidemic with trait space $\Omega$, trait distribution $\Phi$ and next-generation operator $(\mathcal K_0\psi)(x) = N\int_\Omega k_0(x, \xi)\psi(\xi)\,\Phi(d\xi)$, let $R_0 = \rho(\mathcal K_0) > 1$. Let $y = 1 - s(\infty, \cdot)$ be the unique nontrivial solution of the final size equation $y = 1 - e^{-\mathcal K_0 y}$. After the outbreak, the susceptible population is described by the measure $\omega \mapsto \int_\omega s(\infty, x)\,\Phi(dx)$. The corresponding next-generation operator is $\mathcal K_0^{\text{after}} = \mathcal K_0 L$, where $L\psi = (1 - y)\psi$.

**Theorem.** Assume $\Omega$ is compact, the kernel $k_0$ satisfies the continuity hypothesis (H1) and the irreducibility hypothesis (H2) of the final size theorem, and $R_0 > 1$. Then

$$\rho\big(\mathcal K_0^{\text{after}}\big) < 1 .$$

So a reintroduction of the pathogen into the post-outbreak population is subcritical.

## Depends on

- [The basic reproduction ratio `R₀`](../../next-generation-operator-and-basic-reproduction/generation-growth.md)
- [Final size equation for trait-structured epidemics](final-size-equation-for-trait-structured-epidemics.md)

## Expansion

The operator $\bar{\mathcal K}_0 = L\mathcal K_0 = L\,\mathcal K_0^{\text{after}}L^{-1}$ is similar to $\mathcal K_0^{\text{after}}$, so the two have the same spectral radius $\rho$. By (H1), $\bar{\mathcal K}_0$ is compact on $C(\Omega)$, so by Krein–Rutman its adjoint on measures has $\rho$ as an eigenvalue with a nontrivial positive eigenmeasure $\mu$. Rewrite the final size equation as $\mathcal K_0 y + \ln(1 - y) = 0$, multiply by $1 - y$ and integrate against $\mu$:

$$\int_\Omega\big[\rho\,y(x) + (1 - y(x))\ln(1 - y(x))\big]\,\mu(dx) = 0 .$$

For $\rho \ge 1$ and $0 < z < 1$ one has $\rho z + (1 - z)\ln(1 - z) > 0$, and $y$ is strictly positive, so the left side would be positive. Hence $\rho < 1$. The argument adapts a finite-type proof to general trait spaces.

## Sources

- Martin Bootsma, Danny Chan, Odo Diekmann and Hisashi Inaba, "The effect of host population heterogeneity on epidemic outbreaks", Mathematics in Applied Sciences and Engineering 5 (2024), 1–35, <https://doi.org/10.5206/mase/16718>; numbering as in arXiv:2308.06593v2: Section 5, Theorem 5.6 (Theorem 4.6 in v1).
