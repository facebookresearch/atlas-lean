# Solution of Henderson's mixed-model equations

Let $(K, \sigma_g^2, \sigma_e^2)$ be [variance components](model.md) on $n$ individuals, let $X$ be a real $n \times p$ matrix and $y \in \mathbb{R}^n$, and put $R = \sigma_e^2 \mathrm{I}$ and $G = \sigma_g^2 K$. A pair $(\beta, g) \in \mathbb{R}^p \times \mathbb{R}^n$ solves Henderson's mixed-model equations if

$$X^\top R^{-1} X \beta + X^\top R^{-1} g = X^\top R^{-1} y \quad\text{and}\quad R^{-1} X \beta + (R^{-1} + G^{-1}) g = R^{-1} y,$$

with the convention that the inverse of a singular matrix is $0$ (so $G^{-1} = 0$ when $G$ is singular). These are the general mixed-model equations with one genetic effect per individual (incidence matrix $\mathrm{I}$).
