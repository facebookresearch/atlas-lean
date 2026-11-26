# Hypercontractivity in Fourier form

Let $E$ be a finite set and $0 \le \rho \le 1$. For every $f : \{0, 1\}^E \to \mathbb{R}$, with [Walsh–Fourier coefficients](khc-fourier-coeff.md) $\hat f(S)$,

$$\sum_{S \subseteq E} \rho^{2\lvert S\rvert}\, \hat f(S)^2 \le \lVert f\rVert_{1 + \rho^2}^2,$$

where $\lVert f\rVert_r = (\mathbb{E}\lvert f\rvert^r)^{1/r}$ under the uniform measure. The left side is $\lVert T_\rho f\rVert_2^2$, so this is the [Bonami–Beckner inequality](khc-hypercontractivity-general.md) squared.
