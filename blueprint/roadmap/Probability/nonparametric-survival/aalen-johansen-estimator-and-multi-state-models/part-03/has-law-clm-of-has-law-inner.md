# Gaussian laws of scalar projections extend to all continuous linear functionals

Let $(\Omega, P)$ be a measure space (no normalisation is assumed), and let $E$ be a real Hilbert space carrying a measurable structure and a measure $\nu$. Let $A : E \to E$ and $X : \Omega \to E$ be functions.

For a real function $Y$ on $\Omega$, $\mathrm{Var}_P(Y) = \int \big(Y - \int Y \, dP\big)^2 \, dP$, where $\int Y \, dP$ is read as $0$ when $Y$ is not $P$-integrable and the variance is read as $0$ when the outer integral is infinite. Write $\mathcal{N}(0, \sigma^2)$ for the centred Gaussian law on $\mathbb{R}$ with variance $\sigma^2 \ge 0$ (the point mass at $0$ when $\sigma^2 = 0$). A function $Z : E \to \mathbb{R}$ has law $\rho$ under $\nu$ if $Z$ is $\nu$-almost everywhere measurable and the image of $\nu$ under $Z$ is $\rho$.

Assume that for every $t \in E$ the function $z \mapsto \langle A z, t \rangle$ has law $\mathcal{N}\big(0, \mathrm{Var}_P(\langle X, t \rangle)\big)$ under $\nu$. Then for every continuous linear functional $\varphi : E \to \mathbb{R}$, the function $z \mapsto \varphi(A z)$ has law

$$\mathcal{N}\big(0, \mathrm{Var}_P(\varphi \circ X)\big)$$

under $\nu$.
