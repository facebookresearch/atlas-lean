# Uniform persistence of the SVEIR fomite model

Consider the [SVEIR model with saturating fomite transmission](sveir-model-with-saturating-fomite-transmission.md) for any Hill exponent $n\in\mathbb N$, with semiflow $\Phi$ on $\bar\Omega$, interior set $X_0=\{E>0,I>0,C>0\}$ and boundary $\partial X_0=\{EIC=0\}$.

**Lemma.** The largest positively invariant subset of $\partial X_0$ is the disease-free face $\Sigma=\{E=I=C=0\}$. If $\mathcal R_c>1$, then $E_0$ is a weak repeller for $X_0$: $\limsup_{t\to\infty}d(\Phi_t(x_0),E_0)>0$ for every $x_0\in X_0$.

**Theorem.** If $\mathcal R_c>1$, the system is uniformly persistent: there is $\delta>0$ such that every solution with $E(0)+I(0)+C(0)>0$ satisfies

$$\liminf_{t\to\infty}S(t),\ \liminf_{t\to\infty}E(t),\ \liminf_{t\to\infty}I(t),\ \liminf_{t\to\infty}V(t),\ \liminf_{t\to\infty}C(t)\ \ge\delta.$$

Moreover, the system has at least one endemic equilibrium.

For $n\ge2$ the threshold $\mathcal R_c=\mathcal R_c^{\rm dir}$ involves only direct transmission, so persistence above threshold is driven by contact transmission, while fomites still shape the endemic dynamics.

## Depends on

- [SVEIR model with saturating fomite transmission](sveir-model-with-saturating-fomite-transmission.md)

## Expansion

On $\Sigma$ every solution converges to $E_0$, so $\{E_0\}$ is an isolated invariant set giving an acyclic covering of the boundary dynamics. When $\mathcal R_c>1$ the infected subsystem linearized at $E_0$ has a positive principal eigenvalue with a positive eigenvector (monotone systems theory), and a comparison argument shows that orbits from $X_0$ cannot remain near $E_0$, which is the weak-repeller lemma. Thieme's persistence theorem for semiflows then makes $\partial X_0$ a uniform strong repeller, and Zhao's theorem on uniformly persistent dissipative systems yields an interior equilibrium.

## Sources

- E. Penitente, U. Foryś and B. Gürbüz, "Global stability and uniform persistence in an epidemic model with saturating fomite-mediated transmission", *Ricerche di Matematica* (2026), Lemma 1, Lemma 2, Theorem 2 and Section 4 (persistence of the disease and endemic equilibrium), <https://doi.org/10.1007/s11587-026-01159-9> (preprint arXiv:2603.28285).
