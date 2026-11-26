# Basic reproduction ratio as the spectral radius of the next-generation operator

Let individuals carry a heterogeneity state ("h-state") $\xi$ in a measure space $\Omega$ (sums replace integrals when $\Omega$ is discrete). Let $S(\xi) \ge 0$ be the density of susceptibles in the disease-free steady demographic state, and let $A(\tau, \xi, \eta) \ge 0$ be the expected infectivity, towards a susceptible of h-state $\xi$, of an individual infected $\tau$ time units ago while in h-state $\eta$. The **next-generation operator** acts on densities $\phi \in L^1(\Omega)$ of newly infected individuals by

$$(K\phi)(\xi) = S(\xi) \int_\Omega \int_0^\infty A(\tau, \xi, \eta)\, d\tau\, \phi(\eta)\, d\eta ,$$

and it is a positive operator (nonnegative densities go to nonnegative densities). Assume $K$ is bounded on $L^1(\Omega)$. Its spectral radius is

$$r(K) = \inf_{m \ge 1} \|K^m\|^{1/m} = \lim_{m \to \infty} \|K^m\|^{1/m}.$$

**Definition.** The basic reproduction ratio is $R_0 = r(K)$. When $K$ is, for instance, compact, $r(K)$ is an eigenvalue of $K$ (the dominant eigenvalue) with a positive eigenvector $\phi_d$, and under mild extra conditions $K^m \phi \sim c(\phi)\, R_0^m \phi_d$ with $c(\phi) > 0$ for every nonnegative, nonzero $\phi$.

**Threshold.** The generations $K^m\phi$ tend to $0$ when $R_0 < 1$ and can be made arbitrarily large when $R_0 > 1$. In real time, the linearized incidence $i(t,\xi)$ satisfies

$$i(t, \xi) = S(\xi) \int_\Omega \int_0^\infty A(\tau, \xi, \eta)\, i(t - \tau, \eta)\, d\tau\, d\eta ,$$

and $i(t,\xi) = e^{\lambda t}\psi(\xi)$ is a solution exactly when $\psi$ is an eigenvector with eigenvalue $1$ of

$$(K_\lambda \phi)(\xi) = S(\xi) \int_\Omega \int_0^\infty A(\tau, \xi, \eta)\, e^{-\lambda \tau}\, d\tau\, \phi(\eta)\, d\eta .$$

The real root $\lambda_d$ with largest real part satisfies $\lambda_d > 0 \iff R_0 > 1$ and $\lambda_d < 0 \iff R_0 < 1$. The operator norm $\|K\|$ is only an upper bound for $R_0$: for a host–vector model with $K = \begin{pmatrix} 0 & a_{12} S_1 \\ a_{21} S_2 & 0 \end{pmatrix}$, $\|K\| = \max(a_{12}S_1, a_{21}S_2)$ while $R_0 = \sqrt{a_{12} S_1 a_{21} S_2}$, the geometric mean of the two one-generation factors.

For finite $\Omega$, $K$ is a nonnegative matrix and $R_0$ is its spectral radius, the [next-generation matrix](r0.md) quantity.

## Depends on

- [Basic reproduction number of the next-generation matrix](r0.md)

## Expansion

The norm $\|K^m\phi\|$ is the size of generation $m$, so $\|K^m\|^{1/m}$ is the worst-case per-generation growth factor over $m$ generations; Gelfand's formula identifies its limit with the spectral radius. Positivity (Krein–Rutman / Perron–Frobenius) gives a positive dominant eigenvector, which is the "typical" infected individual of the verbal definition. For the real-time statement, $\lambda \mapsto r(K_\lambda)$ is decreasing on the reals with $r(K_0) = R_0$, so $r(K_{\lambda_d}) = 1$ has $\lambda_d > 0$ exactly when $R_0 > 1$.

## Sources

- O. Diekmann, J. A. P. Heesterbeek and J. A. J. Metz, *On the definition and the computation of the basic reproduction ratio $R_0$ in models for infectious diseases in heterogeneous populations*, J. Math. Biol. 28 (1990), 365–382, <https://doi.org/10.1007/BF00178324>, Section 2: Eq. (2.1) (next-generation operator), Eq. (2.2) (spectral radius), the Definition $R_0 = r(K(S))$, Eqs. (2.4)–(2.5) (real-time equation and $K_\lambda$), and the host–vector example.
