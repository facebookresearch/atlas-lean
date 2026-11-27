# Dominant eigenvalue and real-time growth for the next-generation operator of a heterogeneous population

Let individuals carry a heterogeneity state ("h-state") $\xi$ in a measure space $\Omega$ (sums replace integrals when $\Omega$ is discrete). Let $S(\xi) \ge 0$ be the density of susceptibles in the disease-free steady demographic state, and let $A(\tau, \xi, \eta) \ge 0$ be the expected infectivity, towards a susceptible of h-state $\xi$, of an individual infected $\tau$ time units ago while in h-state $\eta$. The **next-generation operator** acts on densities $\phi \in L^1(\Omega)$ of newly infected individuals by

$$(K\phi)(\xi) = S(\xi) \int_\Omega \int_0^\infty A(\tau, \xi, \eta)\, d\tau\, \phi(\eta)\, d\eta ,$$

and it is a [positive](../next-generation-operator-and-basic-reproduction/is-positive.md) operator (nonnegative densities go to nonnegative densities). Assume $K$ is bounded on $L^1(\Omega)$. Its basic reproduction ratio $R_0 = r(K)$ is the [per-generation growth factor](../next-generation-operator-and-basic-reproduction/generation-growth.md) of $K$, the spectral radius of its complexification; it may be $0$, for instance for the zero kernel $A = 0$.

**Dominant eigenvalue.** If $K$ is compact and $r(K) > 0$, then $r(K)$ is an eigenvalue of $K$ with a nonnegative, nonzero eigenfunction $\phi_d$ (Krein–Rutman). If moreover $r(K)$ is an algebraically simple eigenvalue and every other point of the spectrum has modulus less than $r(K)$, then $R_0^{-m} K^m \phi \to P\phi$ for every $\phi \in L^1(\Omega)$, where $P$ is the spectral projection onto the span of $\phi_d$. Without $r(K) > 0$ there need be no such eigenvalue: the Volterra operator $(Kf)(x) = \int_0^x f(y)\,dy$ on $L^1[0, 1]$ is compact, positive and injective, and $r(K) = 0$.

**Threshold.** The generation-by-generation threshold statements for this $K$ are [subcritical decay](../next-generation-operator-and-basic-reproduction/tendsto-norm-pow-apply-zero.md) ($R_0 < 1$) and [supercritical growth](../next-generation-operator-and-basic-reproduction/exists-nonneg-unbounded-of-one-lt.md) ($R_0 > 1$); under irreducibility, [every introduction grows at rate $R_0$](../next-generation-operator-and-basic-reproduction/tendsto-norm-pow-apply-rpow.md).

**Real-time growth.** The linearized incidence $i(t,\xi)$ satisfies

$$i(t, \xi) = S(\xi) \int_\Omega \int_0^\infty A(\tau, \xi, \eta)\, i(t - \tau, \eta)\, d\tau\, d\eta ,$$

and, for real $\lambda$ such that the operator below is bounded, $i(t,\xi) = e^{\lambda t}\psi(\xi)$ is a solution exactly when $\psi$ is an eigenfunction with eigenvalue $1$ of

$$(K_\lambda \phi)(\xi) = S(\xi) \int_\Omega \int_0^\infty A(\tau, \xi, \eta)\, e^{-\lambda \tau}\, d\tau\, \phi(\eta)\, d\eta .$$

Assume there is $\lambda_* \in [-\infty, 0)$ such that $K_\lambda$ is bounded and compact for every real $\lambda > \lambda_*$, and that $\lambda \mapsto r(K_\lambda)$ is continuous and strictly decreasing on $(\lambda_*, \infty)$ with $\lim_{\lambda \to \infty} r(K_\lambda) < 1 < \lim_{\lambda \downarrow \lambda_*} r(K_\lambda)$. Then there is a unique real $\lambda_d > \lambda_*$ with $r(K_{\lambda_d}) = 1$; it gives an exponential solution $e^{\lambda_d t}\psi$ with $\psi \ge 0$ nonzero, and $\lambda_d > 0 \iff R_0 > 1$, $\lambda_d < 0 \iff R_0 < 1$. Without such hypotheses no real root need exist: for $A = 0$ every $K_\lambda$ is zero.

The operator norm $\|K\|$ is only an upper bound for $R_0$: for a host–vector model with $K = \begin{pmatrix} 0 & a_{12} S_1 \\ a_{21} S_2 & 0 \end{pmatrix}$, $\|K\| = \max(a_{12}S_1, a_{21}S_2)$ while $R_0 = \sqrt{a_{12} S_1 a_{21} S_2}$, the geometric mean of the two one-generation factors.

For finite $\Omega$, $K$ is a nonnegative matrix and $R_0$ is its spectral radius, the [next-generation matrix](r0.md) quantity.

## Depends on

- [The basic reproduction ratio `R₀`](../next-generation-operator-and-basic-reproduction/generation-growth.md)
- [Is Positive](../next-generation-operator-and-basic-reproduction/is-positive.md)

## Expansion

For a compact positive operator on $L^1$, whose cone of nonnegative functions is reproducing, the Krein–Rutman theorem gives a nonnegative eigenfunction for $r(K)$ only when $r(K) > 0$; the Volterra example shows the hypothesis is needed. Under the spectral-gap hypothesis, the spectral decomposition $K = r(K)P + K(I - P)$ with $r(K(I - P)) < r(K)$ gives the convergence $R_0^{-m}K^m \to P$. For the real-time statement, monotonicity and continuity of $\lambda \mapsto r(K_\lambda)$ with $r(K_0) = R_0$ give the unique crossing of the level $1$ and its sign; Krein–Rutman applied to $K_{\lambda_d}$ gives the eigenfunction $\psi$.

## Sources

- O. Diekmann, J. A. P. Heesterbeek and J. A. J. Metz, *On the definition and the computation of the basic reproduction ratio $R_0$ in models for infectious diseases in heterogeneous populations*, J. Math. Biol. 28 (1990), 365–382, <https://doi.org/10.1007/BF00178324>, Section 2: Eq. (2.1) (next-generation operator), Eq. (2.3) (dominant eigenvalue), Eqs. (2.4)–(2.5) (real-time equation and $K_\lambda$), and the host–vector example. The hypotheses of the dominant-eigenvalue and real-time statements are stated here explicitly.
