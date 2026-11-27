# Subharmonic coexistence states and chaos in degenerate periodic Volterra predator-prey models

**Model.** Consider the non-autonomous Volterra predator-prey system

$$u' = \lambda\alpha(t)\,u(1 - v), \qquad v' = \lambda\beta(t)\,v(-1 + u),$$

with $\lambda > 0$ and $T$-periodic continuous weights $\alpha, \beta \ge 0$, $\int_0^T\alpha > 0$, $\int_0^T\beta > 0$, which are *degenerate*: $\operatorname{supp}\alpha \cap \operatorname{supp}\beta$ has measure zero, so prey growth and predation act in alternating seasons. Within a period, an $\alpha$-interval (resp. $\beta$-interval) is a maximal interval where $\beta \equiv 0$ (resp. $\alpha \equiv 0$); let $k$ and $\ell$ be their numbers, $\alpha_i, \beta_j$ the restrictions of the weights to them, and $A_i = \int_0^T\alpha_i$, $B_j = \int_0^T\beta_j$. An $nT$-periodic coexistence state is a positive $nT$-periodic solution other than $(1,1)$ (a subharmonic of order $n$).

**Theorem (one season of each).** If $k = \ell = 1$ (one prey season followed by one predation season), then $(1,1)$ is the only $T$-periodic coexistence state, and there are exactly two non-trivial $2T$-periodic coexistence states for every $\lambda > 2/\sqrt{A_1B_1}$. If moreover $A_1 = B_1$, then for $\lambda > 2/A_1$ and every $n \ge 2$ there are at least $n$ (if $n$ is even) or $n-1$ (if $n$ is odd) non-trivial $nT$-periodic coexistence states with $u(0) = v(0)$.

**Theorem (minimal periods).** If $k = \ell = m$, all $A_i$ and $B_j$ equal $A_1$, and the supports alternate, then for $\lambda > 2/A_1$ and all $nm > 2$ the system has at least $\Phi(nm)$ coexistence states of minimal period $nT$, where $\Phi$ is Euler's totient function; for $m = 1$ these lie in distinct periodicity classes when $nm$ is odd.

**Theorem (number of seasons).** For sufficiently large $\lambda$, non-trivial $T$-periodic coexistence states exist if and only if $k + \ell \ge 4$; for $\lambda > 2/A_1$ and under the symmetry conditions above, subharmonics of all orders $n \ge 2$ exist if and only if $k + \ell \ge 2$. With two seasons of each type ($k = \ell = 2$), there are at least two $T$-periodic coexistence states for every $\lambda > \lambda_0 = \sqrt{(A_1+A_2)(B_1+B_2)/(A_1A_2B_1B_2)}$.

**Theorem (chaos).** For the planar system $x' = -\lambda\alpha(t)f(y)$, $y' = \lambda\beta(t)g(x)$ (which contains the Volterra model in logarithmic coordinates), suppose $\alpha \equiv 0 \lneq \beta$ on $[T_0,T]$ and $\alpha,\beta \gneq 0$ on $[0,T_0]$ with $\alpha\beta \ne 0$ somewhere. Then for every $\ell \ge 2$ there is $\lambda^*_\ell$ such that, for $\lambda > \lambda^*_\ell$, if $\int_{T_0}^T\beta$ exceeds a constant $K_\lambda$, the Poincaré map induces chaotic dynamics on $\ell$ symbols on a compact subset of the first quadrant.

## Expansion

In logarithmic coordinates $x = \log u$, $y = \log v$, each season is integrable: during a prey season only $x$ changes, by $\lambda(1 - e^{y})\int\alpha$, and during a predation season only $y$ changes, by $\lambda(e^{x} - 1)\int\beta$. The Poincaré map is therefore an explicit composition of shear maps, and $nT$-periodic points solve polynomial-like equations whose number of solutions is tracked by global bifurcation from $(1,1)$ as $\lambda$ crosses the eigenvalue thresholds $2/\sqrt{A_1B_1}$, $2/A_1$; the characteristic polynomials satisfy divisibility relations $h_{n_1} | h_{n_2} \iff n_1 | n_2$, which count minimal periods by the totient. Many alternating seasons make the Poincaré map stretch and fold a region in the plane, producing horseshoe-type dynamics on $\ell$ symbols.

## Sources

- Julián López-Gómez, Eduardo Muñoz-Hernández and Fabio Zanolin, "Subharmonic solutions for a class of predator-prey models with degenerate weights in periodic environments", Open Mathematics 21 (2023), 20220593, <https://doi.org/10.1515/math-2022-0593>; numbering as in arXiv:2212.11280: Theorems 2.1–2.7, Propositions 2.1–2.3 (Section 2) and Theorems 3.1–3.2 (Section 3).
