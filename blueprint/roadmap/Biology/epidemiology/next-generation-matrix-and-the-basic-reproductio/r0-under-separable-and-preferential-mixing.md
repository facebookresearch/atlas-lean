# $R_0$ under separable mixing with within-group enhancement

Use the notation of the [next-generation operator](next-generation-operator-and-r0-in-heterogeneous-populations.md): h-states $\xi \in \Omega$, susceptible density $S \ge 0$, and integrated infectivity $\int_0^\infty A(\tau, \xi, \eta)\, d\tau$.

**Separable mixing.** If $\int_0^\infty A(\tau, \xi, \eta)\, d\tau = a(\xi)\, b(\eta)$ with $a, b \ge 0$ measurable, $S a \in L^1(\Omega)$ and $b \in L^\infty(\Omega)$, then $K\phi = S a \int_\Omega b\,\phi$ and $R_0 = \int_\Omega b S a$ by [$R_0$ for a separable kernel](../next-generation-operator-and-basic-reproduction/generation-growth-eq-integral-of-separab.md). Proportionate mixing is the case $b = c\,a$ for a constant $c$.

**Separable mixing with within-group enhancement.** If the h-state is constant over epidemiological time and

$$(K\phi)(\xi) = S(\xi)\Bigl\{ a(\xi) \int_\Omega b(\eta)\phi(\eta)\, d\eta + c(\xi)\phi(\xi) \Bigr\},$$

with $a, b$ as in the separable case and $c \ge 0$ measurable, $cS \in L^\infty(\Omega)$, put $\sigma = \operatorname{ess\,sup} cS$. Every eigenvalue $\varrho > \sigma$ of $K$ satisfies the characteristic equation $F(\varrho) = 1$, where

$$F(\varrho) = \int_\Omega \frac{b(\xi) S(\xi) a(\xi)}{\varrho - c(\xi) S(\xi)}\, d\xi, \qquad \varrho > \sigma .$$

$F$ is nonincreasing and tends to $0$ as $\varrho \to \infty$; let $F(\sigma^+) = \lim_{\varrho \downarrow \sigma} F(\varrho) \in [0, \infty]$. Then $R_0 > 1$ if and only if either $\sigma > 1$, or $\sigma \le 1$ and

$$F(1^+) = \lim_{\varrho \downarrow 1} \int_\Omega \frac{b(\xi) S(\xi) a(\xi)}{\varrho - c(\xi) S(\xi)}\, d\xi > 1 .$$

When $\sigma < 1$, $F(1^+)$ is the integral of $bSa/(1 - cS)$. On the set where $c(\xi)S(\xi) < 1$, the factor $(1 - c(\xi)S(\xi))^{-1}$ is the mean total size of the "clan", the chain of infections a case in state $\xi$ starts within its own group, so for $\sigma < 1$ the integral $F(1)$ is the expected number of cross-group infections produced by a clan.

## Depends on

- [Dominant eigenvalue and real-time growth for the next-generation operator of a heterogeneous population](next-generation-operator-and-r0-in-heterogeneous-populations.md)
- [The basic reproduction ratio `R₀`](../next-generation-operator-and-basic-reproduction/generation-growth.md)
- [`R₀` for a separable kernel](../next-generation-operator-and-basic-reproduction/generation-growth-eq-integral-of-separab.md)

## Expansion

In the enhanced case, $K\phi = \varrho\phi$ with $\varrho > \sigma$ gives $\phi = (\varrho - cS)^{-1} S a \int b\phi$, and $\int b\phi \ne 0$ since otherwise $\phi = 0$; multiplying by $b$ and integrating cancels $\int b\phi$ and leaves $F(\varrho) = 1$. Since $0 \le M \le K$ for the multiplication operator $M\phi = cS\phi$, positivity gives $R_0 \ge r(M) = \sigma$. Outside the spectrum of $M$, $\varrho$ lies in the spectrum of $K$ exactly when $F(\varrho) = 1$, so $R_0 = \sigma$ if $F(\sigma^+) \le 1$ and otherwise $R_0$ is the unique root of $F = 1$ in $(\sigma, \infty)$. Monotonicity of $F$ then gives the criterion, with the one-sided limit $F(1^+)$ covering the boundary case $\sigma = 1$, where the integrand at $\varrho = 1$ can be $0/0$.

## Sources

- O. Diekmann, J. A. P. Heesterbeek and J. A. J. Metz, *On the definition and the computation of the basic reproduction ratio $R_0$ in models for infectious diseases in heterogeneous populations*, J. Math. Biol. 28 (1990), 365–382, <https://doi.org/10.1007/BF00178324>, Section 3.2, Eqs. (3.7)–(3.11) (separable mixing with enhanced infection within each group; the clan-size interpretation follows (3.10)).
