# $R_0$ under separable and preferential mixing

Use the notation of the [next-generation operator](next-generation-operator-and-r0-in-heterogeneous-populations.md): h-states $\xi \in \Omega$, susceptible density $S \ge 0$, and integrated infectivity $\int_0^\infty A(\tau, \xi, \eta)\, d\tau$.

**Separable mixing.** If $\int_0^\infty A(\tau, \xi, \eta)\, d\tau = a(\xi)\, b(\eta)$ with $a, b \ge 0$, then $K\phi = S a \int_\Omega b\,\phi$ has one-dimensional range spanned by $S a$, and

$$R_0 = \int_\Omega b(\eta)\, S(\eta)\, a(\eta)\, d\eta .$$

With the normalization $\int_\Omega S a = 1$, $S a$ is the probability density of the h-state at infection, $b(\eta)$ is the expected number of secondary cases of an individual infected in state $\eta$, and $R_0$ is the mean of $b$ under that density. Proportionate mixing is the case $b = c\,a$ for a constant $c$.

**Separable mixing with within-group enhancement.** If the h-state is constant over epidemiological time and

$$(K\phi)(\xi) = S(\xi)\Bigl\{ a(\xi) \int_\Omega b(\eta)\phi(\eta)\, d\eta + c(\xi)\phi(\xi) \Bigr\},$$

with $c \ge 0$, then a positive eigenvalue $\varrho$ with $\varrho > \operatorname{ess\,sup} cS$ satisfies the characteristic equation

$$\int_\Omega \frac{b(\xi) S(\xi) a(\xi)}{\varrho - c(\xi) S(\xi)}\, d\xi = 1 .$$

The left side decreases in $\varrho$ to $0$. Hence $R_0 > 1$ if and only if either $\operatorname{ess\,sup}_\xi c(\xi)S(\xi) > 1$, or $cS \le 1$ and

$$\int_\Omega \frac{b(\xi) S(\xi) a(\xi)}{1 - c(\xi) S(\xi)}\, d\xi > 1 .$$

The last integral is the expected number of cross-group infections produced by a "clan": the chain of infections a case in state $\xi$ starts within its own group, of mean total size $(1 - c(\xi)S(\xi))^{-1}$.

## Depends on

- [Basic reproduction ratio as the spectral radius of the next-generation operator](next-generation-operator-and-r0-in-heterogeneous-populations.md)

## Expansion

In the separable case $K(Sa) = (\int b S a)\, Sa$, and every eigenvector with a nonzero eigenvalue lies in the range of $K$, so $\int bSa$ is the only nonzero eigenvalue. In the enhanced case, $K\phi = \varrho\phi$ gives $\phi = (\varrho - cS)^{-1} S a \int b\phi$; multiplying by $b$ and integrating cancels $\int b\phi$ and leaves the characteristic equation. Monotonicity in $\varrho$ means the largest root exceeds $1$ exactly when the left side at $\varrho = 1$ exceeds $1$ (or blows up because $cS$ reaches $1$).

## Sources

- O. Diekmann, J. A. P. Heesterbeek and J. A. J. Metz, *On the definition and the computation of the basic reproduction ratio $R_0$ in models for infectious diseases in heterogeneous populations*, J. Math. Biol. 28 (1990), 365–382, <https://doi.org/10.1007/BF00178324>, Section 3.1, Eqs. (3.1)–(3.6) (separable mixing), and Section 3.2, Eqs. (3.7)–(3.11) (separable mixing with enhanced infection within each group).
