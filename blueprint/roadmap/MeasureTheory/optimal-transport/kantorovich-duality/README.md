# Kantorovich duality

Let $X$ and $Y$ be Polish spaces, $\mu$ and $\nu$ Borel probability measures on them, and
$c : X \times Y \to [0, \infty]$ lower semicontinuous. Then

$$\inf_\pi \int_{X \times Y} c \, d\pi = \sup \Bigl\{ \int_Y \varphi \, d\nu - \int_X \psi \, d\mu \Bigr\},$$

where the infimum runs over the couplings $\pi$ of $\mu$ and $\nu$, and the supremum over pairs of
bounded continuous functions $\psi$ on $X$ and $\varphi$ on $Y$ with
$\varphi(y) - \psi(x) \le c(x, y)$ for all $x$ and $y$. Both sides may be $+\infty$.

## Idea

The left side is the cheapest way to transport $\mu$ onto $\nu$ when moving a unit of mass from $x$
to $y$ costs $c(x, y)$. The right side is a pricing problem: a carrier buys the goods at $x$ for
$\psi(x)$ and sells them at $y$ for $\varphi(y)$, and stays competitive as long as
$\varphi(y) - \psi(x) \le c(x, y)$. Integrating this constraint against any coupling shows that
every price system earns at most the cost of every plan; the theorem is that there is no gap. For
the cost $c = d$ on a metric space the dual becomes a supremum over $1$-Lipschitz functions, the
Kantorovich–Rubinstein formula.

## Statements

- [Kantorovich duality for lower semicontinuous costs](kantorovich-duality-lsc.md)
- [Kantorovich duality on compact metric spaces](kantorovich-duality-compact.md): the same duality on compact metric spaces, for continuous real-valued costs, with the dual constraint written $\varphi(x) + \psi(y) \le c(x, y)$.
- [Coupling of two probability measures](is-coupling.md): a definition used in the statement.
- [Values of the transport cost over couplings](primal-values.md): a definition used in the compact case.
- [Dual feasible pair of potentials](dual-feasible.md): a definition used in the compact case.

## Sources

- L. V. Kantorovich, *On the translocation of masses* (1942); English translation in J. Math. Sci. 133 (2006).
- C. Villani, *Optimal Transport: Old and New*, Grundlehren der mathematischen Wissenschaften 338, Springer, 2009, Chapter 5.
