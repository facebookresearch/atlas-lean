# Exponential martingale of a positive test function in a martingale problem

Let $X$ solve the [martingale problem](martingale-problems-generic-definition.md) for $L$ with respect to $(\mathcal F_t)$, with càdlàg or continuous paths in $E$. Let $g\in\mathcal D(L)$ satisfy $g\ge c$ on $E$ for a constant $c>0$, with $Lg$ bounded. Then

$$Z_t=\frac{g(X_t)}{g(X_0)}\exp\Bigl(-\int_0^t\frac{Lg}{g}(X_s)\,ds\Bigr)$$

is an $(\mathcal F_t)$-martingale with $Z_0=1$, and $0\le Z_t\le\frac{\lVert g\rVert_\infty}{c}\,e^{t\lVert Lg\rVert_\infty/c}$, so it is bounded on bounded time intervals. A typical case is a diffusion on $[0,1]$ with $\mathcal D(L)\supseteq C^2([0,1])$ and $g\in C^2([0,1])$ strictly positive. For $g$ constant, $Lg=0$ and $Z\equiv1$.

## Depends on

- [Martingale problems](martingale-problems-generic-definition.md)
- [Product rule for martingale-problem martingales and continuous finite-variation factors](product-rule-for-mp-martingales-and-continuous-f.md)

## Proof depends on

- [General optional stopping for uniformly integrable martingales](../../martingales/optional-stopping-theorem/integral-stopped-value-at-top-eq-of-unif.md)

## Expansion

A full proof page must establish:

- The product rule applied to $f=g$ and $k=Lg/g$, which is bounded measurable: then $Lg-kg=0$, so $g(X_t)V_t$ with $V_t=\exp(-\int_0^tk(X_s)\,ds)$ is a martingale; dividing by the bounded positive $\mathcal F_0$-measurable $g(X_0)$ preserves the martingale property.
- The bound on $Z_t$ and the constant case.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://doi.org/10.1002/9780470316658>, Ch. 4, Sec. 3 (exponential martingales for martingale problems).
