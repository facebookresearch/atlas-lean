# Martingale problem under an exponential tilt

Let $E\subseteq\mathbb R$ be a compact interval (for example $[0,1]$) and $Lf=\tfrac a2f''+bf'$ with $a\ge0$ and $b$ bounded measurable on $E$, $a$ bounded, on $\mathcal D(L)=C^2(E)$. Let $X$ solve the [martingale problem](martingale-problems-generic-definition.md) for $L$ with respect to $(\mathcal F_t)$ on $(\Omega,\mathcal F,\mathbb P)$, with continuous paths. Let $g\in C^2(E)$ with $g\ge c>0$, and let

$$Z_t=\frac{g(X_t)}{g(X_0)}\exp\Bigl(-\int_0^t\frac{Lg}{g}(X_s)\,ds\Bigr),$$

an $(\mathcal F_t)$-martingale by the [exponential martingale lemma](exponential-martingale-for-positive-test-functio.md). Fix $t_0>0$ and define $\mathbb Q$ on $\mathcal F_{t_0}$ by $d\mathbb Q=Z_{t_0}\,d\mathbb P$. Then under $\mathbb Q$ the process $(X_t)_{t\le t_0}$ solves the martingale problem on $[0,t_0]$ for

$$L^gf=Lf+a\,\frac{g'}g\,f',\qquad f\in C^2(E),$$

with the same initial law. The same holds on a simplex for $Lf=\tfrac12\sum_{i,j}a_{ij}\partial_i\partial_jf+\sum_ib_i\partial_if$, with $L^gf=Lf+\sum_{i,j}a_{ij}\frac{\partial_ig}g\,\partial_jf$.

Examples on $E=[0,1]$ with $a(x)=x(1-x)$: for $g(x)=e^{\alpha x}$, $L^g$ has drift $b(x)+\alpha x(1-x)$. So tilting the neutral Wright–Fisher generator ($b=0$) gives genic selection with coefficient $\alpha$, and tilting a Wright–Fisher generator with mutation drift $b$ adds the same selection term to it. Tilting $L^g$ by $1/g$ returns $L$.

## Depends on

- [Exponential martingale of a positive test function in a martingale problem](exponential-martingale-for-positive-test-functio.md)
- [Product rule for martingale-problem martingales and continuous finite-variation factors](product-rule-for-mp-martingales-and-continuous-f.md)
- [Martingale problems](martingale-problems-generic-definition.md)

## Proof depends on

- [General optional stopping for uniformly integrable martingales](../../martingales/optional-stopping-theorem/integral-stopped-value-at-top-eq-of-unif.md)

## Expansion

A full proof page must establish:

- The identity $L(fg)=g\,Lf+f\,Lg+a\,f'g'$ for $f,g\in C^2(E)$, so $L^gf=\bigl(L(fg)-f\,Lg\bigr)/g$.
- The [product rule](product-rule-for-mp-martingales-and-continuous-f.md) applied to $fg$ and $k=Lg/g$: $f(X_t)Z_t-f(X_0)-\int_0^tZ_s\,L^gf(X_s)\,ds$ is a $\mathbb P$-martingale (no semimartingale product rule is needed).
- The change of measure: a process $Y$ with $YZ$ a $\mathbb P$-martingale is a $\mathbb Q$-martingale on $[0,t_0]$, applied to $f(X_t)-f(X_0)-\int_0^tL^gf(X_s)\,ds$ via Fubini; the initial law is unchanged since $Z_0=1$.
- The examples and the inverse tilt.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://doi.org/10.1002/9780470316658>, Ch. 4, Sec. 3 (exponential martingales and change of measure for martingale problems).
