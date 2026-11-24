# All-time uniform and mean-square convergence of scalar Picard iteration

Let $B$ have real Brownian finite-dimensional laws, be adapted to $(\mathcal F_t)$, and have increments independent of the past filtration. Assume every $\mathcal F_t$ contains every $P$-null set. Let $\sigma,b:\mathbb R\to\mathbb R$ be globally Lipschitz with a common constant $K\ge0$, and fix $x\in\mathbb R$.

Suppose an all-time Picard sequence starts at $X^0_t=x$ and obeys

$$X^{n+1}_t=x+J^n_t+\int_0^t b(X^n_s)\,ds$$

for every sample and time. For each $n$, $X^n$ is progressive, continuous on every path, and has finite integrated second moment on each finite horizon. Each $J^n$ is a progressive martingale continuous on every path, with fixed-time almost-sure equality to the actual Itô integral of $\sigma(X^n)$ at every nonnegative time.

There is one progressive real process $Y$, continuous on every path, such that outside a **single null set**, for every finite $T\ge0$,

$$X^n\longrightarrow Y\quad\text{uniformly on }[0,T].$$

Moreover, for every $T\ge0$,

$$\mathbb E\sup_{0\le s\le T}|Y_s|^2<\infty,\qquad
\lim_{n\to\infty}\mathbb E\sup_{0\le s\le T}|X^n_s-Y_s|^2=0.$$

These expectations are nonnegative extended integrals. The same $Y$ works for all horizons and for both modes of convergence. This statement concerns the Picard limit; it does not yet assert the limiting stochastic integral equation. Completeness is a sufficient hypothesis for the construction, not a necessity claim. Right continuity of the filtration and continuous driving paths are not required once the specified sequence is supplied.

The square roots of the factorial increment bounds are summable. In the Banach space of continuous paths on a compact interval, this yields both an almost-sure norm limit and an $L^2$ limit. Uniqueness of limits identifies them. Intersecting the full-measure events over integer horizons supplies one all-time process; completeness of each filtration sigma algebra makes a common null-set fallback compatible with adaptedness. This is the convergence step of Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus* (2016), Theorem 8.3, using the complete-filtration convention in Definition 8.1.
