# Invariance of [0,1] and absorption for degenerate one-dimensional SDEs

Let $b:\mathbb R\to\mathbb R$ be Lipschitz and let $\sigma:\mathbb R\to\mathbb R$ satisfy the [Yamada–Watanabe condition](yamada-watanabe-pathwise-uniqueness-holder-1-2-d.md) $|\sigma(x)-\sigma(y)|\le h(|x-y|)$ with $\int_0^\varepsilon h^{-2}=\infty$. Suppose

$$\sigma(0)=\sigma(1)=0,\qquad b(0)\ge0\ge b(1).$$

Then every solution of $dX_t=b(X_t)\,dt+\sigma(X_t)\,dB_t$ with $X_0\in[0,1]$ almost surely satisfies $X_t\in[0,1]$ for all $t\ge0$ almost surely. If moreover $b(0)=b(1)=0$, then $0$ and $1$ are absorbing: almost surely, $X_t=X_\tau$ for all $t\ge\tau$, where $\tau=\inf\{t:X_t\in\{0,1\}\}$.

This applies to the Wright–Fisher diffusion with $\sigma(x)=\sqrt{x(1-x)}$ on $[0,1]$, extended by $0$, and a drift extended to a Lipschitz function on $\mathbb R$, such as one-way or two-way mutation ($b(0)\ge0\ge b(1)$) or genic selection without mutation ($b(0)=b(1)=0$).

## Depends on

- [Yamada–Watanabe pathwise uniqueness for Hölder-type diffusion coefficients](yamada-watanabe-pathwise-uniqueness-holder-1-2-d.md)

## Proof depends on

- [Strong solutions solve the martingale problem](../../markov-chains/martingale-problems/strong-solutions-solve-the-martingale-problem.md)
- [Comparison theorem for one-dimensional stochastic differential equations](comparison-theorem-for-one-dimensional-sdes.md)

## Expansion

A full proof uses the comparison theorem for one-dimensional SDEs (same diffusion coefficient satisfying the Yamada–Watanabe condition, ordered drifts, one of them Lipschitz, ordered initial values): the constant $0$ solves the equation with drift $b-b(0)\le b$, so $X\ge0$; symmetrically the constant $1$ solves the equation with drift $b-b(1)\ge b$, so $X\le1$. Absorption follows from pathwise uniqueness for the process $X_{\tau+\cdot}$, which solves the equation driven by $B_{\tau+\cdot}-B_\tau$ for the shifted filtration, as does the constant $X_\tau$. The hypotheses on the extension outside $[0,1]$ cannot be dropped: with $\sigma\equiv0$, $b=0$ on $[0,1]$ and $b(x)=-3|x|^{2/3}$ for $x<0$, the path $X_t=-t^3$ solves the equation from $0$ and leaves $[0,1]$.

## Sources

- N. Ikeda and S. Watanabe, *Stochastic Differential Equations and Diffusion Processes*, 2nd ed., North-Holland, 1989, <https://books.google.com/books?id=QZbOBQAAQBAJ>, comparison theorem (topic).
- W. Feller, *Diffusion processes in genetics* (1951), as described in E. Baake and A. Wakolbinger, *Feller's contributions to mathematical biology* (2015), <https://arxiv.org/abs/1501.05278>, Wright–Fisher boundary behaviour (motivation).
