# Product rule for martingale-problem martingales and continuous finite-variation factors

Let $X$ solve the [martingale problem](martingale-problems-generic-definition.md) for $L$ with respect to $(\mathcal F_t)$, with càdlàg paths in $E$, let $f\in\mathcal D(L)$, and let $k$ be a bounded measurable function on $E$ (for instance bounded continuous). Put $V_t=\exp\bigl(-\int_0^tk(X_s)\,ds\bigr)$, a continuous adapted process of finite variation. Then

$$f(X_t)\,V_t-f(X_0)-\int_0^tV_s\,(Lf-kf)(X_s)\,ds$$

is an $(\mathcal F_t)$-martingale. The proof uses only the fixed-time martingale identities and Fubini, with no stochastic integral: for $s\le t$ and $B\in\mathcal F_s$,

$$\mathbb E\bigl[\mathbf 1_B\bigl(f(X_t)V_t-f(X_s)V_s\bigr)\bigr]=\mathbb E\Bigl[\mathbf 1_B\int_s^tV_r\,(Lf-kf)(X_r)\,dr\Bigr].$$

For $k=0$, $V\equiv1$ and the statement is the martingale property of $f(X_t)-f(X_0)-\int_0^tLf(X_s)\,ds$.

## Depends on

- [Martingale problems](martingale-problems-generic-definition.md)

## Proof depends on

- [Conditional expectation](../../foundations/conditional-expectation/README.md)
- [Global existence and uniqueness for globally Lipschitz ODEs](../../../Analysis/ordinary-differential-equations/maximal-solutions-and-global-existence/ode-global-exists-of-global-lipschitz.md)

## Expansion

A full proof page must establish the displayed identity:

- Write $V_t=V_s-\int_s^tk(X_r)V_r\,dr$, so $f(X_t)V_t-f(X_s)V_s=V_s\bigl(f(X_t)-f(X_s)\bigr)-\int_s^tf(X_t)k(X_r)V_r\,dr$.
- In the first term, $\mathbf 1_BV_s$ is bounded and $\mathcal F_s$-measurable, so the martingale identity gives $\mathbb E\bigl[\mathbf 1_BV_s\int_s^tLf(X_u)\,du\bigr]$.
- In the second term, condition on $\mathcal F_r$ for each $r$: $\mathbb E[f(X_t)\mid\mathcal F_r]=f(X_r)+\mathbb E\bigl[\int_r^tLf(X_u)\,du\bigm|\mathcal F_r\bigr]$; Fubini over $s\le r\le u\le t$ and $V_s-V_u=\int_s^uk(X_r)V_r\,dr$ combine the two terms into the right-hand side.
- The case $k=0$.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://doi.org/10.1002/9780470316658>, Ch. 4, Sec. 3 (the martingales $f(X_t)\exp(-\int_0^t\cdots)$).
