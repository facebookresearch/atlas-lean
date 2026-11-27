# Every solution of the time-changed neutral martingale problem is a time-changed Wright–Fisher diffusion

Let $\nu : [0, \infty) \to (0, \infty)$ be continuous, $\Lambda(t) = \int_0^t \nu(s)^{-1}\, ds$, and $L_0 f(x) = \tfrac12 x(1 - x) f''(x)$ the neutral Wright–Fisher generator. Every solution $X$ of the [time-inhomogeneous martingale problem](time-inhomogeneous-martingale-problem.md) for $A_t = \nu(t)^{-1} L_0$ with $X_0 = x \in [0, 1]$ has the law of $Y \circ \Lambda$, where $Y$ is the neutral Wright–Fisher diffusion started at $x$. Indeed, by the converse half of the [deterministic clock change](deterministic-clock-change-for-martingale-proble.md), $X \circ \Lambda^{-1}$ solves the martingale problem for $L_0$ on $[0, \Lambda(\infty))$, and its law there is fixed by [uniqueness in law for the neutral martingale problem](../neutral-wright-fisher-martingale-problem/uniqueness-in-law-for-the-neutral-martingale-pro.md). Hence the fixation dichotomy of the [time-changed neutral diffusion](time-changed-neutral-diffusion-under-determinist.md) holds for every solution. For $\nu \equiv 1$ the statement is the uniqueness in law of the neutral martingale problem.

## Depends on

- [Time-inhomogeneous martingale problem](time-inhomogeneous-martingale-problem.md)
- [Deterministic clock change for martingale problems](deterministic-clock-change-for-martingale-proble.md)
- [Uniqueness in law for the neutral martingale problem (well-posedness)](../neutral-wright-fisher-martingale-problem/uniqueness-in-law-for-the-neutral-martingale-pro.md)
- [Time-changed neutral diffusion under deterministic population-size change: construction and fixation](time-changed-neutral-diffusion-under-determinist.md)

## Expansion

A full proof page must still establish:

- uniqueness in law of the neutral martingale problem on the finite or infinite horizon $[0, \Lambda(\infty))$;
- the transfer of the law of $X \circ \Lambda^{-1}$ back to $X$, and of the fixation statements to every solution;
- the case $\nu \equiv 1$.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, Chapter 4 (uniqueness) and Chapter 6 (random time changes), <https://doi.org/10.1002/9780470316658>
