# Deterministic clock change for martingale problems

Let $\nu : [0, \infty) \to (0, \infty)$ be continuous and $\Lambda(t) = \int_0^t \nu(s)^{-1}\, ds$, a strictly increasing $C^1$ function with $\Lambda(0) = 0$, and let $L_0 f(x) = \tfrac12 x(1 - x) f''(x)$.

1. If $Y$ solves the martingale problem for $L_0$ with respect to a filtration $(\mathcal G_r)$, then $X_t = Y_{\Lambda(t)}$ solves the [time-inhomogeneous martingale problem](time-inhomogeneous-martingale-problem.md) for $A_t = \nu(t)^{-1} L_0$ with respect to $\mathcal F_t = \mathcal G_{\Lambda(t)}$.
2. Conversely, if $X$ solves the time-inhomogeneous martingale problem for $(A_t)$ with respect to $(\mathcal F_t)$, then $Y_r = X_{\Lambda^{-1}(r)}$ solves the martingale problem for $L_0$ on $[0, \Lambda(\infty))$ with respect to $\mathcal G_r = \mathcal F_{\Lambda^{-1}(r)}$.

Both follow from the substitution $r = \Lambda(s)$, $dr = \nu(s)^{-1}\, ds$, in the compensator: $\int_0^t \nu(s)^{-1} L_0 f(Y_{\Lambda(s)})\, ds = \int_0^{\Lambda(t)} L_0 f(Y_r)\, dr$.

## Depends on

- [Time-inhomogeneous martingale problem](time-inhomogeneous-martingale-problem.md)

## Proof depends on

- [Martingale problem for the Wright–Fisher diffusion](is-wright-fisher-solution.md)

## Expansion

A full proof page must still establish:

- the change of variables in the compensator integral and the transfer of the martingale property between the filtrations $(\mathcal G_{\Lambda(t)})$ and $(\mathcal F_{\Lambda^{-1}(r)})$;
- the restriction of the converse to $[0, \Lambda(\infty))$ when $\Lambda(\infty) < \infty$.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, Chapter 6 (random time changes, deterministic case), <https://doi.org/10.1002/9780470316658>
- S. P. Otto and M. C. Whitlock, "The probability of fixation in populations of changing size", *Genetics*, 1997, <https://docslib.org/download/3490747/the-probability-of-fixation-in-populations-of-changing-size> (background)
