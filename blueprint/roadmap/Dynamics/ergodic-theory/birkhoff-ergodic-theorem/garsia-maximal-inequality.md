# Maximal ergodic theorem

Let $\mu$ be a measure on $X$, $T : X \to X$ a measurable map preserving $\mu$, $f : X \to \mathbb{R}$ an integrable
function and $N \ge 1$. Write $S_n f(x) = \sum_{k=0}^{n-1} f(T^k x)$. Then

$$\int_{\{x \,:\, \max_{1 \le n \le N} S_n f(x) > 0\}} f \, d\mu \ge 0.$$

This is the finite form, due to Garsia, of Hopf's maximal ergodic theorem; letting $N \to \infty$ gives the
[Hopf maximal ergodic theorem](maximal-ergodic.md).

## Sources

- E. Hopf, *The general temporally discrete Markoff process*, J. Rational Mech. Anal. 3 (1954), 13–45.
- A. M. Garsia, *A simple proof of E. Hopf's maximal ergodic theorem*, J. Math. Mech. 14 (1965), 381–382.
