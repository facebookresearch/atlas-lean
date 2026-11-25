# Consistency of sample average approximation over finitely many decisions

Let $X$ be finite and nonempty, and let $\xi_1, \xi_2, \dots$ be i.i.d. with $C(x, \xi_1)$ integrable for each $x$, $f(x) = E[C(x, \xi_1)]$ and $\hat f_N(x) = N^{-1}\sum_{i \le N}C(x, \xi_i)$. Almost surely $\max_x|\hat f_N(x) - f(x)| \to 0$, and for all large $N$ every minimizer of $\hat f_N$ minimizes $f$.

## Proof depends on

- [Strong law of large numbers from the ergodic theorem](../../../Dynamics/ergodic-theory/birkhoff-ergodic-theorem/tendsto-average-coordinates-ae.md): almost-sure convergence for each of the finitely many $x$, after transporting the i.i.d. sequence to the coordinate process of the product law.

## Sources

- A. Shapiro, D. Dentcheva and A. Ruszczyński, *Lectures on Stochastic Programming: Modeling and Theory*, SIAM, 2009, Section 5.3.1, finite feasible set, <https://bpb-us-e1.wpmucdn.com/sites.gatech.edu/dist/4/1470/files/2021/03/SPbook.pdf>. The source states a special case or part of the statement; the rest is derived on this page.
