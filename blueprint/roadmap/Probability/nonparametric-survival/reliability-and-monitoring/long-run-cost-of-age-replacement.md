# Long-run cost rate of an age-replacement policy

Components with i.i.d. lifetimes $L > 0$ are replaced at failure or at age $T > 0$, whichever comes first; a failure at exactly age $T$ counts as a failure. A failure replacement costs $c_f$ and a planned replacement $c_p$. The replacement cycles are i.i.d. with length $\min(L, T) \in (0, T]$ and cost $c_p \mathbf 1\{L > T\} + c_f \mathbf 1\{L \le T\}$, so by the renewal–reward theorem the long-run cost per unit time is almost surely $\bigl(c_p P(L > T) + c_f P(L \le T)\bigr)/E[\min(L, T)]$. Replacement at failure only ($T = \infty$) has long-run cost rate $c_f/E[L]$, which requires $E[L] < \infty$; comparisons with it need that hypothesis.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- The renewal–reward theorem for i.i.d. cycles with finite positive mean length and integrable reward.

## Sources

- K. Sigman, *Renewal reward theorem*, lecture notes, Columbia University, 2009, <http://www.columbia.edu/~ks20/stochastic-I/stochastic-I-RRT.pdf>, Theorem 2.1
