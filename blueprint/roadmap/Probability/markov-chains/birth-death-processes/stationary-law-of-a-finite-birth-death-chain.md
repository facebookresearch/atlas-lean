# Stationary law of a finite birth–death chain

Let $K \ge 0$ and let $Q$ be a rate matrix on $\{0, \dots, K\}$ with jumps only between neighboring states. Write $\lambda_n=Q_{n,n+1}\ge 0$ for $n<K$ and $\mu_n=Q_{n,n-1}>0$ for $1\le n\le K$. The [unnormalized weights](finite-birth-death-weight.md) are $w_0=1$ and $w_n=\prod_{i<n}\lambda_i/\mu_{i+1}$. Then $\pi_n=w_n/\sum_{m\le K} w_m$ is the unique probability vector with $\pi Q=0$. It is in detailed balance with $Q$, hence invariant under the transition semigroup. If $\lambda_k=0$, both $w_n$ and $\pi_n$ vanish for every $n>k$.

Proof. Detailed balance $\lambda_n\pi_n = \mu_{n+1}\pi_{n+1}$ holds by construction and [implies invariance under the transition semigroup](../finite-continuous-time-markov-chains/stationarity-and-detailed-balance-for-finite-con/vec-mul-ctmc-transition.md). Conversely, summing the equations of $\pi Q = 0$ for the states $0, \dots, n$ gives $\lambda_n\pi_n = \mu_{n+1}\pi_{n+1}$ for each $n < K$, so $\pi_{n+1} = \pi_n\lambda_n/\mu_{n+1}$ and $\pi$ is proportional to $w$; the sum of the weights is at least $w_0 = 1$.

## Background

- [Normalized balance weights of a birth–death rate sequence](birth-death-balance-weights.md): the balance weights on the nonnegative integers.

## Sources

- K. Sigman, *Continuous-Time Markov Chains* (lecture notes, IEOR 6711), Columbia University, 2009, Section 1.13, item 2 (Birth and Death processes), equations (26)-(27), <http://www.columbia.edu/~ks20/stochastic-I/stochastic-I-CTMC.pdf>. The source states a special case or part of the statement; the rest is derived on this page.
