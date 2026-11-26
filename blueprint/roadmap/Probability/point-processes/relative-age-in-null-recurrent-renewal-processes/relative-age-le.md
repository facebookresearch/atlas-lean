# Relative age event of a renewal process

Let $X_0, X_1, \dots$ be real random variables on $\Omega$ with partial sums $S_n = X_0 + \dots + X_{n-1}$ (so $S_0 = 0$), and let $t, u \in \mathbb{R}$. Define the event

$$\{U_t \le u\} = \{\omega : \exists n \in \mathbb{N},\ S_n(\omega) \le t < S_{n+1}(\omega) \text{ and } t - S_n(\omega) \le u\, X_n(\omega)\}.$$

The test is existential and is defined for arbitrary increments. When the $X_i$ are positive, the epochs increase strictly and at most one $n$ satisfies $S_n \le t < S_{n+1}$: then $t$ lies in the renewal cycle $[S_n, S_{n+1})$ of length $D_t = X_n$, the age is $A_t = t - S_n$, and the event says that the relative age $U_t = A_t / D_t$ is at most $u$. For other increments several cycles can cover $t$: for increments $2, -2, 4, \dots$ the time $t = 1$ lies in $[0, 2)$ and in $[0, 4)$, with ratios $1/2$ and $1/4$, so the event holds at $u = 1/3$ although there is no unique relative age.
