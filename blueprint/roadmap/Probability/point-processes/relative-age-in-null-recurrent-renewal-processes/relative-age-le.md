# Relative age event of a renewal process

Let $X_0, X_1, \dots$ be real random variables on $\Omega$ with partial sums $S_n = X_0 + \dots + X_{n-1}$ (so $S_0 = 0$), and let $t, u \in \mathbb{R}$. Define the event

$$\{U_t \le u\} = \{\omega : \exists n \in \mathbb{N},\ S_n(\omega) \le t < S_{n+1}(\omega) \text{ and } t - S_n(\omega) \le u\, X_n(\omega)\}.$$

The test is existential and is defined for arbitrary increments. At an outcome where exactly one interval $[S_n, S_{n+1})$ contains $t$, that interval is the cycle covering $t$, of length $D_t = X_n$, the age is $A_t = t - S_n$, and the event says that the relative age $U_t = A_t / D_t$ is at most $u$. If no interval contains $t$ the event fails for every $u$: for $X_n = 2^{-(n+1)}$ and $t = 1$ the partial sums $1 - 2^{-n}$ never reach $t$. If several intervals contain $t$ there is no unique relative age: for increments $2, -2, 4, \dots$ the time $t = 1$ lies in $[0, 2)$ and in $[0, 4)$, with ratios $1/2$ and $1/4$, so the event holds at $u = 1/3$. For a renewal process with independent, identically distributed positive recurrence times $X_i$, the partial sums increase strictly and diverge almost surely, so every $t \ge 0$ lies in exactly one cycle and $\{U_t \le u\}$ is the event that the relative age at time $t$ is at most $u$.
