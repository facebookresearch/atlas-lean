# Relative age event of a renewal process

Let $X_0, X_1, \dots$ be real random variables on $\Omega$ with renewal epochs $S_n = X_0 + \dots + X_{n-1}$ (so $S_0 = 0$), and let $t, u \in \mathbb{R}$. The event $\{U_t \le u\}$ that the relative age at time $t$ is at most $u$ is

$$\{U_t \le u\} = \{\omega : \exists n \in \mathbb{N},\ S_n(\omega) \le t < S_{n+1}(\omega) \text{ and } t - S_n(\omega) \le u\, X_n(\omega)\}.$$

Here $t$ lies in the renewal cycle $[S_n, S_{n+1})$ of length $D_t = X_n$, the age is $A_t = t - S_n$, and $U_t = A_t / D_t$.
