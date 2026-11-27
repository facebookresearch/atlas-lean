# Compositions into odd parts with a part count in a residue class

Let $O$ be the set of odd natural numbers, and let $b_O(m, q; n)$ and $c_O(m, q; n)$ be the numbers of compositions and of circular compositions of $n$ with all parts odd and a number of parts congruent to $q$ modulo $m$. Let $\mathcal{F}_n$ and $\mathcal{L}_n$ be the Fibonacci and Lucas polynomials in $\mathbb{Z}[z]$: $\mathcal{F}_0 = 0$, $\mathcal{F}_1 = 1$, $\mathcal{L}_0 = 2$, $\mathcal{L}_1 = z$, and $P_{n+2} = z P_{n+1} + P_n$ for both. Let $\zeta = e^{2\pi i/m}$, and let $S(m, n, q)$ be the set of natural numbers $k$ with $2k \equiv n - q \pmod m$ (the difference taken in $\mathbb{Z}$) and $2k < n$. For natural numbers $m$, $q$ and $n$ with $q < m$ and $n \ge 1$:

$$b_O(m, q; n) = \frac{1}{m} \sum_{k=0}^{m-1} \zeta^{k(1-q)}\, \mathcal{F}_n(\zeta^k) = \sum_{k \in S(m, n, q)} \binom{n - k - 1}{k},$$

the first equality in $\mathbb{C}$ (with integer exponent $k(1 - q)$) and the second in $\mathbb{N}$, and

$$c_O(m, q; n) = -\bigl(1 + (-1)^n\bigr)[q = 0] + \frac{1}{m} \sum_{k=0}^{m-1} \zeta^{-kq}\, \mathcal{L}_n(\zeta^k) = \sum_{k \in S(m, n, q)} \frac{n}{n - k} \binom{n - k}{k},$$

the first equality in $\mathbb{C}$ and the second in $\mathbb{Q}$, where $[q = 0]$ is $1$ if $q = 0$ and $0$ otherwise. Since $2k < n$ for $k \in S(m, n, q)$, every $n - k$ is positive and $n - k - 1 \ge k$.

## Sources

- Joshua P. Bowman, *Compositions with an Odd Number of Parts, and Other Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6, Theorem 13.
