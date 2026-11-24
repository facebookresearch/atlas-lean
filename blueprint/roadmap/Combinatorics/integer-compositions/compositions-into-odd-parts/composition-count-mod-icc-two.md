# Compositions with parts at most N and an even or odd number of parts

Let $N \ge 2$ and $n \ge 1$ be natural numbers, and let $b_{[N]}(2, q; n)$ and $c_{[N]}(2, q; n)$ be the numbers of compositions and of circular compositions of $n$ with all parts in $\{1, \dots, N\}$ and a number of parts congruent to $q$ modulo $2$. Let $F^{(N)}_n$ be the $N$-step Fibonacci numbers ($F^{(N)}_0 = 0$, $F^{(N)}_1 = 1$, and $F^{(N)}_n = \sum_{i=1}^{N} F^{(N)}_{n-i}$ for $n \ge 2$, terms with negative index read as $0$), and let $L^{(N)}_n$ be the $N$-step Lucas numbers, given for $n \ge 1$ by $L^{(N)}_n = 2^n - 1$ for $1 \le n \le N$ and $L^{(N)}_n = \sum_{i=1}^{N} L^{(N)}_{n-i}$ for $n > N$. Then, in $\mathbb{Q}$,

$$b_{[N]}(2, 0; n) = \frac{F^{(N)}_{n+1}}{2} + \varepsilon, \qquad b_{[N]}(2, 1; n) = \frac{F^{(N)}_{n+1}}{2} - \varepsilon,$$

where $\varepsilon = \frac{1}{2}$ if $n \equiv 0 \pmod{N+1}$, $\varepsilon = -\frac{1}{2}$ if $n \equiv 1 \pmod{N+1}$, and $\varepsilon = 0$ otherwise; and

$$c_{[N]}(2, 0; n) = \frac{L^{(N)}_n}{2} + \delta, \qquad c_{[N]}(2, 1; n) = \frac{L^{(N)}_n}{2} - \delta,$$

where $\delta = \frac{N}{2}$ if $n \equiv 0 \pmod{N+1}$ and $\delta = -\frac{1}{2}$ otherwise. For $n \ge 1$ these $L^{(N)}_n$ agree with the $N$-step Lucas numbers of Noe and Post, defined by $L_0 = N$, $L_k = -1$ for $k < 0$ and the sum of the $N$ preceding terms.

## Sources

- Joshua P. Bowman, *Compositions with an Odd Number of Parts, and Other Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6, Theorem 12.
