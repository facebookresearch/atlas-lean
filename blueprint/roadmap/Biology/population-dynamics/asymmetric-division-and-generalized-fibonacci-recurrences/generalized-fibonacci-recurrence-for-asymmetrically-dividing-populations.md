# Generalized Fibonacci recurrence for asymmetrically dividing populations

**Model.** Fix integers $1 \le k < m$. A bacterium born at time $0$ first divides at time $m$. From then on every division produces a faster-growing child that divides $k$ time units later and a slower-growing child that divides $m$ time units later, and all descendants follow the same rule. Let $a_n$ be the number of bacteria alive during $[n, n+1)$, $d_n$ the number of divisions at time $n$, and $b_n$, $c_n$ the numbers of living bacteria with lifetime $k$ and $m$.

**Theorem.** Each of $(a_n)$, $(d_n)$, $(b_n)$, $(c_n)$ satisfies the generalized Fibonacci recurrence

$$g_n = g_{n-k} + g_{n-m},$$

with initial conditions $a_0 = \dots = a_m = 1$; $d_0 = \dots = d_{m-1} = 0$, $d_m = 1$; and analogous ones for $b$ and $c$. Hence all grow like $x_*^{-n}$, where $x_* \in (0,1)$ is the unique positive root of $1 - x^k - x^m = 0$.

**Theorem (diagonal sums of Pascal's triangle).** Let $T_n = \sum_{x,y \ge 0,\ kx + my = n}\binom{x+y}{x}$ be the sum of the entries of Pascal's triangle on the line $kx + my = n$, which satisfies $T_n = T_{n-k} + T_{n-m}$ for $n \ge m$. If $\gcd(k,m) = 1$, then for all $n \ge 0$

$$T_n = \sum_{j=0}^{\lfloor (n+m)/k\rfloor}\binom{\lfloor (n - jk)/m\rfloor + j + 1}{j+1} - \sum_{j=0}^{\lfloor (n+m-1)/k\rfloor}\binom{\lfloor (n - 1 - jk)/m\rfloor + j + 1}{j+1}.$$

The population count $a_n$ equals, for $n \ge m - k$, the total weight of the edges crossing the vertical line $x = n + m - k$ in a $(k,m)$-weighted Pascal's triangle that encodes the division history.

## Expansion

At each time the bacteria dividing now are exactly those born $k$ steps earlier as fast children or $m$ steps earlier as slow children, and each division at time $n - k$ (respectively $n - m$) created exactly one fast (respectively slow) child, which gives $d_n = d_{n-k} + d_{n-m}$; the other counts are linear combinations of shifted division counts and inherit the recurrence. A division history is a word in the letters "fast" and "slow", and a cell dividing at time $n$ corresponds to a word with $x$ fast and $y$ slow steps and $kx + my = n$, counted by $\binom{x+y}{x}$; this is the link to diagonals of Pascal's triangle. The closed formula counts lattice points under the line $kx + my = n$ column by column using the hockey-stick identity and takes the difference between the cumulative counts at $n$ and $n - 1$.

## Sources

- Natasha Blitvić, Vicente I. Fernandez, "On a Generalized Fibonacci Recurrence", arXiv (2019). Section 2 (model, Theorem 1), Lemma 1, Theorem 2, Equation (T). <https://doi.org/10.48550/arXiv.1901.04080>
