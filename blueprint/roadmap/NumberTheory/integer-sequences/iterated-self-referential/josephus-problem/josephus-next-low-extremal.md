# The next low extremal point of the Josephus function

Let $k \ge 2$ and let $n \ge 2k - 3$ be low extremal. Put $r = n \bmod (k - 1)$, $c = 1$ if $r < J_k(n)$ and $c = 0$ otherwise, and $n' = \lfloor (kn - r)/(k - 1) \rfloor - c + 1$. Then $n' > n$ is the next low extremal point (no $m$ with $n < m < n'$ is low extremal), and $J_k(n') = k - n' + J_k(n) + k\lfloor (n - J_k(n))/(k - 1) \rfloor$. Here $J_k(n)$ is the Josephus function, the position of the survivor when every $k$-th person is eliminated from a circle of $n$ people; $m$ is low extremal when $1 \le J_k(m) \le k - 1$, and high extremal when $m + 1$ is low extremal.

This is Corollary 11 without its last formula, which fails as printed already for $k = 2$, where it gives $3$ for the value $J_2(2) = 1$.

## Sources

- Y. Bello-Cruz and R. Quintero-Contreras, Analytical study and efficient evaluation of the Josephus function, J. Integer Seq. 27 (2024), Article 24.3.8, Corollary 11.
