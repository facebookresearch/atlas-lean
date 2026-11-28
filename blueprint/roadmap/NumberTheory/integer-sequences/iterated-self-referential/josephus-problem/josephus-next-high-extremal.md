# The next high extremal point of the Josephus function

Let $k \ge 2$ and let $n_e \ge 2k - 3$ be high extremal. Put $r = n_e \bmod (k - 1)$, $c = 1$ if $r < k - 2 - n_e + J_k(n_e)$ and $c = 0$ otherwise, and $n_e' = \lfloor (k(n_e + 1) - (r + 1))/(k - 1) \rfloor - c$. Then $n_e' > n_e$ is the next high extremal point (no $m$ with $n_e < m < n_e'$ is high extremal), $J_k(n_e') = (k - 1) - n_e + J_k(n_e) + k\lfloor (2n_e - J_k(n_e) - (k - 2))/(k - 1) \rfloor$, and $J_k(n) = k(n - n_e') + J_k(n_e')$ for $n_e + 1 \le n \le n_e'$. Here $J_k(n)$ is the Josephus function, the position of the survivor when every $k$-th person is eliminated from a circle of $n$ people; $m$ is low extremal when $1 \le J_k(m) \le k - 1$, and high extremal when $m + 1$ is low extremal.

## Sources

- Y. Bello-Cruz and R. Quintero-Contreras, Analytical study and efficient evaluation of the Josephus function, J. Integer Seq. 27 (2024), Article 24.3.8, Corollary 10.
