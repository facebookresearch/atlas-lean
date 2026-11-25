# Edge condition for permutiples

Let $n \ge 1$, $b$ and $k$ be natural numbers, let $\sigma$
be a permutation of $\{0, \dots, k\}$ and let $(d_k, \dots, d_0)_b$ be an
$(n, b, \sigma)$-permutiple, that is, $d_i < b$ for all $i$ and
$(d_k, \dots, d_0)_b = n \cdot (d_{\sigma(k)}, \dots, d_{\sigma(0)})_b$. Then for every
$0 \le j \le k$, $\lambda(d_j + (b - n) d_{\sigma(j)}) \le n - 1$, where $\lambda$ is the least
non-negative residue modulo $b$ and $b - n$ is computed in the integers, so it may be negative.

The hypothesis $n \ge 1$ is needed: for $n = 0$ the only permutiples have all digits zero and the
bound would read $0 \le -1$.

## Sources

- Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*, INTEGERS 25 (2025), Article A111, Theorem 3, quoting Holt, *Finding Permutiples of a Known Base and Multiplier*.
