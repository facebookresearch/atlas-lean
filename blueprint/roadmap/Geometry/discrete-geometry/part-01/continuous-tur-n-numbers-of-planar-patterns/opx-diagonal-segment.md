# Continuous Turán number of a diagonal segment

Let $a, b, n$ be real numbers with
$0 < a \le n$ and $0 < b \le n$, and let $P$ be the closed segment from $(0, 0)$ to $(a, b)$.
Then the continuous Turán number satisfies $\operatorname{opx}(n, P) = (a + b)n - ab$.

The hypotheses $a \le n$ and $b \le n$ are missing from the paper, whose lower-bound construction
$(0, a) \times (0, n) \cup (0, n) \times (0, b) \subseteq [0, n]^2$ uses them: for
$0 < n < \max(a, b)$ no subset of $[0, n]^2$ contains $P$, so $\operatorname{opx}(n, P) = n^2$
(for example $a = b = 2$ and $n = 1$, where $(a + b)n - ab = 0 \ne 1$).

## Sources

- Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Theorem 4.2 (`integers-2024-A1-thm-4-2`).
