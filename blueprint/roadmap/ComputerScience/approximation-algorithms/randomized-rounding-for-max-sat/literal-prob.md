# Probability that a literal is true

Let $p_i \in \mathbb{R}$ for every variable index $i$. The value at $p$ of the literal $x_i$ is $p_i$,
and that of the literal $\bar x_i$ is $1 - p_i$. When $0 \le p_i \le 1$ and variable $x_i$ is true with
probability $p_i$, this is the probability that the literal is true. Evaluated at an LP solution $y$, the
same expression is the literal's term in the [clause bound](lp-clause-bound.md), the left-hand side
of the clause constraint of (LP).

## Sources

- M. X. Goemans and D. P. Williamson, "New 3/4-approximation algorithms for the maximum satisfiability problem", *SIAM J. Discrete Math.* 7(4) (1994), 656–666 (journal version), §2–3.
