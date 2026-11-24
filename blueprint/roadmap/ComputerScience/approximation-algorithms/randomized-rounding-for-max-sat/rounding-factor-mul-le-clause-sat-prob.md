# Goemans–Williamson Lemma 3.1

Let $C$ be a clause with $k$ literals on distinct variables, let $0 \le y_i \le 1$ on its variables and
$0 \le z \le \min\left(1, \sum_{i \in P} y_i + \sum_{i \in N}(1 - y_i)\right)$. Then randomized
rounding, which sets $x_i$ true independently with probability $y_i$, satisfies $C$ with
[probability](clause-sat-prob.md) at least $\beta_k z$, where $\beta_k$ is the
[randomized-rounding factor](rounding-factor.md). The proof is the paper's: the arithmetic–geometric mean inequality applied to the
factors $1 - \Pr[\ell \text{ true}]$ gives $1 - (1 - z/k)^k$, and convexity of $t \mapsto t^k$
gives $1 - (1 - z/k)^k \ge \beta_k z$ on $[0, 1]$. The paper's reduction to unnegated variables
is not needed: negated literals enter through $1 - y_i$ directly.

## Sources

- M. X. Goemans and D. P. Williamson, "New 3/4-approximation algorithms for the maximum satisfiability problem", *SIAM J. Discrete Math.* 7(4) (1994), 656–666 (journal version), Lemma 3.1.
