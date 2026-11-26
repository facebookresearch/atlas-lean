# Branching vectors and branching factors

A **branching vector** is a finite list $(a_1, \dots, a_b)$ of positive integers, describing a branching rule that replaces an instance of measure $n$ by subinstances of measures at most $n - a_1, \dots, n - a_b$. Its **characteristic sum** at $r > 0$ is $\chi(r) = \sum_{i=1}^{b} r^{-a_i}$, and a **branching factor** for it is any $r \ge 1$ with $\chi(r) \le 1$; the least such $r$ is the unique positive root of $\chi(r) = 1$ when $b \ge 2$. Examples: $(1,1)$ has factor $2$; $(1,2)$ has factor $(1 + \sqrt{5})/2$; $(1, 2, \dots, k)$ admits the factor $2 - 2^{-k}$.

## Sources

- F. V. Fomin and D. Kratsch, "Exact Exponential Algorithms", Springer, 2010.
- M. Cygan, F. V. Fomin, L. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk and S. Saurabh, "Parameterized Algorithms", Springer, 2015.
