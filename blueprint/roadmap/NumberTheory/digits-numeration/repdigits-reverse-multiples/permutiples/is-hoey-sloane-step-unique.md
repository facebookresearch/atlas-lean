# Uniqueness of Hoey-Sloane transitions

Let $n \le b$. If an input $e$ moves state $c_1$
to state $c_2$ and also moves state $\hat c_1$ to state $\hat c_2$, each in one transition of the
$(n, b)$-Hoey-Sloane machine, then $c_1 = \hat c_1$ and $c_2 = \hat c_2$.

The paper assumes $1 < n < b$; here it is weakened to $n \le b$. For $n > b$ the claim can fail:
for $n = 3$ and $b = 1$ the input $(0, 0)$ moves $0$ to $0$ and also $1$ to $1$.

## Sources

- Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*, INTEGERS 25 (2025), Article A111, Theorem 5 (`integers-2025-A111-thm-5`).
