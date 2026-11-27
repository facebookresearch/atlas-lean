# Bernstein coefficients of a real polynomial

For a natural number $n$, a real polynomial $p(s) = \sum_k p_k s^k$ and a natural number $j$, the degree-$n$ Bernstein coefficient of $p$ at $j$ is

$$c_j = \sum_{k=0}^{n} p_k \frac{\binom{j}{k}}{\binom{n}{k}},$$

with $\binom{j}{k} = 0$ for $j < k$. Only the coefficients $p_0, \dots, p_n$ enter, so the coefficients $c_0, \dots, c_n$ recover $p$ in the Bernstein basis of degree $n$ only when $p$ has degree at most $n$.
