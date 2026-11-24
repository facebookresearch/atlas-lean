# Generating functions for run-and-repeat Nicomachean sequences

For integers $j, m \ge 1$
let $\sigma(j, m)$ be the integer sequence $(1, 2, \ldots, j + 1, m, \ldots, m)$ in which $m$ is
repeated $2j$ times, and let $\nu$ denote the Nicomachean defect. Call $j \ge 1$ admissible if
$\nu(\sigma(j, m)) = 0$ for some integer $m \ge 1$, let $j_k$ be the $k$-th smallest admissible
integer (counting from $k = 0$), and let $m_k = j_k + \lfloor \sqrt{2j_k^2 + 3j_k + 2} \rfloor$.
Then $\nu(\sigma(j_k, m_k)) = 0$ for every $k$, and in the ring of formal power series over
$\mathbb{Z}$

$$
(X - 1)(1 - 6X + X^2)(1 + 6X + X^2) \sum_{k \ge 0} j_k X^k = X^4 + X^3 - 19X^2 - 5X - 2
$$

and

$$
(1 - X)(1 - 6X + X^2)(1 + 6X + X^2) \sum_{k \ge 0} m_k X^k = 6(1 + X)^2.
$$

For admissible $j$ the square root is an integer and $m = j + \sqrt{2j^2 + 3j + 2}$ is the
positive root of $\nu(\sigma(j, m)) = 0$ in $m$, so these say that $(j_k)$ and $(m_k)$ have the
generating functions $(x^4 + x^3 - 19x^2 - 5x - 2)/((x - 1)(1 - 6x + x^2)(1 + 6x + x^2))$ and
$6(1 + x)^2/((1 - x)(1 - 6x + x^2)(1 + 6x + x^2))$.

## Sources

- Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Proposition 5 (`jis-2024-24.6.3-prop-5`).
