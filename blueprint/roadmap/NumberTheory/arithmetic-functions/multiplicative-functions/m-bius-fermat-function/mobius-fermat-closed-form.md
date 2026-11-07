# Closed form of the Möbius–Fermat function

Let $u_M$ be the Fermat unit function
and let $\mu_M$ be an integer-valued arithmetic function with $\mu_M * u_M = \varepsilon$, where
$*$ is Dirichlet convolution and $\varepsilon$ is its identity, with $\varepsilon(1) = 1$ and
$\varepsilon(l) = 0$ for $l \ne 1$; thus $\mu_M$ is the Dirichlet inverse of $u_M$, the
Möbius–Fermat function.
Let $m_1, m_2 \ge 0$ be integers, let $n_3, \dots, n_k$ be finitely many (possibly no) distinct
integers with $n_j \ge 4$ and $n_j \ne 6$, let $m_3, \dots, m_k \ge 1$ be integers, and put
$l = 3^{m_1} 7^{m_2} \prod_{j=3}^{k} (2^{n_j} - 1)^{m_j}$ and
$r = m_1 + m_2 + m_3 + \dots + m_k$. Then, as rational numbers,

$$\mu_M(l) = (-1)^r \sum_{j=0}^{\min(\lfloor m_1/2 \rfloor, m_2)}
\frac{(r - 2j)!}{(m_1 - 2j)! \, (m_2 - j)! \, j! \, m_3! \cdots m_k!}.$$

## Sources

- J. L. Varona, *The Möbius and the von Mangoldt-type Functions of the Fermat Zeta Function*, INTEGERS 26 (2026), Article A106, Theorem 9.
