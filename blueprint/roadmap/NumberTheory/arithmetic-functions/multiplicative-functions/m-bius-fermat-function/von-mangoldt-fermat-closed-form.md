# Closed form of the von Mangoldt–Fermat function

Let $u_M$ be the Fermat unit function
and let $\mu_M$ be an integer-valued arithmetic function with $\mu_M * u_M = \varepsilon$, where
$*$ is Dirichlet convolution and $\varepsilon$ is its identity, with $\varepsilon(1) = 1$ and
$\varepsilon(l) = 0$ for $l \ne 1$; thus $\mu_M$ is the Dirichlet inverse of $u_M$, the
Möbius–Fermat function.
Let $\Lambda_M = \mu_M * u_M'$, computed with real values, where
$u_M'(l) = u_M(l) \log l$.
Let $m_1, m_2 \ge 0$ be integers, let $n_3, \dots, n_k$ be finitely many (possibly no) distinct
integers with $n_j \ge 4$ and $n_j \ne 6$, let $m_3, \dots, m_k \ge 1$ be integers, and put
$l = 3^{m_1} 7^{m_2} \prod_{j=3}^{k} (2^{n_j} - 1)^{m_j}$ and
$r = m_1 + m_2 + m_3 + \dots + m_k$. Then

$$\Lambda_M(l) = (-1)^{r-1} \Big(\sum_{j=0}^{\min(\lfloor m_1/2 \rfloor, m_2)}
\frac{(r - 2j - 1)!}{(m_1 - 2j)! \, (m_2 - j)! \, j! \, m_3! \cdots m_k!}\Big) \log l.$$

When $r = 0$, that is $l = 1$, both sides are $0$: on the right, $r - 1$ and $r - 2j - 1$ are
read as $0$ and $\log 1 = 0$.

## Sources

- J. L. Varona, *The Möbius and the von Mangoldt-type Functions of the Fermat Zeta Function*, INTEGERS 26 (2026), Article A106, Theorem 10.
