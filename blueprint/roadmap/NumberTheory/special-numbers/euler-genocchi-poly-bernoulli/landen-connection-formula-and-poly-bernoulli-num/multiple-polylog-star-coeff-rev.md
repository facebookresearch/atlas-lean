# Coefficient recursion for the non-strict multiple polylogarithm

For a finite list $\ell$
of natural numbers and $m \in \mathbb{N}$, the real number $c_\ell(m)$ is defined by recursion on
$\ell$: for the empty list, $c_\ell(m) = 1$ if $m = 0$ and $c_\ell(m) = 0$ otherwise; for a list
$\ell = (a, \ell')$ with first entry $a$ followed by the list $\ell'$,

$$c_{(a, \ell')}(m) = \frac{1}{m^a} \sum_{m' = 0}^{m} c_{\ell'}(m'),$$

where $0^0 = 1$ and $1/0 = 0$.

Applied to the reversed list $(k_r, \dots, k_1)$ of positive integers $k_1, \dots, k_r$ with
$r \ge 1$, it gives the coefficient of $z^m$ in
$\sum_{0 < m_1 \le \cdots \le m_r} z^{m_r} / (m_1^{k_1} \cdots m_r^{k_r})$.

## Sources

- Ken Kamano, *A Generalization of the Landen Connection Formula and Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 1, definition of `Li⋆_k(z)`.
