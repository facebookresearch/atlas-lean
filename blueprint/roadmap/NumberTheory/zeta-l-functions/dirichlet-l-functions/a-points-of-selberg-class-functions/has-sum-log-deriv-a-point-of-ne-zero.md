# Lemma 6, case a ≠ 0 (expansion of the logarithmic derivative)

Let $F$ be a function in
the Selberg class with Dirichlet coefficients $a(n)$, let $k \ge 1$ and let $a \in \mathbb{C}$ with
$a \ne 0$. Then there is a real number $E$ such that for every $s \in \mathbb{C}$ with
$\operatorname{Re} s \ge E$,

$$
\frac{F^{(k+1)}(s)}{F^{(k)}(s) - a} = \sum_{l \ge 0} \sum_{n_0, \dots, n_l \ge 1}
\frac{(-1)^{k(l+1)}}{a^{l+1}} (\log n_0)^{k+1} (\log n_1 \cdots \log n_l)^k
\frac{a(n_0) \cdots a(n_l)}{n_0^s \cdots n_l^s},
$$

where $F^{(k)}$ is the $k$-th derivative of $F$ and the sum over all pairs of $l \ge 0$ and
positive integers $(n_0, \dots, n_l)$ converges unconditionally (equivalently, absolutely).

The paper sums over $n_i \ge \ell$, where $\ell \ge 2$ is least with $a(\ell) \ne 0$; the added
terms vanish because $\log 1 = 0$ and $a(n) = 0$ for $2 \le n < \ell$.

## Sources

- M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11, Lemma 6 (`integers-2024-A11-lem-6`).
