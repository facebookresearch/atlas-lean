# Weighted form series

Let $g = (g_0, g_1, \dots, g_s)$ be Landen data, where $g_i$ has
rows $(a_i, b_i)$ and $(c_i, d_i)$ for $1 \le i \le s$, and let $w_1, \dots, w_s$ be real
numbers. The weighted form series of $g$ with weights $w$ is the formal power series
$u \sum_{i=1}^{s} w_i G_{g_i}(u) \in \mathbb{R}[[u]]$, where $u\,G_{g_i}(u)$ is the Landen form
series of $g_i$: the expansion of $\frac{c_i u}{a_i - c_i u} - \frac{d_i u}{b_i - d_i u}$, a
fraction with zero numerator and zero denominator being read as $0$.

## Sources

- Ken Kamano, *A Generalization of the Landen Connection Formula and Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2, definition of `Li_k(g; (β, γ); z)`.
