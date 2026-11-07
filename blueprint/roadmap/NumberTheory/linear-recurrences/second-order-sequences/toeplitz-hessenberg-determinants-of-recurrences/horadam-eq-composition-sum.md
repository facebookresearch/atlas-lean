# Horadam sequences as composition sums

Let $p, q, r, s$ be complex numbers with
$(q - r)^2 = 4s(p - 1)$ and $4s(p - 1) \ne 0$, and let $(v_k)_{k \ge 0}$ be the complex sequence
with $v_0 = p$, $v_1 = q$ and $v_{k+2} = r v_{k+1} + s v_k$ for every $k \ge 0$. Put
$e = 2ps/(r - q)$. Then for every $n \ge 1$,

$$v_n = \sum_c \bigl((r - q)/2\bigr)^{n - \ell(c)} \prod_{j \in c} \bigl((q + e) j - e\bigr),$$

where $c$ runs over the compositions of $n$ (ordered tuples of positive integers with sum $n$),
$\ell(c)$ is the number of parts of $c$ and the product runs over the parts $j$ of $c$.

In the source this is identity (12), a sum over $\alpha$ with
$\alpha_1 + 2\alpha_2 + \dots + n\alpha_n = n$ weighted by multinomial coefficients, which is the
same number.

## Sources

- Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Theorem 1 (`integers-2025-A97-thm-1`).
