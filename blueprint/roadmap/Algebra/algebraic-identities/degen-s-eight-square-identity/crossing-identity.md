# Eight-square crossing identity

For all $x, y, u, v \in \{0, 1\}^3$, the structure constants of the eight-square table satisfy

$$\sum_{k \in \{0, 1\}^3} c(x, y, k)\, c(v, u, k) + \sum_{k \in \{0, 1\}^3} c(x, u, k)\, c(v, y, k)
= 2\, [x = v \text{ and } y = u],$$

where $[P]$ is $1$ if $P$ holds and $0$ otherwise.

This is the step behind Degen's eight-square identity. Expanding
$\sum_k \bigl(\sum_{p \oplus q = k} \varepsilon(p, q)\, a_p b_q\bigr)^2$ gives
$\sum_{x, y, v, u} \sum_k c(x, y, k)\, c(v, u, k)\, a_x b_y a_v b_u$; the terms for $(x, y, v, u)$
and $(x, u, v, y)$ carry the same monomial, so the identity turns the sum into
$\bigl(\sum_p a_p^2\bigr)\bigl(\sum_q b_q^2\bigr)$.
