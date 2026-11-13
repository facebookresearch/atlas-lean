# The zeroth moment of the trace distance is one

Let $p \ge 1$ and $N$ be natural numbers,
and let $K$ be a field generated over $\mathbb{Q}$ by a primitive $p$-th root of unity, with fixed
primitive $p$-th root of unity $\omega \in K$. Let $d$ be the trace metric on $K$, given by
$d(\alpha, \beta) \ge 0$ and
$d(\alpha, \beta)^2 = \sum_{j=1}^{p-1} \mathrm{Tr}_{K/\mathbb{Q}}((\alpha - \beta) \omega^j)^2$.
Let $B(p, N)$ be the set of integer vectors $a = (a_1, \dots, a_{p-1})$ with $-N \le a_i \le N$
for all $i$, write $\alpha_a = a_1 \omega + \dots + a_{p-1} \omega^{p-1}$, and let
$M_k(p, N) = \lvert B(p, N) \rvert^{-2} \sum_{a, b \in B(p, N)} d(\alpha_a, \alpha_b)^k$ be the
$k$-th moment of $d$ over $B(p, N)$. Then $M_0(p, N) = 1$, with the convention $0^0 = 1$ for
coinciding points.

## Sources

- Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*, INTEGERS 25 (2025), Article A10, Section 6 (Definition 6.1 of arXiv:2410.22687).
