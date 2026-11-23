# Generating function of the squared Lucas triangular numbers

Let $(s, t)$ be nondegenerate
Lucas parameters, with Lucas brackets $\{n\}_{s,t}$ and Lucasnomial coefficients
$\binom{n}{k}_{s,t}$, and let $\varphi$ and $\varphi'$ be real numbers with
$\varphi + \varphi' = s$ and $\varphi \varphi' = -t$. Then, as formal power series in $x$ with
real coefficients,

$$\Big(\sum_{n \ge 1} \binom{n+1}{2}_{s,t}^{2} x^n\Big) (1 - t^2 x) (1 - \varphi'^4 x)
\prod_{k=0}^{3} (1 - \varphi^{4-k} \varphi'^k x) = x + (\{4\}_{s,t} \varphi - \varphi^4) x^2 -
\{3\}_{s,t} \varphi^3 \varphi'^3 x^3 +
(\{3\}_{s,t} \varphi^7 \varphi'^3 - \{4\}_{s,t} \varphi^6 \varphi'^3) x^4.$$

This is the paper's quotient formula for $\sum_{n \ge 1} \binom{n+1}{2}_{s,t}^{2} x^n$ with the
denominator cleared; the paper writes the product over $k$ as $(\varphi^4 x; q)_4$ with
$q = \varphi' / \varphi$.

## Sources

- Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*, Journal of Integer Sequences 28 (2025), Article 25.5.6, Theorem 10 (`jis-2025-25.5.6-thm-10`).
