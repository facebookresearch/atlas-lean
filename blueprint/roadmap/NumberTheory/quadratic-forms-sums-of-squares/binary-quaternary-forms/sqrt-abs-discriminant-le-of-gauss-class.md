# Fowler's bound on imaginary quadratic order discriminants

Let $D<0$ be congruent to
$0$ or $1$ modulo $4$ and let $k$ be a positive integer. If the class number $h(D)$ of the
order of discriminant $D$ is at most $k$, then $\sqrt{|D|} \le 2k^2\exp(21000k^2)$.

The class number is counted by primitive positive-definite Gauss-reduced binary quadratic forms,
using the unique reduced representative of each proper class. In particular, $D$ need not be
fundamental and this is not the weighted Hurwitz class number.

## Informally uses

- [Every imaginary quadratic discriminant has a conductor decomposition](../../algebraic-number-theory/quadratic-fields/imaginary-quadratic-discriminants/exists-conductor-decomposition.md), to write $D = f^2 D_K$ with $D_K$ fundamental, so that $\sqrt{|D|} = f \sqrt{|D_K|}$
- [Class number formula for imaginary quadratic orders](class-number-formula-for-orders.md), relating $h(D)$ to $h(D_K)$
- [Totient lower bounds for class numbers of imaginary quadratic orders](fowler-s-discriminant-bound/gauss-class-number-mul-totient-le.md), for $h(D_K) \le k$ and $\varphi(f) \le k$ when $D_K \notin \{-3, -4\}$, and $\varphi(f) \le 3k$ otherwise
- [Fowler's lower bound for class numbers of fundamental discriminants](fowler-class-number-log-lower-bound.md), for $|D_K| \le e^{42000k^2}$ when $D_K \notin \{-3, -4\}$
- [Lower bound $\varphi(n) \ge \sqrt{n/2}$ for Euler's totient](../../arithmetic-functions/divisor-totient-functions/totient-ge-sqrt-half.md), for $f \le 2k^2$, or $f \le 18k^2$ when $D_K \in \{-3, -4\}$, where then $\sqrt{|D|} \le 36k^2$

## Sources

- Guy Fowler, *Some uniform effective results on André–Oort for sums of powers in* $\mathbb{C}^n$, Math. Proc. Cambridge Philos. Soc. 180 (2026), 607–641, [Proposition 2.7, p. 615](https://doi.org/10.1017/S0305004125101825).
