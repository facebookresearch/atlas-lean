# Totient lower bounds for class numbers of imaginary quadratic orders

Let $D < 0$ be a fundamental discriminant, let $f \ge 1$ be an integer and let $\varphi$ be Euler's
totient function. If $D \notin \{-3, -4\}$, then the Gauss class numbers satisfy

$$h(D)\, \varphi(f) \le h(f^2 D).$$

If $D \in \{-3, -4\}$, then $\varphi(f) \le 3\, h(f^2 D)$.

## Depends on

- [Gauss class number of a discriminant](kronecker-s-class-number-sums/gauss-class-number.md)
- [Fundamental imaginary quadratic discriminant](../../algebraic-number-theory/quadratic-fields/imaginary-quadratic-discriminants/is-fundamental-imaginary-quadratic-discr.md)
- [Euler's totient function](../../arithmetic-functions/divisor-totient-functions/euler-totient.md)

## Proof depends on

- [Class number formula for imaginary quadratic orders](class-number-formula-for-orders.md), since each Kronecker symbol is at most $1$, so that $f \prod_{p \mid f} (1 - (D/p)/p) \ge f \prod_{p \mid f} (1 - 1/p) = \varphi(f)$, and $e \le 3$, with $e = 1$ when $D \notin \{-3, -4\}$
- [Class numbers of the discriminants $-3$, $-4$ and $-12$](kronecker-s-class-number-sums/gauss-class-number-small.md), for $h(-3) = h(-4) = 1$

## Sources

- Guy Fowler, *Some uniform effective results on André–Oort for sums of powers in* $\mathbb{C}^n$, Math. Proc. Cambridge Philos. Soc. 180 (2026), 607–641, [proof of Proposition 2.7, p. 615–616](https://doi.org/10.1017/S0305004125101825).
