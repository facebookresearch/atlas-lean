# Genus theory bound on the prime divisors of a fundamental discriminant

For every fundamental discriminant $D < 0$, the integer $2^{\omega(D) - 1}$ divides the Gauss class
number $h(D)$, where $\omega(D)$ is the number of distinct primes dividing $D$. In particular
$\omega(D) - 1 \le v_2(h(D))$, where $v_2(h(D))$ is the largest integer $k$ with $2^k \mid h(D)$.

The source deduces it from genus theory: the subgroup of elements of order dividing $2$ in the
class group $\mathrm{cl}(D)$, whose order is $h(D)$, has exactly $2^{\omega(D) - 1}$ elements.

## Expansion

A good expansion has pages for the form class group $C(D)$ of primitive positive definite forms of
discriminant $D$ under composition, a finite abelian group of order $h(D)$; for the step from the
reduced forms counted below to $C(D)[2]$, namely that they are exactly the reduced forms of the
classes of order dividing $2$, so that $|C(D)[2]| = 2^{\omega(D) - 1}$ when $D$ is fundamental (Cox,
Proposition 3.11 and Theorem 6.1); and for Lagrange's theorem in $C(D)$, which turns that count into
the divisibility. Each page states its result precisely, with its locator in Cox.

## Depends on

- [Gauss class number of a discriminant](kronecker-s-class-number-sums/gauss-class-number.md)
- [Fundamental imaginary quadratic discriminant](../../algebraic-number-theory/quadratic-fields/imaginary-quadratic-discriminants/is-fundamental-imaginary-quadratic-discr.md)

## Proof depends on

- [Number of primitive reduced forms with $b = 0$, $b = a$ or $a = c$](binary-quadratic-forms/ncard-ambiguous-reduced-forms.md), which counts $2^{\omega(D) - 1}$ such forms of discriminant $D$ for every fundamental $D < 0$, as then $|D| \not\equiv 12 \pmod{16}$ and $|D| \not\equiv 0 \pmod{32}$

## Sources

- Guy Fowler, *Some uniform effective results on André–Oort for sums of powers in* $\mathbb{C}^n$, Math. Proc. Cambridge Philos. Soc. 180 (2026), 607–641, [proof of Proposition 2.6, p. 615](https://doi.org/10.1017/S0305004125101825), citing David A. Cox, *Primes of the form* $x^2 + ny^2$*: Fermat, class field theory, and complex multiplication*, 3rd ed., AMS Chelsea Publishing, Providence, RI, 2022, Proposition 3.11 and Theorem 6.1.
- Joseph Oesterlé, *Nombres de classes des corps quadratiques imaginaires*, Séminaire Bourbaki, vol. 1983/84, exposé 631, Astérisque 121–122 (1985), 309–323, p. 310 (by genus theory, the number of primes dividing $|D|$ other than the largest is at most $v_2(h(D))$), [https://www.numdam.org/item/SB_1983-1984__26__309_0/](https://www.numdam.org/item/SB_1983-1984__26__309_0/).
