# Class number formula for imaginary quadratic orders

Let $D < 0$ be a fundamental discriminant and let $f \ge 1$ be an integer. Then

$$h(f^2 D) = \frac{h(D)\, f}{e} \prod_{p \mid f} \left(1 - \left(\frac{D}{p}\right) \frac{1}{p}\right),$$

where $h$ is the Gauss class number, the product runs over the primes $p$ dividing $f$,
$\left(\frac{D}{p}\right)$ is the Kronecker symbol, and $e = 1$ if $f = 1$ or $D < -4$, $e = 2$ if
$D = -4$ and $f \ge 2$, and $e = 3$ if $D = -3$ and $f \ge 2$.

Here $e$ is the index $[\mathcal{O}_K^\times : \mathcal{O}^\times]$ of the unit group of the order
$\mathcal{O}$ of conductor $f$ in that of the ring of integers $\mathcal{O}_K$ of
$K = \mathbb{Q}(\sqrt{D})$: the units of $\mathcal{O}$ are $\pm 1$ when $f \ge 2$, and
$\mathcal{O}_K^\times$ has $6$, $4$ or $2$ elements as $D = -3$, $D = -4$ or $D < -4$. The Gauss class
number $h(f^2 D)$ counts one reduced form in each proper equivalence class of primitive positive
definite forms of discriminant $f^2 D$, and these classes correspond to the proper ideal classes of
$\mathcal{O}$, so $h(f^2 D)$ is the class number of $\mathcal{O}$, as in the source.

## Expansion

A good expansion has pages for the unit index $[\mathcal{O}_K^\times : \mathcal{O}^\times]$ and for
the steps of Cox's proof of Theorem 7.24, which compares the class groups of $\mathcal{O}$ and
$\mathcal{O}_K$ through $(\mathcal{O}_K / f\mathcal{O}_K)^\times$ and $(\mathbb{Z}/f\mathbb{Z})^\times$.
Each page states its result precisely, with its locator in Cox.

## Depends on

- [Gauss class number of a discriminant](kronecker-s-class-number-sums/gauss-class-number.md)
- [Fundamental imaginary quadratic discriminant](../../algebraic-number-theory/quadratic-fields/imaginary-quadratic-discriminants/is-fundamental-imaginary-quadratic-discr.md)
- [Kronecker symbol](../../congruences/power-residues-reciprocity/kronecker-symbol-and-quadratic-characters/kronecker-sym.md)

## Proof depends on

- [Form classes and proper ideal classes of an imaginary quadratic order](form-classes-and-proper-ideal-classes/form-classes-equiv-proper-ideal-classes.md), for $h(f^2 D) = h(\mathcal{O})$ and $h(D) = h(\mathcal{O}_K)$ (Cox, Theorem 7.7)

## Sources

- David A. Cox, *Primes of the form* $x^2 + ny^2$*: Fermat, class field theory, and complex multiplication*, 3rd ed., AMS Chelsea Publishing, Providence, RI, 2022, Theorem 7.24.
- Guy Fowler, *Some uniform effective results on André–Oort for sums of powers in* $\mathbb{C}^n$, Math. Proc. Cambridge Philos. Soc. 180 (2026), 607–641, [proof of Proposition 2.7, p. 615–616](https://doi.org/10.1017/S0305004125101825), which applies it in this form.
