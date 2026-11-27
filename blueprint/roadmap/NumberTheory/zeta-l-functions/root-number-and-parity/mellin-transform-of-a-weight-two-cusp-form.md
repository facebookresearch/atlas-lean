# Mellin transform of a weight-two cusp form

Let $N \ge 1$ and let $f \in S_2(\Gamma_0(N))$ be a [cusp form](../../modular-forms-q-series/modular-forms/cusp-form.md)
of weight $2$ for [$\Gamma_0(N)$](../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma0.md), with
$q$-expansion $f(z) = \sum_{n \ge 1} a_n e^{2\pi i n z}$, and let $L(f, s) = \sum_{n \ge 1} a_n n^{-s}$. Then for every
$s \in \mathbb{C}$ with $\operatorname{Re}(s) > 0$ and $\sum_{n \ge 1} \lvert a_n \rvert n^{-\operatorname{Re}(s)} < \infty$, the integral
$\int_0^\infty f(it) t^{s-1} \, dt$ converges absolutely and

$$\Lambda(f, s) := (2\pi)^{-s} \Gamma(s) N^{s/2} L(f, s) = N^{s/2} \int_0^\infty f(it) \, t^{s-1} \, dt.$$

Proof outline (worked out here): $\int_0^\infty e^{-2\pi n t} t^{s-1} \, dt = (2\pi n)^{-s} \Gamma(s)$ for
$\operatorname{Re}(s) > 0$, and the absolute convergence of $\sum_n \lvert a_n \rvert (2\pi n)^{-\operatorname{Re}(s)} \Gamma(\operatorname{Re}(s))$
allows the sum and the integral to be exchanged.

## Depends on

- [Cusp form](../../modular-forms-q-series/modular-forms/cusp-form.md), for $S_2(\Gamma_0(N))$
- [Congruence subgroup $\Gamma_0(N)$](../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma0.md)

## Sources

- H. Darmon, *Rational points on modular elliptic curves*, CBMS Regional Conference Series in Mathematics 101,
  American Mathematical Society, 2004; author's version,
  <https://www.math.mcgill.ca/darmon/pub/Articles/Research/36.NSF-CBMS/chapter.pdf>, cited by the page numbers
  printed in that version: (2.11), p. 17 ("A direct calculation (cf. Exercise 8) shows that
  $\Lambda(f, s) := (2\pi)^{-s}\Gamma(s)N^{s/2}L(f, s) = N^{s/2}\int_0^\infty f(it)t^{s-1}dt$"), stated there for a newform
  without a domain of validity, and Exercise 8 of Chapter 2, p. 24 ("Check formula (2.11) in the text.").
