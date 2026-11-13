# Möbius sum over the monic divisors of a polynomial over a finite field

Let $F$ be a finite
field with $q$ elements and let $\mu$ be the Möbius function of $F[T]$. For every monic
$f \in F[T]$,

$$\sum_{g \text{ monic},\ g \mid f} \frac{\mu(g)}{q^{\deg g}} =
\prod_{P \text{ monic irreducible},\ P \mid f} \left(1 - \frac{1}{q^{\deg P}}\right).$$

The right side is $\Phi(f) / q^{\deg f}$, where $\Phi$ is Euler's totient function on $F[T]$.

## Sources

- Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Lemma 6; `Φ` as defined after Theorem 3.
