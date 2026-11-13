# Degree-weighted Möbius sum over the monic divisors of a polynomial over a finite field

Let
$F$ be a finite field with $q$ elements and let $\mu$ be the Möbius function of $F[T]$. For every
monic $f \in F[T]$,

$$\sum_{g \text{ monic},\ g \mid f} \frac{\mu(g) \deg g}{q^{\deg g}} =
\prod_{P \mid f} \left(1 - \frac{1}{q^{\deg P}}\right)
\sum_{P \mid f} \frac{\deg P}{1 - q^{\deg P}},$$

where in the product and in the sum $P$ runs over the monic irreducible divisors of $f$.

The product is $\Phi(f) / q^{\deg f}$, where $\Phi$ is Euler's totient function on $F[T]$.

## Sources

- Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Lemma 7; `Φ` as defined after Theorem 3.
