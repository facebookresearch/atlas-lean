# Monic irreducible polynomials of prime degree over Z/pZ

Let $p$ and $k$ be primes and let $N$ be the number of monic irreducible polynomials of degree $k$
over $\mathbb{Z}/p\mathbb{Z}$. Then

$$N k = p^k - p.$$

The proof is Rabin's: in the field $\mathrm{GF}(p^k)$, every element outside $\mathbb{Z}/p\mathbb{Z}$
has a minimal polynomial whose degree divides $k$ and is not $1$, hence is $k$. Every monic
irreducible $f$ of degree $k$ has a root in $\mathrm{GF}(p^k)$, because
$(\mathbb{Z}/p\mathbb{Z})[X]/(f)$ is a field with $p^k$ elements and therefore isomorphic to
$\mathrm{GF}(p^k)$; its $k$ roots there are distinct (finite fields are perfect) and all have
minimal polynomial $f$. So the $p^k - p$ elements outside $\mathbb{Z}/p\mathbb{Z}$ fall into $N$ root
sets of size $k$.

Rabin states and proves the case $p = 2$; the statement here holds for every prime $p$. For
composite $k$ the count is given by Gauss's formula with the Möbius function.

## Sources

- M. O. Rabin, *Fingerprinting by random polynomials*, Technical Report TR-15-81, Center for Research in Computing Technology, Harvard University, 1981, Section 2, Lemma 1 and its proof.
