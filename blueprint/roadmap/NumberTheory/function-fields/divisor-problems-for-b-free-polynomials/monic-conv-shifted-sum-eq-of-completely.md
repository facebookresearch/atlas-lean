# Shifted partial sums for completely multiplicative functions

Let $F$ be a finite field
and let $\alpha, \beta \colon F[T] \to \mathbb{C}$ be completely multiplicative, that is, monoid
homomorphisms from the multiplicative monoid of $F[T]$ to $\mathbb{C}$. Write $\mu$ for the Möbius
function of $F[T]$. For $f \in F[T]$, a natural number $n$ and an integer $k$, write
$S_f[\alpha, \beta](n)$ and $D[\alpha, \beta](k)$ for the shifted partial sums and the partial
sums of the Dirichlet convolution of $\alpha$ and $\beta$ over monic divisors, where
$D[\alpha, \beta](k) = 0$ for $k < 0$. Then for every monic $f \in F[T]$ and every natural number
$n$,

$$S_f[\alpha, \beta](n) = \sum_{d \mid f} \alpha(d)\, \beta(f/d) \sum_{\ell \mid d} \mu(\ell)\,
\beta(\ell)\, D[\alpha, \beta](n - \deg(f \ell)),$$

where $d$ runs over the monic divisors of $f$, $\ell$ over the monic divisors of $d$, and
$n - \deg(f \ell)$ is computed in the integers.

The paper states this for every $f \in F[T]$, monic or not; its proof applies Lemma 2, which needs
$f$ monic.

## Sources

- Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Lemma 3 (`integers-2026-A80-lem-3`).
