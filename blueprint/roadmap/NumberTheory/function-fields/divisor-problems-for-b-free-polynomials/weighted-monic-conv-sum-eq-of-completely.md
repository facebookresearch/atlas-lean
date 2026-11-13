# Camargo's identity over $F(T)$

Let $F$ be a finite field and let $\mu$ be the Möbius
function of $F[T]$. For functions $\alpha, \beta \colon F[T] \to \mathbb{C}$ let
$(\alpha * \beta)(f) = \sum_{g \mid f} \alpha(g) \beta(f/g)$, over monic divisors $g$, be their
Dirichlet convolution, and let $D[\alpha, \beta](k)$ be the sum of $(\alpha * \beta)(g)$ over the
monic $g$ of degree at most $k$, which is $0$ for $k < 0$. For a further function $\gamma$ let
$D[\gamma, \alpha, \beta](n)$ be the sum of $\gamma(f) (\alpha * \beta)(f)$ over the monic $f$ of
degree at most $n$. Suppose $\alpha$ and $\beta$ are completely multiplicative, that is,
$\alpha(1) = 1$ and $\alpha(f g) = \alpha(f) \alpha(g)$ for all $f, g \in F[T]$, and likewise for
$\beta$, and let $\gamma \colon F[T] \to \mathbb{C}$ be arbitrary. Then for every natural number
$n$,

$$D[\gamma, \alpha, \beta](n) = \sum_{f \text{ monic},\ \deg f \le n} (\gamma * \mu)(f)
\sum_{d \mid f} \alpha(d) \beta(f/d) \sum_{\ell \mid d} \mu(\ell) \beta(\ell) \,
D[\alpha, \beta](n - \deg(f \ell)),$$

where $d$ runs over the monic divisors of $f$ and $\ell$ over the monic divisors of $d$.

## Sources

- Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Theorem 6.
