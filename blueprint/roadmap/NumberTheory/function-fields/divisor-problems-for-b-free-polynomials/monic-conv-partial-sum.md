# Partial sums of a Dirichlet convolution over monic polynomials

Let $F$ be a field, let
$\alpha, \beta \colon F[T] \to \mathbb{C}$, and let $\alpha * \beta$ be their Dirichlet
convolution over monic divisors. For an integer $n$,
$D[\alpha, \beta](n) = \sum_g (\alpha * \beta)(g)$, the sum over the monic $g \in F[T]$ of degree
at most $n$. For $n < 0$ the sum is empty, so $D[\alpha, \beta](n) = 0$; this is how the paper's
Lemma 3 uses $D$ at $n - \deg(f \ell)$.

The sum is a finitary sum: it is $0$ when infinitely many of its terms are nonzero, which can
happen only for infinite $F$.

## Sources

- Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of `D[α, β](n)`.
