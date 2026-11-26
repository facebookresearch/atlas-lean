# Interpolation error at the Chebyshev points

Let $f$ have $n + 1$ continuous derivatives on $[-1, 1]$, and let $Q_n$ be the polynomial of degree at most $n$ that interpolates $f$ at the $n + 1$ zeros of the Chebyshev polynomial $T_{n+1}$,

$$x_j = \cos\Bigl(\frac{2j + 1}{2n + 2}\, \pi\Bigr), \qquad 0 \le j \le n.$$

Then for every $x \in [-1, 1]$,

$$|f(x) - Q_n(x)| \le \frac{1}{2^n (n+1)!} \max_{|\xi| \le 1} |f^{(n+1)}(\xi)|.$$

Here $\prod_j (x - x_j) = 2^{-n} T_{n+1}(x)$ is the monic Chebyshev polynomial, whose maximum modulus on $[-1, 1]$ is $2^{-n}$, the smallest possible for a monic polynomial of degree $n + 1$; so these nodes minimize the factor $\max_{[-1,1]} |\prod_j (x - x_j)|$ of the error formula.

## Depends on

- [Lagrange interpolant](../../approximation-theory/lagrange-interpolation/eval-interpolant.md)

## Proof depends on

- [Error of polynomial interpolation](interpolation-error-formula.md)
- [Bound for the monic Chebyshev polynomial on the interval](../../approximation-theory/minimax-property-of-the-chebyshev-polynomials/abs-eval-chebyshev-monic-le.md)

## Informally uses

- [Minimax property of the Chebyshev polynomials](../../approximation-theory/minimax-property-of-the-chebyshev-polynomials/inv-two-pow-le-of-forall-abs-eval-le.md)

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 3.8, Theorem 3.12 and Theorem 3.13 with (3.38). <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
