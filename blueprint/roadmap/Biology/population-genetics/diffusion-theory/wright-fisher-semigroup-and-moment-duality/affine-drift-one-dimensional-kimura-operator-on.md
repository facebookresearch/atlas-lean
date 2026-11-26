# Kimura operators with affine drift are twice the mutation generator

Let $b(x) = b_0 + b_1 x$ with $b(0) = b_0 \ge 0 \ge b(1) = b_0 + b_1$, and let $K_b f = x(1 - x) f'' + b f'$ act on real polynomials. Then

$$K_b x^n = n(n - 1 + b_0)\, x^{n-1} - n(n - 1 - b_1)\, x^n ,$$

so $K_b$ maps the polynomials of degree at most $n$ into themselves and is triangular in the monomial basis. With $\theta_1 = b(0)$ and $\theta_2 = -b(1)$,
both nonnegative exactly under the inward condition above, $K_b = 2L$ on polynomials, where $L$ is the [canonical generator](../wright-fisher-diffusion-with-selection-and-mutat/selection-mutation-generator.md) with zero selection,
$Lf = \frac12 x(1 - x) f'' + \frac12(\theta_1 - \theta x) f'$, $\theta = \theta_1 + \theta_2$. The degree-$n$ diagonal entry is $-n(n - 1 + \theta) = -2\lambda_n$, matching the [polynomial spectrum](../wright-fisher-diffusion-with-mutation/spectral-structure-of-l-0-theta-on-polynomials.md) of $L$; for
$b = 0$, $K_0 = 2L_0$. On each finite-dimensional space of polynomials of degree at most $n$, the matrix exponentials satisfy $e^{tK_b} = e^{2tL}$ for all $t\ge0$.

## Expansion

A proof page must establish the monomial identity, the invariance of each space of polynomials of degree at most $n$, the identity $K_b=2L$ there, and the resulting matrix-exponential identity. The statement is algebraic; relating $e^{tL}$ to the transition semigroup of the diffusion is a separate result.

## Depends on

- [Generator of the Wright–Fisher diffusion with selection and mutation](../wright-fisher-diffusion-with-selection-and-mutat/selection-mutation-generator.md)

## Proof depends on

- [Polynomial spectrum of the neutral Wright–Fisher generator with mutation](../wright-fisher-diffusion-with-mutation/spectral-structure-of-l-0-theta-on-polynomials.md)

## Sources

- R. C. Griffiths and D. Spanò, "Diffusion processes and coalescent trees", arXiv:1003.4650 (2010) (context only). The coefficient identity is computed above.
