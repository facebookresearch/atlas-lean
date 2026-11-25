# Polynomial spectrum of the neutral Wright–Fisher generator with mutation

Let $\theta_1,\theta_2\ge0$, $\theta=\theta_1+\theta_2$, and
$L f=\frac12x(1-x)f''+\frac12(\theta_1-\theta x)f'$, the
[canonical generator](../wright-fisher-diffusion-with-selection-and-mutat/selection-mutation-generator.md)
with zero selection. The space of polynomials of degree at most $N$
is invariant. In its monomial basis,

$$Lx^n=\tfrac12 n(n-1+\theta_1)x^{n-1}-\lambda_nx^n,
\qquad\lambda_n=\tfrac12 n(n-1+\theta),$$

with $L1=0$. Thus the eigenvalues, counted with multiplicity, are
$-\lambda_0,\ldots,-\lambda_N$.
If $\theta>0$, they are distinct and there is a unique monic
eigenpolynomial of each degree, including when exactly one mutation
parameter is zero. If both parameters are positive, scalar multiples
are the [orthonormal Jacobi polynomials](../transition-densities-of-wright-fisher-diffusions/jacobi-and-gegenbauer-polynomials-on-0-1.md)
$R_n^{(\theta_1,\theta_2)}$.
The monic degree-one eigenfunction is $x-\theta_1/\theta$.

If $\theta=0$, the zero eigenspace is spanned by $1,x$ (intersected
with the given degree bound). For $n\ge2$, an eigenfunction of degree
$n$ is $x(1-x)C_{n-2}^{(3/2)}(1-2x)$, with eigenvalue $-n(n-1)/2$.
Together these give an eigenbasis of each finite polynomial space.
This is a finite-dimensional polynomial assertion, not a claim about
the spectrum or domain of an unbounded operator on every function space.

## Depends on

- [Orthonormal shifted Jacobi polynomials](../transition-densities-of-wright-fisher-diffusions/jacobi-and-gegenbauer-polynomials-on-0-1.md)
- [Selection-mutation generator](../wright-fisher-diffusion-with-selection-and-mutat/selection-mutation-generator.md)

## Expansion

The monomial calculation gives triangularity.
For $\theta>0$, $\lambda_n-\lambda_{n-1}=n-1+\theta/2>0$.
For a monic degree-$n$ eigenpolynomial $\sum_{j=0}^nc_jx^j$, set
$c_n=1$ and determine
$c_j=-(j+1)(j+\theta_1)c_{j+1}/(2(\lambda_n-\lambda_j))$
for $j<n$. This proves existence and uniqueness even at a one-sided
mutation boundary, without using a singular Jacobi parameter.
For zero mutation, write $g=x(1-x)$ and calculate
$L(gP)=\frac12g(gP''+2(1-2x)P'-2P)$.
The Jacobi ODE with parameters $2,2$ proves the stated Gegenbauer formula.
In particular $L[x(1-x)]=-x(1-x)$.

## Sources

- R. C. Griffiths and D. Spanò, *Diffusion processes and coalescent trees* (2010), <https://arxiv.org/abs/1003.4650>, Section 1, (1.4) and (1.7). The parameter convention here is fixed by the explicit drift and checked directly on monomials; the triangular boundary cases are derived above.
