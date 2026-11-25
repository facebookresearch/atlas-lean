# Convergence and PDEs of the neutral Gegenbauer series

Set $g(x)=x(1-x)$, $\lambda_i=i(i+1)/2$ and
$\varphi_i(x)=g(x)C_{i-1}^{(3/2)}(1-2x)$ for $i\ge1$.
The [polynomial eigenfunction identity](../wright-fisher-diffusion-with-mutation/spectral-structure-of-l-0-theta-on-polynomials.md)
is $L_0\varphi_i=-\lambda_i\varphi_i$ for $L_0f=gf''/2$.
The functions are orthogonal in $L^2(dx/g(x))$, with squared norms
$h_i=i(i+1)/(4(2i+1))$.
Define the analytic series, for $t>0$ and $x,y\in[0,1]$,

$$p_t(x,y)=\sum_{i\ge1}\frac{4(2i+1)}{i(i+1)}\,
 g(x)C_{i-1}^{(3/2)}(1-2x)C_{i-1}^{(3/2)}(1-2y)e^{-\lambda_i t}.$$

For every $t_0>0$ and every fixed finite derivative order in $x,y,t$,
the differentiated series converges uniformly on
$[t_0,\infty)\times[0,1]^2$. Consequently it satisfies the backward
PDE $\partial_t p=\frac12g(x)\partial_x^2p$ and the forward PDE
$\partial_t p=\frac12\partial_y^2(g(y)p)$ on the interior.
As $t\to\infty$,
$p_t(x,y)=g(x)(6e^{-t}+O(e^{-3t}))$, with the error bound uniform in
$x,y\in[0,1]$.
These are analytic claims. Identification as the killed diffusion's
Lebesgue transition density is a separate residual claim.

## Depends on

- [Polynomial spectrum of the Wright–Fisher generator](../wright-fisher-diffusion-with-mutation/spectral-structure-of-l-0-theta-on-polynomials.md)

## Proof depends on

- [Canonical Jacobi normalization and Gegenbauer norms](../transition-densities-of-wright-fisher-diffusions/jacobi-and-gegenbauer-polynomials-on-0-1.md)

## Expansion

The norm follows from the $a=b=2$ identity on the linked page.
The coefficient is $h_i^{-1}$: a series expressed relative to the
measure $dy/g(y)$ contains $\varphi_i(x)\varphi_i(y)$; converting to
Lebesgue measure cancels the factor $g(y)$.

For $z\in[-1,1]$ the sharp bound
$|C_n^{(3/2)}(z)|\le(n+1)(n+2)/2$ follows from the normalized integral
representation
$C_n^{(3/2)}(z)/C_n^{(3/2)}(1)
=(2/\pi)\int_0^\pi(z+\mathrm i\sqrt{1-z^2}\cos u)^n\sin^2u\,du$.
Expanding the power and evaluating the even beta moments verifies this
polynomial identity; the integrand's complex base has modulus at most one.
For a direct all-derivative bound, the three-term recurrence bounds the
sum of absolute coefficients of $C_n^{(3/2)}$ by $4^n$.
A fixed $r$-th derivative on $[-1,1]$ is therefore bounded by $n^r4^n$;
composition with $1-2x$ adds $2^r$.
Every differentiated summand is bounded by a fixed polynomial in $i$
times $16^i e^{-i(i+1)t_0/2}$, a summable sequence.
This justifies each differentiation. The eigenfunction ODE gives both
PDEs term by term. The first term is $6g(x)e^{-t}$, and the remaining
terms start at $\lambda_2=3$, giving the uniform weighted remainder.

A separate identification theorem must establish the initial condition,
positivity and the appropriate killed-semigroup uniqueness or a duality
argument. Solving the PDEs for positive time alone does not prove that
$p_t$ is a probability transition density. No such result is credited here.

## Sources

- M. Kimura, *Solution of a process of random genetic drift with a continuous model* (1955), <https://doi.org/10.1073/pnas.41.3.144>, bibliographic attribution only. Coefficients, convergence and PDEs are derived above from the canonical Gegenbauer polynomials.
