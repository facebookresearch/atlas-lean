# Spatial and time integrals of the neutral spectral series

For the [analytic series](kimura-1955-eigen-series-convergence-and-pde-for.md)
$p_t$ and $g(x)=x(1-x)$, define $S_t(x)=\int_0^1p_t(x,y)\,dy$.
For $t>0$ and $x\in[0,1]$,

$$S_t(x)=\sum_{\substack{i\ge1\\i\text{ odd}}}
 \frac{4(2i+1)}{i(i+1)}g(x)C_{i-1}^{(3/2)}(1-2x)e^{-i(i+1)t/2}.$$

Uniformly in $x$, $S_t(x)=g(x)(6e^{-t}+O(e^{-6t}))$ as $t\to\infty$.
Furthermore the improper time integral is absolutely convergent and

$$\int_0^\infty S_t(x)\,dt
 =\sum_{\substack{i\ge1\\i\text{ odd}}}
 \frac{8(2i+1)}{i^2(i+1)^2}g(x)C_{i-1}^{(3/2)}(1-2x)
 =-2\bigl(x\log x+(1-x)\log(1-x)\bigr),$$

where $0\log0=0$. The last series converges absolutely and uniformly
on $[0,1]$. The function on the right is the canonical
[Kimura–Ohta function](mean-absorption-time.md).

## Depends on

- [Analytic Gegenbauer series](kimura-1955-eigen-series-convergence-and-pde-for.md)

## Proof depends on

- [Jacobi normalization and Gegenbauer norms](../transition-densities-of-wright-fisher-diffusions/jacobi-and-gegenbauer-polynomials-on-0-1.md)
- [Kimura–Ohta function](mean-absorption-time.md)

## Expansion

Let $P_i$ denote the classical Legendre polynomial. The identity
$C_{i-1}^{(3/2)}=P_i'$ gives
$\int_0^1C_{i-1}^{(3/2)}(1-2y)\,dy=(1-(-1)^i)/2$.
The positive-time uniform convergence permits this spatial integration.
Only odd $i$ survive, and their second eigenvalue is $\lambda_3=6$.

Integration down to $t=0$ requires more than that positive-time bound.
The Legendre identities $|P_i(z)|\le1$ and
$(1-z^2)P_i'(z)=i(P_{i-1}(z)-zP_i(z))$ imply
$|g(x)C_{i-1}^{(3/2)}(1-2x)|\le i/2$.
Thus the sum of the time integrals of the absolute summands is uniformly
bounded by
$\sum_{i\text{ odd}}4(2i+1)/(i(i+1)^2)<\infty$.
Absolute Fubini proves the time-integration formula and uniform convergence.

To identify the sum without unjustified twice-termwise differentiation,
work in $L^2(dx/g)$. The functions $\varphi_i=gC_{i-1}^{(3/2)}$
are complete there: multiplication by $g$ identifies this space with
$L^2(g\,dx)$, where the Gegenbauer polynomials span all polynomials;
Weierstrass approximation and density of continuous functions establish
completeness. Write $T(x)=-2(x\log x+(1-x)\log(1-x))$.
It belongs to $L^2(dx/g)$, since $T(x)=O(x|\log x|)$ at zero and
symmetrically at one. Also $T''=-2/g$ in the interior.
Twice integrating by parts, with vanishing boundary terms
$T\varphi_i'$ and $T'\varphi_i$, gives
$\int_0^1T(x)C_{i-1}^{(3/2)}(1-2x)\,dx
=\lambda_i^{-1}\int_0^1C_{i-1}^{(3/2)}(1-2x)\,dx$.
Dividing by $h_i$ gives exactly the displayed coefficients.
Completeness identifies the series with $T$ in $L^2(dx/g)$;
the uniform convergence and continuity identify it at every point.

The probabilistic interpretation requires the separate identification of
the killed transition density. **Given that identification**,
$S_t(x)=\mathbb P_x(\tau>t)$, the absorption CDF is $1-S_t(x)$, and the
time integral is $\mathbb E_x\tau$. Without it, this page calls $S_t$
an integrated series, not an established survival function.

## Sources

- M. Kimura, *Solution of a process of random genetic drift with a continuous model* (1955), <https://doi.org/10.1073/pnas.41.3.144>, bibliographic attribution only. The analytic identities and the zero-time integrability argument are derived above.
