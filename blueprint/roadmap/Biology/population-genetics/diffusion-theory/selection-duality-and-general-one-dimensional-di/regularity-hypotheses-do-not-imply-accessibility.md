# Regular coefficients with natural analytic boundary tests

Let $b(x)=0$ and $a(x)=x^2(1-x)^2$ on $(0,1)$, with generator
$L f=b f'+a f''/2$. These satisfy the canonical
[regularity hypotheses](is-regular-diffusion.md): $a$ is continuous and
strictly positive in the interior, and $b/a=0$ is continuous there and
integrable on $[0,1]$, with zero values assigned at the endpoints.
The [scale function](scale-function.md) is $S(x)=x$, and the canonical
[Dirichlet ratio](fixation-prob.md) is $S(p)/S(1)=p$.
This is the same example already described in the general-diffusion
module's warning, with the boundary integrals made explicit here.

Set $c=1/2$, scale density $S'(x)=1$ and speed density
$m(x)=2/(a(x)S'(x))=2/[x^2(1-x)^2]$.
Use **nonnegative extended integrals**, so divergence means $+\infty$,
not the zero assigned to a nonintegrable function by a totalized real
integral. The two lower-boundary tests are

$$\Sigma_0=\int_0^c(S(x)-S(0))m(x)\,dx,
\qquad N_0=\int_0^c(S(c)-S(x))m(x)\,dx.$$

Both are infinite. By reflection, the upper tests
$\Sigma_1=\int_c^1(S(1)-S(x))m(x)\,dx$ and
$N_1=\int_c^1(S(x)-S(c))m(x)\,dx$ are infinite as well.
In the analytic Feller convention, the case $\Sigma=N=\infty$ is called
**natural**. Thus these standing interior regularity assumptions do not
imply finiteness of the boundary-accessibility test.
No boundary-hitting theorem for a constructed stochastic process is
proved here; the value $p$ is established as an analytic Dirichlet
solution, not supplied with a hitting-probability interpretation by
regularity alone.

## Depends on

- [Standing diffusion regularity](is-regular-diffusion.md)
- [Scale function](scale-function.md)
- [Analytic Dirichlet ratio](fixation-prob.md)

## Expansion

For the first integral,
$\Sigma_0=\int_0^{1/2}2/[x(1-x)^2]\,dx
\ge2\int_0^{1/2}dx/x=\infty$.
For the second, for $0<\varepsilon<1/2$,

$$\int_\varepsilon^{1/2}(1/2-x)\frac{2\,dx}{x^2(1-x)^2}
=\frac1{\varepsilon(1-\varepsilon)}-4
\longrightarrow\infty.$$

The identity follows by differentiating $-1/[x(1-x)]$.
Alternatively on $(0,1/4)$ the second integrand is at least $1/(2x^2)$.
Reflection proves the upper-end claims. Since $b/a=0$, the scale density
is one, and $u(x)=x$ directly satisfies $Lu=0$, $u(0)=0$, $u(1)=1$.

The orientation of the second integral is essential. Tonelli gives
$\int_0^c(\int_x^c m(y)\,dy)\,dS(x)=\Sigma_0$;
that is the accessibility integral **again**, not the entrance integral.
The latter is instead
$N_0=\int_0^c(\int_0^x m(y)\,dy)\,dS(x)$, the opposite triangle.
For comparison, neutral Wright–Fisher variance $a(x)=x(1-x)$ has
$\Sigma_0=2\log2<\infty$ but $N_0=\infty$, distinguishing the two tests.
These definitions and calculations are self-contained; they do not
silently depend on an unreviewed general boundary-classification page.

## Sources

- W. Feller, "The parabolic differential equations and the associated semi-groups of transformations", Annals of Mathematics 55 (1952), 468–519, <https://doi.org/10.2307/1969644> (boundary classification). The integrals are computed above.
