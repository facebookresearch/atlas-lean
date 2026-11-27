# Feller's boundary classification

For a one-dimensional diffusion on an interval, Döring and Kyprianou (2020, Section 1) recall Feller's classification of an endpoint by two properties: it is accessible if it is reached in finite time from the interior, and enterable if the diffusion started there can enter the interior. The endpoint is regular if it is accessible and enterable, exit if it is accessible but not enterable, entrance if it is enterable but not accessible, and natural if it is neither.

Accessibility is decided by the scale function $S$ and the speed density. For the generator $b\partial_x + \frac12a^2\partial_x^2$ on $(x_m, x_M)$ with speed density $V = 1/(a^2S')$, the probability of leaving $(x_m, x_M)$ through $x_m$ is the scale ratio $(S(x_M) - S(x))/(S(x_M) - S(x_m))$, so the lower endpoint is not reached when $S(x) \to -\infty$ as $x \downarrow x_m$. When $S(x_m) > -\infty$, the lower endpoint is accessible exactly when the integral $2\int_{x_m}^xS'(y)\int_y^xV(y_1)\,dy_1\,dy$ is finite (Feller 1952; Karlin and Taylor 1981, Chapter 15). By Fubini's theorem this integral equals

$$2\int_{x_m}^x\bigl(S(y) - S(x_m)\bigr)V(y)\,dy,$$

so the endpoint is accessible exactly when $S(x_m) > -\infty$ and this integral is finite. The integral is a finiteness test only; it is not the mean time to reach $x_m$ conditioned on reaching it first. For standard Brownian motion on $(0, 1)$, $S(y) = y$ and $V = 1$, and the integral is $x^2$; but with $T$ the exit time from $(0, 1)$, $h(x) = P_x(X_T = 0) = 1 - x$ and $u(x) = E_x[T;\ X_T = 0]$ solves $\frac12u'' = -h$ with $u(0) = u(1) = 0$, so $u(x)/h(x) = x(2 - x)/3$, which is $7/48$ rather than $1/16$ at $x = 1/4$. The conditional mean is instead the Green's-function quantity $(G h)/h$ of the page on path functionals between prescribed frequencies. Boundary conditions are needed only at endpoints that can be reached: if both endpoints are inaccessible, exactly one process satisfies the backward equation; if at least one endpoint is accessible, infinitely many do, the simplest being the absorbing-barrier process, which stops when an endpoint is reached (Feller 1954, Section 2). At an endpoint that is reached, the behaviour must be specified separately: absorbing, elastic or reflecting, holding at the endpoint for an exponentially distributed time, or jumping back into the interior (Feller 1954, Section 2).

## Depends on

- [Scale function of a one-dimensional diffusion](../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/scale-function.md)
- [Speed density of a one-dimensional diffusion](../../../Biology/population-genetics/diffusion-theory/scale-and-speed-of-one-dimensional-diffusions/speed-density.md)

## Expansion

1. Exit probabilities from the scale function, and inaccessibility when $S(x_m) = -\infty$.
2. Feller's accessibility integral and its Fubini form, as a test for reaching the endpoint in finite time; it is not the conditional mean hitting time.
3. Feller's enterability integral $\int_{x_m}^x(S(x) - S(y))V(y)\,dy$ and the resulting four-way classification, as a separate statement.
4. The boundary behaviours at an accessible endpoint (absorbing, elastic or reflecting, holding at the endpoint, jumping) and the boundary conditions that select them.

## Sources

- L. Döring and A. E. Kyprianou, Entrance and exit at infinity for stable jump diffusions, Ann. Probab. 48 (2020), 1220–1265, Section 1. <https://doi.org/10.1214/19-AOP1389>
- S. Karlin and H. M. Taylor, *A Second Course in Stochastic Processes*, Academic Press, New York (1981), Chapter 15 (exit probabilities from the scale function and Feller's accessibility test).
- W. Feller, Diffusion processes in one dimension, Trans. Amer. Math. Soc. 77 (1954), 1–31, Section 2.
- Original result: W. Feller, The parabolic differential equations and the associated semi-groups of transformations, Ann. of Math. 55 (1952), 468–519. <https://doi.org/10.2307/1969644> The four boundary types and their definition by accessibility and enterability follow Döring and Kyprianou (2020, Section 1).
