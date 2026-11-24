# Feller's boundary classification

For a one-dimensional diffusion on an interval, Döring and Kyprianou (2020, Section 1) recall Feller's classification of an endpoint by two properties: it is accessible if it is reached in finite time from the interior, and enterable if the diffusion started there can enter the interior. The endpoint is regular if it is accessible and enterable, exit if it is accessible but not enterable, entrance if it is enterable but not accessible, and natural if it is neither.

Accessibility is decided by the scale function $S$ and the speed density. For the generator $b\partial_x + \frac12a^2\partial_x^2$ on $(x_m, x_M)$ with speed density $V = 1/(a^2S')$, the probability of leaving $(x_m, x_M)$ through $x_m$ is the scale ratio $(S(x_M) - S(x))/(S(x_M) - S(x_m))$, so the lower endpoint is not reached when $S(x) \to -\infty$ as $x \downarrow x_m$; when $S(x_m) > -\infty$, the mean time to reach $x_m + \varepsilon$ conditioned on reaching it first tends as $\varepsilon \downarrow 0$ to $2\int_{x_m}^xS'(y)\int_y^xV(y_1)\,dy_1\,dy$ (lecture notes on one-dimensional diffusions and boundary conditions, Sections 4.1–4.2, equations (4.5)–(4.14)). By Fubini's theorem this limit equals

$$2\int_{x_m}^x\bigl(S(y) - S(x_m)\bigr)V(y)\,dy,$$

so the endpoint is accessible in finite mean time exactly when this integral is finite. Boundary conditions are needed only at endpoints that can be reached: if no endpoint is reached, the minimal solution of the backward equation is a proper distribution; otherwise it describes the process absorbed at the endpoint, and other processes are extensions of it (Etheridge, lecture notes, Section 4). At an endpoint that is reached, the behaviour must be specified separately: absorbing, instantaneously reflecting (the set of times spent at the endpoint has Lebesgue measure zero), slowly reflecting or sticky (positive Lebesgue measure), or jumping back into the interior (lecture notes on boundary conditions, Section 5.3). The type depends on the rates at which the coefficients degenerate at the endpoint, not on their smoothness (same notes, Section 5 and the Cox–Ingersoll–Ross example of Section 6).

## Depends on

- [Scale function of a one-dimensional diffusion](../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/scale-function.md)
- [Speed density of a one-dimensional diffusion](../../../Biology/population-genetics/diffusion-theory/scale-and-speed-of-one-dimensional-diffusions/speed-density.md)

## Expansion

1. Exit probabilities from the scale function, and inaccessibility when $S(x_m) = -\infty$.
2. The limiting conditioned mean hitting time and its Fubini form as the accessibility integral.
3. Feller's enterability integral $\int_{x_m}^x(S(x) - S(y))V(y)\,dy$ and the resulting four-way classification, as a separate statement.
4. The boundary behaviours at an accessible endpoint (absorbing, instantaneously reflecting, sticky, jumping) and the boundary conditions that select them.

## Sources

- L. Döring and A. E. Kyprianou, Entrance and exit at infinity for stable jump diffusions, arXiv:1802.01672 (2020), Section 1. <https://arxiv.org/abs/1802.01672>
- *One dimensional diffusions and boundary conditions*, lecture 17 of the course Stochastic methods for physics and biology, University of Helsinki, spring 2012, Sections 4–6.
- A. Etheridge, *Diffusion process models in mathematical genetics*, lecture notes, University of Oxford, Section 4.
- Original result: W. Feller, The parabolic differential equations and the associated semi-groups of transformations, Ann. of Math. 55 (1952), 468–519. <https://doi.org/10.2307/1969644> The four boundary types and their definition by accessibility and enterability follow Döring and Kyprianou (2020, Section 1).
