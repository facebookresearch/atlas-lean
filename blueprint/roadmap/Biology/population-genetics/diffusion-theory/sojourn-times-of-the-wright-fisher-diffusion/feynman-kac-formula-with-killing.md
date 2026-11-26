# Feynman–Kac formula with killing for the Wright–Fisher diffusion

This page covers a research target: for the Wright–Fisher diffusion with generator $L$, absorbed at its exit time $\tau$ from $(0, 1)$, a killing rate $q \ge 0$, a running payoff $g$ and a terminal payoff $h$ at the endpoints, the function

$$v(x) = \mathbb{E}_x\Bigl[\int_0^\tau e^{-\int_0^t q(X_s)\, ds} g(X_t)\, dt + e^{-\int_0^\tau q(X_s)\, ds} h(X_\tau)\Bigr]$$

is to be characterized as the solution of $(L - q) v = -g$ on $(0, 1)$ with $v = h$ at the endpoints, under stated regularity and boundary conditions, for the degenerate coefficient $x(1 - x)$. For $q = 0$ and $h = 0$ this is [the occupation identity](../selection-duality-and-general-one-dimensional-di/green-function-occupation-times-and-mean-exit-ti.md).

## Expansion

Fix the class of $q$, $g$ and $h$ and the boundary conditions, then state and prove the characterization, each case as a page of its own.

Prerequisites:

- [Dirichlet Green's function of a one-dimensional diffusion](../selection-duality-and-general-one-dimensional-di/green-function.md)

## Sources

- S. Karlin and H. M. Taylor, *A Second Course in Stochastic Processes*, Academic Press (1981).
- T. Maruyama, *Stochastic Problems in Population Genetics*, Lecture Notes in Biomathematics 17, Springer (1977), <https://doi.org/10.1007/978-3-642-93065-2>, Chapters 4 and 5.
