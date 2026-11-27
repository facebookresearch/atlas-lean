# Lax's solution of the Riemann problem for small data

This node covers Lax's theorem on the Riemann problem. Let $U \subset \mathbb{R}^n$ be open and $f : U \to \mathbb{R}^n$ smooth, such that
$u_t + f(u)_x = 0$ is strictly hyperbolic on $U$ and each characteristic field is either genuinely nonlinear or linearly degenerate. Then for
every $\bar u \in U$ there is $\delta > 0$ such that for all $u_L, u_R$ within $\delta$ of $\bar u$ the Riemann problem with $u(x, 0) = u_L$ for
$x < 0$ and $u_R$ for $x > 0$ has exactly one solution of the following form: a self-similar weak solution consisting of at most $n + 1$
constant states joined, in order of increasing characteristic family, by centred rarefaction waves, shocks satisfying the Lax entropy
inequalities, or contact discontinuities.

## Expansion

A good expansion constructs the wave curves of each family through a state (rarefaction and Hugoniot curves, tangent to the
right eigenvectors to second order), proves that their composition is a local diffeomorphism near $\bar u$ by the inverse function theorem,
and verifies the entropy conditions. The Euler equations of gas dynamics as an instance, large data and numerical convergence are separate
nodes.

## Sources

- P. D. Lax, Hyperbolic systems of conservation laws II, *Communications on Pure and Applied Mathematics* 10 (1957) 537-566.
- J. Smoller, *Shock Waves and Reaction-Diffusion Equations*, 2nd edition, Springer, 1994.
