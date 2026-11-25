# CFL condition: numerical domain of dependence must contain the true one

Consider the advection equation $q_t + a q_x = 0$ on an infinite or periodic grid with spacing $\Delta x$ and time step $\Delta t$, and an
explicit scheme of stencil radius $r$: $q_j^{n+1}$ depends only on $q_{j-r}^n, \dots, q_{j+r}^n$.

1. **Influence lemma.** The computed value $q_j^n$ depends only on the initial values with indices in $\{j - rn, \dots, j + rn\}$:
   changing the initial data outside this window does not change it.
2. **CFL condition.** If $\lvert a \rvert \Delta t/\Delta x > r$, the scheme with initial data sampled pointwise from smooth functions does
   not converge to the exact solution for all smooth initial data as $\Delta x \to 0$ with $\Delta t/\Delta x$ fixed, because the
   initial data can be changed near $x - at$, inside the exact domain of dependence, but outside the numerical one.

The CFL condition is necessary for convergence. It is not in general necessary for stability alone (a stable but
inconsistent scheme, such as $q_j^{n+1} = q_j^n$ for $a \ne 0$, violates it), and it is not sufficient for stability.

## Related topics

- [Discrete-time dynamical system (input-driven state-update map)](../control-theory/discrete-time-systems-and-safety/discrete-time-dynamical-system.md)

## Sources

- AMath 574 Notes: Conservation Laws and Finite Volume Methods (lecture 5) — R. J. LeVeque, University of Washington AMath 574 (after Finite Volume Methods for Hyperbolic Problems, Sec. 4.4), slides 'The CFL Condition' and 'Numerical domain of dependence'. <https://faculty.washington.edu/rjl/classes/hyperbolic2013/am574w2011/am574lecture5nup3.pdf>
