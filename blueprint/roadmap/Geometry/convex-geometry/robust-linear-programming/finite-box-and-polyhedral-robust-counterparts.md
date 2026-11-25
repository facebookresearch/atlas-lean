# Robust counterparts for finite, box and polyhedral uncertainty

A robust constraint $\max_{u \in U} f(x, u) \le t$ is equivalent to $f(x, u_s) \le t$ for all $s$ when $U = \{u_1, \dots, u_m\}$ is finite and nonempty. For an affinely perturbed linear constraint $[a_0 + \sum_\ell \zeta_\ell a_\ell]^{\mathsf T}x \le b_0 + \sum_\ell \zeta_\ell b_\ell$ for all $\zeta$ in a nonempty polyhedron $Z = \{\zeta : \exists u,\ P\zeta + Qu + p \ge 0\}$, the constraint holds if and only if there is $y \ge 0$ with $p^{\mathsf T}y + a_0^{\mathsf T}x \le b_0$, $Q^{\mathsf T}y = 0$ and $(P^{\mathsf T}y)_\ell + a_\ell^{\mathsf T}x = b_\ell$ for every $\ell$: if the robust constraint holds, the inner maximization over $Z$ is a feasible and bounded linear program, and strong duality gives the stated certificate; conversely any such $y$ bounds the inner maximum by weak duality. For the box $\zeta \in [-1,1]^L$ with $b_\ell = 0$ this gives $a_0^{\mathsf T}x + \sum_\ell |a_\ell^{\mathsf T}x| \le b_0$; box radii other than $1$ can be absorbed into the $a_\ell$.

## Proof depends on

- [Strong linear programming duality](../linear-programming/strong-linear-programming-duality.md): strong duality for the inner linear program, after writing free variables as differences of nonnegative ones and equalities as pairs of inequalities.

## Background

- [Robust linear programming](README.md): the ellipsoidal robust counterpart, a separate result.

## Sources

- A. Ben-Tal, L. El Ghaoui and A. Nemirovski, *Robust Optimization*, Princeton University Press, 2009, <https://www2.isye.gatech.edu/~nemirovs/FullBookDec11.pdf>, §1.3, Theorem 1.3.4 (polyhedral case, $K$ the nonnegative orthant)
