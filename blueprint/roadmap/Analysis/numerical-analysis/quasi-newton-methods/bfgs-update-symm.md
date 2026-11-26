# The BFGS update preserves symmetry

If $B$ is symmetric ($\langle Bu, v \rangle = \langle u, Bv \rangle$ for all $u, v$), so is its
[BFGS update](bfgs-update.md) $B_+$: the two corrections $(Bs)(Bs)^\top$ and $y y^\top$ are symmetric.

## Sources

- J. E. Dennis and R. B. Schnabel, *Numerical Methods for Unconstrained Optimization and Nonlinear Equations*, Prentice-Hall 1983 (SIAM reprint 1996), Section 9.2: $H_+ - H_c$ is a symmetric matrix of rank at most two.
