# For k > 0, grounding either mass leaves a positive stiffness k

Let `k > 0` and `K = k [[1, -1], [-1, 1]]` the
[two-mass stiffness matrix](stiffness-matrix-two-mass-weights.md). Then:

- deleting the row and column of either mass from `K` gives the `1 × 1`
  [stiffness matrix](../harmonic-oscillators-equilibrium-and-spring-netw/stiffness-matrix.md) `[k]` of one node with a wall spring of stiffness
  `k` and no pair springs;
- that `1 × 1` matrix is positive definite;
- for every real `u`, the [spring energy](spring-energy-two-mass-weights.md) of the two masses with
  displacements `(0, u)`, and also with `(u, 0)`, equals the energy `k u² / 2` of that wall spring
  at displacement `u`.
