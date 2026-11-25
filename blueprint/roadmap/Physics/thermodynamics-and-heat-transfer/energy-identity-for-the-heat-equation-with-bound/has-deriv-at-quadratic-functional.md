# Symmetric G, no inputs: ∑ C T²/2 has rate −½ ∑∑ G times squared gaps

Let `ι` be a finite index set of nodes, with capacities `C i`, conductances `G i j` such that
`G i j = G j i`, temperatures `T i` differentiable at time `t` with derivatives `dT i`, such that
every node obeys `C i dT i = ∑_j G i j (T j(t) - T i(t))`. Then

`∑_i C i T i²/2` has at `t` the derivative `-∑_i ∑_j G i j (T i(t) - T j(t))²/2`.

It is the case with no boundary conductance, zero reference and no heating power of the
[zone quadratic dissipation identity](../heat-balance-of-lumped-thermal-networks/quadratic-dissipation-has-deriv-at.md).
