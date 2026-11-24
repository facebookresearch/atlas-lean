# With symmetric conductances the stored heat changes at the input rate

Let `ι` be a finite index set of nodes, with capacities `C i`, conductances `G i j` such that
`G i j = G j i`, temperatures `T i` differentiable at time `t` with derivatives `dT i` and inputs
`Q i`, such that every node obeys `C i dT i = ∑_j G i j (T j(t) - T i(t)) + Q i`. Then the stored
heat `∑_i C i T i` has at `t` the derivative `∑_i Q i`: conduction between nodes cancels. It is the
case without heating power of the
[zone heat-inventory balance](../heat-balance-of-lumped-thermal-networks/heat-inventory-has-deriv-at.md).
