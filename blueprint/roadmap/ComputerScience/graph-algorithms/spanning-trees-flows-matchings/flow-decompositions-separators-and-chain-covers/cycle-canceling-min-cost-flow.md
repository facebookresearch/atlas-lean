# Cycle canceling computes minimum-cost flows

For a capacitated network with integral capacities, integral arc costs and integral vertex balances, the **cycle-canceling algorithm** starts from any feasible flow (found by a maximum-flow computation) and repeatedly augments the minimum residual capacity around a negative-cost cycle of the residual network, found by Bellman-Ford negative-cycle detection, until none remains. It terminates with a minimum-cost feasible flow, together with integral node potentials certifying optimality by complementary slackness; the same procedure applied after computing a maximum flow yields a minimum-cost maximum flow.

## Proof sketch

Each cancellation lowers the integral cost by at least one, and the cost is bounded below. At termination, the absence of negative residual cycles gives shortest-path potentials, and Klein's criterion gives optimality.

## Depends on

- [Optimality conditions for minimum-cost flows](../../linear-programming-and-flows/optimality-conditions-for-minimum-cost-flows.md)
- [Bellman–Ford result](../../shortest-paths/bellman-ford-algorithm/result.md)

## Proof depends on

- [Optimality conditions for minimum-cost flows](../../linear-programming-and-flows/optimality-conditions-for-minimum-cost-flows.md)

## Sources

- M. Klein, "A Primal Method for Minimal Cost Flows with Applications to the Assignment and Transportation Problems", Management Science 14(3), 1967.
- A. Schrijver, "Combinatorial Optimization: Polyhedra and Efficiency", Springer, 2003.
