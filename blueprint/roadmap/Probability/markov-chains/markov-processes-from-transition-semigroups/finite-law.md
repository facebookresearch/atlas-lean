# Markov law at a finite set of times

Let $(K_t)_{t \ge 0}$ be kernels on $E$, $x \in E$, and $J \subset [0, \infty)$ a finite set with
increasing enumeration $j_0 < j_1 < \dots < j_{k-1}$. The Markov law at the times $J$ is the
measure on $E^J$ obtained from the [finite-dimensional law](finite-chain-law.md)
$F_{0, (j_0, \dots, j_{k-1})}(x, \cdot)$ on $E^k$ by [reindexing the coordinates by
$J$](order-measurable-equiv.md).

No condition $K_0(x, \cdot) = \delta_x$ is imposed: when $0 \in J$, the marginal at time $0$ is
$K_0(x, \cdot)$, which is the point mass $\delta_x$ only when $K_0$ is the identity kernel.
