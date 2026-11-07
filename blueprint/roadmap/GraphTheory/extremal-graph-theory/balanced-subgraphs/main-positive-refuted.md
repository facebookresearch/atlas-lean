# The Erdős–Simonovits balanced subgraph claim is false

It is not the case that for all reals
$\varepsilon$ and $\alpha$ with $0 < \varepsilon < 1$ and $0 < \alpha < 1$, for all sufficiently
large real $D$ and then all sufficiently large $n$, every simple graph $G$ on the vertex set
$\{0, \dots, n-1\}$ with more than $n^{1+\alpha}$ edges has a (not necessarily induced) subgraph
$H$ with some number $m$ of vertices such that $H$ is $D$-balanced (its maximum degree is at most
$D$ times its minimum degree), $m > n^{1-\alpha}$, and $H$ has more than $\varepsilon m^{1+\alpha}$
edges.

The disproof uses a bipartite witness: the requirement $m > n^{1-\alpha}$ is too strong, and the
correct order is $n^{\alpha}$ per Jun Gao and Jiang–Longbrake [JiLo25], per erdosproblems.com/1077.

## Sources

- External Lean disproof of Erdos Problem 1077, plby/lean-proofs, https://github.com/plby/lean-proofs/blob/dfe2d78128b493c572cf525b1b8edf4897fb7664/src/latest/ErdosProblems/Erdos1077.lean#L265.
