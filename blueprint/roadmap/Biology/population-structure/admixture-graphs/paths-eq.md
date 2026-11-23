# First-step equation for root-ward paths

In every [admixture graph](admixture-graph.md) and for every node $X$, the set of [root-ward paths](paths.md) from $X$ is $\{(X)\}$ if $\mathrm{pa}(X) = \varnothing$, and otherwise

$$\bigcup_{Y \in \mathrm{pa}(X)} \{(X, v_1, \dots, v_k) : (v_1, \dots, v_k) \text{ a root-ward path from } Y\}.$$
