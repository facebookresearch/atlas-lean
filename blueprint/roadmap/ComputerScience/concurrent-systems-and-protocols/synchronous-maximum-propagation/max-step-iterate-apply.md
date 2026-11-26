# Maximum propagation after k rounds

Let $n$ be a natural number, $\rho$ a map from $\{0, \dots, n - 1\}$ to itself, and $v$ an assignment of natural numbers to the nodes. In one round of maximum propagation every node $i$ replaces its value by the maximum of its own value and the value of node $\rho(i)$. Then for every $k$ and every node $i$, after $k$ rounds node $i$ holds

$$\max_{0 \le t \le k} v(\rho^t(i)),$$

the maximum of the initial values at the $k + 1$ nodes $i, \rho(i), \dots, \rho^k(i)$, which need not be distinct; here $\rho^t$ is the $t$-fold iterate of $\rho$ and $\rho^0(i) = i$.
