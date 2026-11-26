# Joint law of the first nodes

The joint law of the first $m$ nodes of a kernel causal Bayesian network with nodes ordered $0, \dots, n - 1$ is defined by recursion on $m \le n$, as the ordered product of the nodes' Markov kernels. For $m = 0$ it is the Dirac measure at the empty tuple. The law of the first $m + 1$ nodes is the composition-product $\mu_m \otimes \kappa_m$ of the law $\mu_m$ of the first $m$ nodes with the kernel $\kappa_m$ of node $m$, which reads the values of the parents of node $m$ among the first $m$ nodes, pushed forward by appending the value of node $m$ to the tuple.
