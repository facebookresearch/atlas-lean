# PC adjacency phase fails on the XOR collider

Let $X_0, X_1$ be independent fair coins and $X_2 = X_0 \oplus X_1$, a Bayesian network with edges $0 \to 2 \leftarrow 1$. The population adjacency phase of the PC algorithm, run with the true conditional independences of this law, does not return the skeleton of the graph.
