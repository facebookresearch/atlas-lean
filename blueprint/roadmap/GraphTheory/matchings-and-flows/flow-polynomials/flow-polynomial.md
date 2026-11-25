# Flow polynomial of a multigraph

For a finite multigraph given by finite sets $V$ of vertices and $E$ of edges and an end map assigning to each edge an unordered pair of vertices (loops and parallel edges allowed) and a real number $x$, the flow polynomial at $x$ is

$$\Phi(x) = \sum_{A \subseteq E} (-1)^{|E| - |A|}\, x^{|A| + c(A) - |V|},$$

where $c(A)$ is the number of connected components of the spanning subgraph with edge set $A$ (the exponent never becomes negative, and $x^0 = 1$). For a positive integer $k$, $\Phi(k)$ counts the nowhere-zero $\mathbb{Z}/k$-flows.
