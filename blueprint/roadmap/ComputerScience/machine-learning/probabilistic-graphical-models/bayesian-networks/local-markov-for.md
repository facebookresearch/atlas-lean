# The local Markov property for a graph

**The local Markov property for a graph** (Lauritzen 2009, property (L)): let $\alpha$ be a
finite type, $P : \alpha^n \to \mathbb{R}$ and $B$ a Bayesian network on the nodes
$0, \dots, n - 1$. Then $P$ has the local Markov property for the graph of $B$ if, under $P$,
every node $k$ is conditionally independent of the nodes that are neither descendants nor
parents of $k$, given the parents of $k$.
