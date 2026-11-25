# The global Markov property for a graph

**The global Markov property for a graph** (Lauritzen 2009, property (G)): let $\alpha$ be a
finite type, $P : \alpha^n \to \mathbb{R}$ and $B$ a Bayesian network on the nodes
$0, \dots, n - 1$. Then $P$ has the global Markov property for the graph of $B$ if for all sets
$X, Y, Z$ of nodes such that $Z$ d-separates $X$ from $Y$ in the graph of $B$, $X$ and $Y$ are
conditionally independent given $Z$ under $P$.
