# Skeleton recovery for an abstract oracle

Let $b$ be a Bayesian network on $n$ nodes and $O$ a conditional-independence oracle that is Markov for $b$ (for distinct $i, j$ and a set $S$ containing neither, d-separation of $i$ and $j$ by $S$ implies $O$ declares them independent given $S$) and adjacency-faithful for $b$ (adjacent $i, j$ are declared dependent given every set containing neither). Then the adjacency phase of the PC algorithm run on $O$ returns the skeleton of $b$.
