# Moral graph on a vertex set

For a Bayesian network $b$ on vertices $\{0, \dots, n-1\}$ and a set $A$ of vertices, the moral graph on $A$ makes distinct $i, j \in A$ adjacent when they are adjacent in the skeleton of $b$ (an edge in either direction), or they are both parents of a common child in $A$. Vertices outside $A$ are isolated. For an ancestral set $A$ this is Lauritzen's moral graph of the subnetwork on $A$.
