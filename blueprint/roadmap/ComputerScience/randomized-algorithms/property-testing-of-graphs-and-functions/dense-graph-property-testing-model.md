# Property testing in the dense graph model

In the *dense graph model* a graph on vertex set $[n]$ is accessed through an adjacency oracle answering "is $\{u, v\}$ an edge?". A graph property $\Pi$ is a set of graphs closed under isomorphism. A graph $G$ is *$\varepsilon$-far* from $\Pi$ if every graph in $\Pi$ on $[n]$ differs from $G$ in more than $\varepsilon n^2$ vertex pairs (edit distance). A *one-sided tester* for $\Pi$ with proximity $\varepsilon$ and query complexity $q$ is a randomized oracle algorithm making at most $q$ queries that accepts every $G \in \Pi$ with probability $1$ and rejects every graph $\varepsilon$-far from $\Pi$ with probability at least $2/3$. $\Pi$ is *testable* if $q$ depends only on $\varepsilon$, not on $n$.

## Sources

- O. Goldreich, S. Goldwasser and D. Ron, "Property Testing and Its Connection to Learning and Approximation", Journal of the ACM 45(4), 1998.
- O. Goldreich, "Introduction to Property Testing", Cambridge University Press, 2017.
