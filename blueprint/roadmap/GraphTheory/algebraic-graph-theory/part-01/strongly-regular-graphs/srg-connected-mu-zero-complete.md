# Connected strongly regular graphs with μ = 0 are complete

Let $G$ be a finite strongly
regular graph with parameters $(n, k, \ell, \mu)$ where $\mu = 0$: $G$ has $n$ vertices, every
vertex has degree $k$, any two adjacent vertices have exactly $\ell$ common neighbors, and any
two distinct nonadjacent vertices have no common neighbor. If $G$ is connected, then $G$ is
complete, that is, any two distinct vertices of $G$ are adjacent.

Proof: The $\mu = 0$ common-neighbor count makes every nontrivial two-edge walk a
triangle, so walk induction makes each component a clique. Connectedness then
gives completeness. Brouwer and Haemers, Section 9.1.4, state the component
fact: $\mu = 0$ makes the graph a disjoint union of complete graphs.

## Sources

- A. E. Brouwer and W. H. Haemers, Spectra of Graphs, Springer 2012, Ch. 9 (disconnected and complete strongly regular graphs); C. Godsil and G. Royle, Algebraic Graph Theory, GTM 207, Ch. 10.
