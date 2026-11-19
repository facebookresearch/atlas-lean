# Edmonds's question: an NP description of perfect graphs

The perfect-graph decision
problem, which accepts exactly the bitstrings that decode to a valid adjacency-matrix instance
whose graph is perfect, lies in the complexity class NP: there are a polynomial $p$ with
natural-number coefficients and a polynomial-time verifier $R$ on pairs of bitstrings such that a
bitstring $x$ is accepted if and only if $R$ accepts $(x, w)$ for some bitstring $w$ of length at
most $p(|x|)$.

## Sources

- ARCC workshop *The Perfect Graph Conjecture* (American Institute of Mathematics, 2002), workshop materials, *Recognition of Perfect Graphs*, item 4, *NP Characterization of Perfect Graphs*, contributed by Jack Edmonds, https://aimath.org/pastworkshops/perfectgraph.html.
