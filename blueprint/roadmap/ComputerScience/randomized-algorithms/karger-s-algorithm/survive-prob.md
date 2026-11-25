# Probability that a run outputs a given cut

For a map $X$ from vertices to booleans, a
fuel bound $f$ and a multigraph $G$, this is the probability that the contraction process on $G$
(contract an edge chosen uniformly at random, counted with multiplicity, while more than two
vertices and at least one edge remain, making at most $f$ contractions) never contracts an edge
whose endpoints $X$ separates and ends with exactly two vertices on which $X$ takes both values.

Explicitly: if $f = 0$, or $G$ has at most two vertices, or $G$ has no edges, the value is $1$
when $G$ has exactly two vertices and $X$ is a cut of $G$, and $0$ otherwise. Otherwise it is the
average over the edges $e$ of $G$, counted with multiplicity, of the value for fuel $f - 1$ on
the contraction of $G$ along $e$ when $X$ agrees on the two endpoints of $e$, and of $0$ when it
does not.
