# Diameter of an open percolation cluster

Let $G$ be a simple graph with vertex set $V$, let $\omega$ assign open or closed to every unordered pair of vertices, and let $x \in V$. Let $C_x$ be the open cluster of $x$: the set of vertices joined to $x$ by a path of edges $e$ of $G$ with $\omega(e)$ open. The cluster diameter of $x$ is the diameter of the graph on $C_x$ whose edges are the open edges of $G$ between vertices of $C_x$,

$$\operatorname{diam}(C_x) = \sup_{y, z \in C_x} d_{C_x}(y, z),$$

with distances measured inside the cluster. It is a natural number, read as $0$ when this supremum is infinite.
