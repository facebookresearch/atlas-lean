# Distance-vector round

Let $G$ be a simple graph whose vertices are the nodes of a
network and whose edges are its links, let $c(x, v) \in \mathbb{N}$ be the cost of the direct link
from $x$ to $v$, and let $D_x(y) \in \mathbb{N} \cup \{\infty\}$ be the estimate of node $x$ of its
distance to node $y$, where $\infty$ means that $x$ knows no route to $y$. In one round every node
recomputes its estimates from those its neighbors held before the round: node $x$ estimates
its distance to itself as $0$ and its distance to every other node $y$ as

$$D'_x(y) = \min_{v \sim x} \bigl(c(x, v) + D_v(y)\bigr),$$

the minimum over the neighbors $v$ of $x$ in $G$, which is $\infty$ when $x$ has no neighbor.

## Sources

- A. C. Snoeren, *Distance-vector Routing*, Lecture 13 of CSE 123: Computer Networks, UC San Diego, Fall 2010, slide 5.
