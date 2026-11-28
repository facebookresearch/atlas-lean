# Open subgraph of a box configuration

Let $a, b \in \mathbb{N}$ and let $\omega$ assign to each edge of the box $[0, a] \times [0, b]$ of $\mathbb{Z}^2$ the value open or closed. The open graph of $\omega$ is the simple graph on the vertex set $\{0, \dots, a\} \times \{0, \dots, b\}$ in which two distinct vertices $u, v$ are adjacent exactly when they are the endpoints of an open edge: either $\{u, v\} = \{(x, y), (x+1, y)\}$ for an open horizontal edge with $x < a$, or $\{u, v\} = \{(x, y), (x, y+1)\}$ for an open vertical edge with $y < b$.
