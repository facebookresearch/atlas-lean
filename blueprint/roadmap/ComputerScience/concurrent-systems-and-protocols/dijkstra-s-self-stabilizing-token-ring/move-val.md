# The value a privileged machine moves to

In Dijkstra's token ring with machines indexed by $\mathbb{Z}/(n+1)$ and values in $\mathbb{Z}/K$, the move of machine $i$ in configuration $x$ produces the value $x_0 + 1$ (computed in $\mathbb{Z}/K$) when $i = 0$, and the value $x_{i-1}$ of its predecessor otherwise. For $K = 0$ the values are integers, since $\mathbb{Z}/0 = \mathbb{Z}$, so machine $0$ moves to $x_0 + 1$ as an unbounded integer rather than wrapping modulo $K$.
