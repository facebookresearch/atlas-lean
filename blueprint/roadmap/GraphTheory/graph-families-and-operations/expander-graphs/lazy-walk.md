# Lazy random walk on a graph

Let $G$ be a simple graph on a finite vertex set $V$. The lazy simple random walk matrix $P$ has entries $P(x, y)$ equal to $1/2$ if $x = y$, to $1/(2\deg x)$ if $y$ is adjacent to $x$, and to $0$ otherwise. When $G$ has no isolated vertex, each row of $P$ sums to $1$, so $P$ is a transition matrix; at an isolated vertex $x$, the row is $1/2$ at $x$ and $0$ elsewhere.
