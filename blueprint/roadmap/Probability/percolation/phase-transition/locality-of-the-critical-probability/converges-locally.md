# Local convergence of rooted graphs

Let $(G_n)_{n \in \mathbb{N}}$ be graphs with vertex sets $V_n$ and $G$ a graph with vertex set $W$. The sequence $G_n$ converges locally to $G$ if for every $r \in \mathbb{N}$ there is $N$ such that for every $n \ge N$, every $v_n \in V_n$ and every $v \in W$, there is a graph isomorphism

$$B_{G_n}(v_n, r) \cong B_G(v, r)$$

sending $v_n$ to $v$, where $B_H(u, r)$ is the [ball](ball.md) of radius $r$: the induced subgraph of $H$ on the vertices $w$ with $d_H(u, w) \le r$, where an unreachable vertex has distance $0$. On disconnected graphs these balls differ from the usual ones: two isolated vertices and a single isolated vertex have isomorphic ordinary balls of radius $0$, but the balls here have two and one vertices. For connected graphs this is the form of convergence in Benjamini's local metric that Hutchcroft uses for transitive graphs.
