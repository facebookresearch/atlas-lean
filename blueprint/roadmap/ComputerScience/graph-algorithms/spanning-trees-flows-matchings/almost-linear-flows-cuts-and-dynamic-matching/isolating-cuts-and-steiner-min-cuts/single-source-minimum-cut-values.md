# Single-source minimum cut values

Let $G = (V, E, w)$ be a connected undirected graph with positive weights and let $s \in V$. The *single-source minimum cuts problem* asks for the values $\lambda_G(s, v)$ for every $v \in V \setminus \{s\}$; the *all-pairs minimum cuts problem* asks for $\lambda_G(u,v)$ for all pairs. A cut-equivalent tree solves both. Because $\lambda_G(u, v) \ge \min(\lambda_G(s,u), \lambda_G(s,v))$ for every $s$, the single-source values determine, for every threshold $k$, which vertices lie in the same $k$-edge-connected class as $s$.

## Depends on

- [Edge cuts separating two vertices](../../../../../GraphTheory/paths-cycles-connectivity/menger-s-theorem/is-stedge-cut.md)
- [Flow-equivalent and cut-equivalent trees of weighted graphs](../../../../../GraphTheory/paths-cycles-connectivity/cactus-representation-and-sparse-certificates/flow-equivalent-and-cut-equivalent-trees.md)

## Sources

- Amir Abboud, Robert Krauthgamer, Jason Li, Debmalya Panigrahi, Thatchaphol Saranurak, Ohad Trabelsi, "Breaking the Cubic Barrier for All-Pairs Max-Flow: Gomory-Hu Tree in Nearly Quadratic Time", FOCS (2022), arXiv:2111.04958.
- Jason Li, Debmalya Panigrahi, "Approximate Gomory-Hu Tree Is Faster Than n-1 Max-Flows", STOC (2021), arXiv:2111.02022.
