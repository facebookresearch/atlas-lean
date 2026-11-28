# Saranurak-Wang expander pruning under online edge deletions

Let $G = (V, E)$ be a $\varphi$-expander with $m$ edges. There is a deterministic algorithm with access to the adjacency lists of $G$ that, given an online sequence of $k \le \varphi m / 10$ edge deletions, maintains a pruned set $P \subseteq V$ as follows. Writing $G_i$ and $P_i$ for the graph and the pruned set after the $i$-th deletion, for all $i \le k$:

1. $P_0 = \emptyset$ and $P_i \subseteq P_{i+1}$;
2. $\mathrm{vol}_G(P_i) \le 8i/\varphi$ and $|E_{G_i}(P_i, V \setminus P_i)| \le 4i$;
3. $G_i\{V \setminus P_i\}$ is a $\varphi/6$-expander.

The total time to produce $P_0, \dots, P_k$ is $O(k \log m / \varphi^2)$.

## Proof sketch

Each deletion of an edge $\{u, v\}$ outside $P$ is treated like a new boundary edge in the trimming lemma: it injects $2/\varphi$ units of source mass at $u$ and at $v$. The bounded-height local flow is continued incrementally rather than restarted, and every set that cannot route its mass is moved into $P$. Since $G$ was a $\varphi$-expander, $V$ is nearly $\varphi$-expanding in each $G_i$ relative to $P_i$, so the trimming analysis gives the volume, boundary and conductance bounds, and the reuse of flow across rounds gives total work $O(k \log m/\varphi^2)$.

## Depends on

- [Cut conductance, phi-expanders and degree-preserving induced subgraphs](conductance-and-phi-expanders.md)

## Proof depends on

- [Trimming a nearly expanding set into a degree-preserving phi/6-expander](trimming-lemma.md)

## Sources

- Thatchaphol Saranurak, Di Wang, "Expander Decomposition and Pruning: Faster, Stronger, and Simpler", SODA (2019), arXiv:1812.08958.
- Danupon Nanongkai, Thatchaphol Saranurak, Christian Wulff-Nilsen, "Dynamic Minimum Spanning Forest with Subpolynomial Worst-case Update Time", FOCS (2017), arXiv:1708.03962.
