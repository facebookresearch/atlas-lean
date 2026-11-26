# Edge-safe walks for metagenomic reconstructions

Let $G$ be a strongly connected directed graph. An **edge-covering metagenomic reconstruction** is a collection of circular walks covering every edge of $G$, and a walk is **edge-safe** if it is a subwalk of some circular walk in every such collection. A walk $w = (v_0, e_0, \dots, e_t, v_{t+1})$ is an **edge-omnitig** if for all $1 \le i \le j \le t$ there is no proper $v_j$–$v_i$ path with first edge different from $e_j$ and last edge different from $e_{i-1}$ (the [omnitig](../../omnitigs-and-safe-walks-in-genome-assembly/is-omnitig.md) condition).

**Theorem.** A walk $w$ in a strongly connected graph $G$ is edge-safe if and only if $w$ is an edge-omnitig and there is an edge $e$ such that $w$ is a subwalk of every cycle through $e$ (Obscura Acosta, Mäkinen and Tomescu 2018, Theorem 4). All edge-safe walks can be reported in $O(m^2 n)$ time (Theorem 14).

## Depends on

- [Omnitig](../../omnitigs-and-safe-walks-in-genome-assembly/is-omnitig.md)
- [Node-safe walks for metagenomic reconstructions](node-safe-walks-for-metagenomic-reconstructions.md)

## Expansion

Let $S(G)$ subdivide every edge $(u,v)$ by a new node $x_{uv}$ with a single in-neighbour $u$ and a single out-neighbour $v$. Edge-covering reconstructions of $G$ correspond bijectively to node-covering reconstructions of $S(G)$, so $w$ is edge-safe in $G$ iff its subdivision $S(w)$ is node-safe in $S(G)$. In $S(G)$ the second node-omnitig condition holds automatically along subdivided edges, the first reduces to the edge-omnitig condition in $G$, and a certificate node $x_{uv}$ corresponds to a certificate edge $(u,v)$. The node-safe characterization then transfers.

## Sources

- N. Obscura Acosta, V. Mäkinen and A. I. Tomescu, *A safe and complete algorithm for metagenomic assembly*, Algorithms for Molecular Biology 13 (2018), 3, Definition 4, Theorem 4 and Theorem 14. <https://doi.org/10.1186/s13015-018-0122-7> (PMCID: PMC5802251)
