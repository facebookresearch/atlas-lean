# The stable paths problem

Let $G = (V, E)$ be a simple undirected graph with $V = \{0, 1, \dots, n\}$, where node $0$ is the *origin*, and let $\mathrm{peers}(u) = \{w : \{u, w\} \in E\}$. A *path* is either the empty path $\epsilon$ or a sequence of nodes $(v_k v_{k-1} \dots v_0)$, $k \ge 0$, with $\{v_i, v_{i-1}\} \in E$; for a path $P$ starting at $v$ and an edge $\{u, v\}$, $(u\,v)P$ is the path from $u$ that traverses the edge and then follows $P$. For each node $v$, $\mathcal P^v$ is a set of *permitted paths* from $v$ to the origin, and $\lambda^v$ is a nonnegative integer *ranking function* on $\mathcal P^v$; $P_2$ is preferred over $P_1$ when $\lambda^v(P_1) < \lambda^v(P_2)$. An *instance* $S = (G, \mathcal P, \Lambda)$ of the stable paths problem satisfies $\mathcal P^0 = \{(0)\}$ and, for every $v \ne 0$:

1. $\epsilon \in \mathcal P^v$ and $\lambda^v(\epsilon) = 0 < \lambda^v(P)$ for $P \ne \epsilon$;
2. (strictness) if $P_1 \ne P_2$ have $\lambda^v(P_1) = \lambda^v(P_2)$, then $P_1 = (v\,u)P'_1$ and $P_2 = (v\,u)P'_2$ have the same next hop $u$;
3. (simplicity) every permitted path is simple.

A *path assignment* $\pi$ maps each node $u$ to a path $\pi(u) \in \mathcal P^u$, with $\pi(0) = (0)$. The *choices* of $u \ne 0$ are $\mathrm{choices}(\pi, u) = \{(u\,v)\pi(v) : \{u, v\} \in E\} \cap \mathcal P^u$, and for a set $W$ of permitted paths with distinct next hops, $\mathrm{best}(W, u)$ is the path of $W$ of maximal rank ($\epsilon$ if $W$ is empty). The assignment $\pi$ is *stable* if $\pi(u) = \mathrm{best}(\mathrm{choices}(\pi, u), u)$ at every node $u$; a stable assignment is a *solution*, and $S$ is *solvable* if it has one. If $\pi$ is stable and $\pi(u) = (u\,w)P$ then $\pi(w) = P$, so the nonempty paths of a solution form a tree rooted at the origin. Shortest-path routing is the case in which ranks decrease with path length.

## Sources

- T. G. Griffin, F. B. Shepherd and G. Wilfong, "The stable paths problem and interdomain routing", *IEEE/ACM Transactions on Networking* 10(2):232–243, 2002, Section III (the definitions, the conditions on instances, path assignments, choices, best paths, stability and solvability, and Fig. 1).
