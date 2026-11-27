# Weighted total cophenetic index of a phylogenetic network

**Setting.** Let $N$ be a rooted phylogenetic network on $n$ leaves with root $\rho_N$. A vertex is *relevant* if it has more than one child after contracting the non-trivial blocks hanging below it, and $\mathring V_N$ is the set of relevant vertices. For a non-trivial block $B$ (a biconnected component with a cycle) with root $\rho_B$, let $\kappa_v$ be the number of vertices of $B$ below or equal to $v$ and define the block weight

$$\omega(B) = \sum_{v \in V(B) \setminus \{\rho_B\}} \binom{\kappa_v}{2}.$$

Fix $0 \le \epsilon \le 2$. Each vertex $v$ gets weight $\phi(v) = 1$ if $v$ roots no non-trivial block and $\phi(v) = \epsilon + \sum_{B : \rho_B = v} \omega(B)$ otherwise.

**Definition.** The weighted partial cophenetic index and the weighted total cophenetic index are

$$\Phi^*(N) = \sum_{v \in \mathring V_N \setminus \{\rho_N\}} \phi(v) \binom{|L_N(v)|}{2}, \qquad \Phi^{**}(N) = \Phi^*(N) + \phi(\rho_N)\binom{n}{2},$$

where $L_N(v)$ is the set of leaves below $v$. On trees $\Phi^{**}(T) - \binom{n}{2}$ is the classical total cophenetic index.

**Properties.**
1. *Block weights.* For a block $B$ with $m$ vertices, $m - 2 \le \omega(B) \le \binom{m}{3}$; the lower bound is attained exactly by lanterns and the upper exactly by crescents (a Hamiltonian path from $\rho_B$ to the hybrid plus a shortcut). In binary level-1 networks $\omega(B) \ge \binom{\lceil m/2\rceil + 1}{3} + \binom{\lfloor m/2 \rfloor + 1}{3}$, attained exactly by full-moon blocks (two internally disjoint paths of balanced length).
2. *Locality and recursion.* On level-1 networks $\Phi^{**}$ is local: replacing the relevant part below a vertex changes $\Phi^{**}$ only through that part and the vertex weight. If $v_1, \dots, v_k$ are the relevant neighbours of the root, then $\Phi^{**}(N) = \sum_i \Phi^{**}(\partial N(v_i)) + \phi(\rho_N)\binom{n}{2}$.
3. *Complexity.* $\Phi^{**}$ is computable in linear time on level-1 networks and in $O(|V|^2 + |V||E|)$ time in general.

## Expansion

The block weight is the classical total cophenetic index of the block with one pendant leaf added at each vertex, so $\omega$ measures the internal balance of a reticulation cycle without reference to its surroundings. Plain $\Phi$ ignores shortcuts and blocks hanging at the root, so very different networks collide. Weighting the roots of blocks by $\omega(B) + \epsilon$ separates them, and $\epsilon > 0$ separates a triangle root ($\omega = 1$) from an ordinary tree vertex. Locality follows from a decomposition of a level-1 network into relevant parts glued at relevant vertices, which also gives the dynamic program behind the linear-time algorithm.

## Sources

- Linda Knüver, Mareike Fischer, Marc Hellmuth and Kristina Wicke, "The weighted total cophenetic index: A novel balance index for phylogenetic networks", Discrete Applied Mathematics 359 (2024), 89–142, <https://doi.org/10.1016/j.dam.2024.07.037>; numbering as in arXiv:2307.08654: Definition of $\Phi^*$, $\Phi^{**}$ (Section 3), Proposition 9.9, Theorems 10.3–10.4, Propositions 11.3 and 11.5.
