# Cut edges and degree-two vertices from a two-terminal reliability matrix

Let $G = (V,E)$ be the unknown graph of direct protein interactions. In a pull-down, each edge survives independently with probability $\hat p \in (0,1)$, and the abundance of prey $v$ recovered with bait $u$ is proportional to the **connectivity**

$$P_G(u,v) = \Pr\big[\text{$u$ and $v$ are joined by a path of surviving edges}\big],$$

the two-terminal reliability of $G$. Computing $P_G$ exactly is #P-complete. The inverse problem asks for $G$ with $P_G = M$ for an observed matrix $M$ (exactly, or for as many pairs as possible within tolerance $\delta$).

**Composition rules.** If $G$ is obtained by gluing $G_1$ and $G_2$ at a single vertex $c$, then $P_G(s,t) = P_{G_1}(s,c)\,P_{G_2}(c,t)$ for $s \in V_1\setminus\{c\}$, $t \in V_2\setminus\{c\}$ (series); if they are glued at two vertices $s, t$, then $P_G(s,t) = P_{G_1}(s,t) + P_{G_2}(s,t) - P_{G_1}(s,t)P_{G_2}(s,t)$ (parallel).

**Theorem 1 (cut edges).** $\{u,v\}$ is a cut edge of a connected $G$ if and only if (i) $P_G(u,v) = \hat p$, and (ii) with $V_u = \{x : P_G(x,u) \ge P_G(x,v)\}$ and $V_v = V \setminus V_u$,

$$P_G(s,t) = P_G(s,u)\,\hat p\,P_G(v,t) \qquad \text{for all } s \in V_u,\ t \in V_v .$$

Each pair is tested in $O(|V|^2)$ time; removing a cut edge splits the problem into independent subproblems on $V_u$ and $V_v$, and a tree is recovered exactly by recursion.

**Theorem 2 (degree-two vertices).** If $s$ has exactly two neighbours $u, v$, then (i) $P_G(s,t) < 2\hat p - \hat p^2$ for all $t \ne s$; (ii) $P_G(s,t) < P_G(s,u) = P_G(s,v)$ for all $t \notin \{s,u,v\}$; and (iii) $P_G(s,t) < \max\{P_G(u,t), P_G(v,t)\}$ for all $t \notin \{s,u,v\}$.

## Depends on

- [Bridge test for an edge set](../../../../ComputerScience/greedy-algorithms-and-matroids/graphic-matroid/bridge-in.md)

## Expansion

For Theorem 1, necessity follows from the series rule. Conversely, if $\{u,v\}$ satisfied (i)–(ii) but were not a cut edge, some other edge $\{s,t\}$ would join $V_u$ and $V_v$, forcing $P_G(s,t) \ge \hat p$, whereas (ii) gives $P_G(s,t) = P_G(s,u)\hat p P_G(v,t) < \hat p$. For Theorem 2(i), $s$ is isolated with probability $(1-\hat p)^2$; for (ii), applying the parallel and series rules to the two edges at $s$ gives the same expression for $P_G(s,u)$ and $P_G(s,v)$, and comparing equal-size subgraphs shows that any other target is reached with strictly smaller probability. These tests resolve most low-degree proteins of sparse interaction networks; dense regions and the remainder are then fitted by clique detection and a cut-guided genetic algorithm.

## Sources

- E. D. Kim, A. Sabharwal, A. R. Vetta and M. Blanchette, "Predicting direct protein interactions from affinity purification mass spectrometry data", Algorithms for Molecular Biology 5 (2010), 34, Problem formulation, Theorems 1–2, Facts 1–2 and Appendix proofs, <https://doi.org/10.1186/1748-7188-5-34>, PMCID: PMC2991326.
