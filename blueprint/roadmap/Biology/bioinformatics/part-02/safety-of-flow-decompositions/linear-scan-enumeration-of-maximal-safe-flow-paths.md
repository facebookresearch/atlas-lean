# Linear-scan enumeration of maximal safe flow paths

**Setting.** Let $G$ be a flow DAG with $n$ vertices and $m$ edges, the kind of splice graph used in RNA transcript assembly. A path $P$ is safe for flow decomposition, that is, it is a subpath of positive total weight in every flow decomposition, exactly when its excess flow $f_P$ is positive. A set of safe paths is *complete* if it contains every maximal safe path.

**Theorem.**

1. (Verification.) After $O(m)$ preprocessing, the safety of any path $P$ can be decided in $O(|P|)=O(n)$ time.
2. (Enumeration.) Let $\mathcal P_f$ be any flow decomposition, which can be computed in $O(mn)$ time. All maximal safe paths of $G$ can be reported in $O(|\mathcal P_f|)=O(mn)$ total time.

**Algorithm.** Every safe path is a subpath of some path in every decomposition, so it suffices to scan each decomposition path $P\in\mathcal P_f$ with two pointers. Keep a window, a subpath of $P$, together with its excess flow. While the excess flow is positive, extend the window to the right, and when it is no longer positive, shrink it from the left. Each change updates the excess flow in $O(1)$ by the incremental rule: adding or removing an end edge $(u,v)$ shifts $f_P$ by $\mp\bigl(f_{out}(u)-f(u,v)\bigr)$ on the right and $\mp\bigl(f_{in}(v)-f(u,v)\bigr)$ on the left. A window is reported, as two indices on $P$, whenever it is safe but its right extension is not. The output is a *concise representation* $\mathcal P_c$: a minimal set of minimal-length paths containing every safe path as a subpath. Duplicates and prefix or suffix overlaps across decomposition paths are removed with an Aho–Corasick trie. The size of $\mathcal P_c$ is $\Omega(mn)$ in the worst case, but can be as small as $O(m+n)$, so beating $O(mn)$ in general requires avoiding a candidate decomposition.

## Expansion

Verification computes $f_P=\sum_if(u_i,u_{i+1})-\sum_{i\ge2}f_{out}(u_i)$ in one pass over $P$. For enumeration, a maximal safe path must be a subpath of any fixed decomposition path that carries it. Along a fixed path, safety is monotone under taking subpaths, since extending a path can only lower $f_P$. So the two-pointer window visits every maximal safe subpath, and each pointer moves $O(|P|)$ times. Summing over $\mathcal P_f$ gives $O(mn)$. On simulated RNA splice graphs the maximal safe paths keep perfect precision and give about 50% more coverage than unitig-based safe paths. On datasets with many complex graphs they beat the greedy-width heuristic by about 20% in F-score.

## Depends on

- [Excess-flow characterization of safe paths in flow decompositions](excess-flow-characterization-of-safe-paths-in-flow-decompositions.md)

## Sources

- Shahbaz Khan, Milla Kortelainen, Manuel Cáceres, Lucia Williams, Alexandru I. Tomescu, "Safety and Completeness in Flow Decompositions for RNA Assembly", arXiv:2201.10372 (2022), Section 1 (Theorems 2 and 3), Section 4 (verification and enumeration algorithms, concise representation), <https://doi.org/10.48550/arXiv.2201.10372>.
