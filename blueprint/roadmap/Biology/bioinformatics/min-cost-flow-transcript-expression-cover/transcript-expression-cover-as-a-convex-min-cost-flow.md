# Transcript expression cover as a convex min-cost flow

**Setting.** A splicing graph is a directed acyclic graph $G = (V, E)$ whose nodes are exon segments and whose arcs are observed splice junctions, with nonnegative coverages $\mathrm{cov}(v)$ and $\mathrm{cov}(u,v)$, a set $S$ of sources and a set $T$ of sinks. For every node and arc let $f_v, f_{uv} : [0, \infty) \to [0,\infty)$ be convex nondecreasing penalties of the absolute deviation (for instance $f(x) = x$, $f(x) = x^2$, or $f(x) = x/\mathrm{cov}$).

**Unannotated transcript expression cover (UTEC).** Find a finite tuple $\mathcal P$ of paths from $S$ to $T$ and expression levels $e(P) \ge 0$ minimizing

$$\sum_{v \in V} f_v\Big(\Big|\mathrm{cov}(v) - \sum_{P \ni v} e(P)\Big|\Big) + \sum_{(u,v) \in E} f_{uv}\Big(\Big|\mathrm{cov}(u,v) - \sum_{P \ni (u,v)} e(P)\Big|\Big).$$

The arc-only variant (UTEJC) drops the node terms. Replacing each node $v$ by an arc $(v_{\mathrm{in}}, v_{\mathrm{out}})$ with coverage $\mathrm{cov}(v)$ and penalty $f_v$, and each arc $(u,v)$ by $(u_{\mathrm{out}}, v_{\mathrm{in}})$, puts the optimal solutions of UTEC on $G$ in bijection with those of UTEJC on the new graph.

**Offset network.** For UTEJC on $G$ build a flow network $N^*$ (flows satisfy, at each node $w$, out-flow minus in-flow $= q_w$, and $0 \le x \le$ capacity):
1. keep every arc $(u,v) \in E$ with infinite capacity and cost $f_{uv}$, and add the reverse arc $(v,u)$ with capacity $\mathrm{cov}(u,v)$ and cost $f_{uv}$;
2. add a super-source $s_0$ and super-sink $t_0$, arcs $(s_0, s)$ for $s \in S$, $(t, t_0)$ for $t \in T$ and $(t_0, s_0)$, all of infinite capacity and zero cost;
3. for each $v \in V$ let $d_v = \sum_{w} \mathrm{cov}(v,w) - \sum_{u} \mathrm{cov}(u,v)$; if $d_v > 0$ add an arc $(v, t^*)$ of capacity $d_v$ and zero cost, if $d_v < 0$ add an arc $(s^*, v)$ of capacity $-d_v$ and zero cost; give all original nodes supply $0$ and set the supplies of $s^*$ and $t^*$ to $-\sum_{d_v<0} d_v$ and $-\sum_{d_v > 0} d_v$ respectively, so these arcs must be saturated.

**Lemma.** The supplies of $N^*$ sum to zero, so $N^*$ is a flow network (because $\sum_v d_v = \sum_{(u,v)\in E}\mathrm{cov}(u,v) - \sum_{(u,v)\in E}\mathrm{cov}(u,v) = 0$).

**Theorem.** Let $x^*$ be a minimum-cost flow on $N^*$ and define, for $(u,v) \in E$,

$$x_{uv} = \mathrm{cov}(u,v) + x^*_{uv} - x^*_{vu} \ \ (\ge 0).$$

Then (1) $x$ is conserved at every node of $V \setminus (S \cup T)$; (2) the total flow leaving $S$ equals the total flow entering $T$; and (3) every decomposition of $x$ into weighted source-to-sink paths is an optimal solution of UTEJC on $G$. Consequently UTEC is solvable in polynomial time by convex-cost minimum-cost flow, and a decomposition into at most $|E|$ paths can be found in $O(|V|\,|E|)$ time.

Minimizing the number of paths in a flow decomposition is NP-hard in the strong sense even on DAGs, while every flow on $G$ decomposes into at most $|E| - |V| + 2$ paths; any decomposition heuristic (for example repeatedly removing a path of maximum bottleneck) keeps optimality of the coverage fit.

## Expansion

At a minimum-cost flow, at most one of $x^*_{uv}, x^*_{vu}$ is positive: cancelling $\min(x^*_{uv}, x^*_{vu})$ on both keeps feasibility and strictly lowers the cost. Hence $x^*_{uv} - x^*_{vu}$ is the signed offset by which the explained expression departs from the measured coverage, and the capacity $\mathrm{cov}(u,v)$ of the reverse arc keeps $x_{uv} \ge 0$. The saturated arcs at $s^*, t^*$ inject exactly the coverage imbalance $d_v$ at each node, so the offsets repair conservation, which gives (1); flow through $(t_0, s_0)$ gives (2). Path systems with expressions correspond to conservative nonnegative flows on $G$ and conversely, and conservative flows on $G$ correspond to flows on $N^*$, with UTEJC cost $\sum f_{uv}(|x_{uv} - \mathrm{cov}(u,v)|) = \sum f_{uv}(x^*_{uv}) + f_{uv}(x^*_{vu})$ when only one offset is nonzero; so $x^*$ minimizes the UTEJC objective, which gives (3).

## Sources

- A. I. Tomescu, A. Kuosmanen, R. Rizzi, V. Mäkinen, "A novel min-cost flow method for estimating transcript expression with RNA-Seq", BMC Bioinformatics (2013), Methods: Problems 1 (UTEC) and 2 (UTEJC), construction of the offset network, Lemma 1 and Theorem 1, <https://doi.org/10.1186/1471-2105-14-S5-S15>, PMCID PMC3622638.
