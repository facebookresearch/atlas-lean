# Validity of network histories and blocking loops

**Network histories.** Nodes (genes or proteins) descend from ancestral nodes by duplications encoded in a binary *duplication forest* $F$: an internal node $u$ duplicates into children $u_L, u_R$ and then ceases to exist, and leaves are labelled Present or Absent (lost). Interaction gain and loss are recorded by *flip edges*: non-tree edges $\{u,v\}$ between forest nodes, each toggling the interaction between the lineages of $u$ and $v$. With $P_u$ the path from $u$ to its root, two Present leaves $u, v$ interact iff an odd number of flip edges join a node of $P_u$ to a node of $P_v$. The union $H$ of $F$ and the flip edges is a *network history*; it *constructs* a graph $G$ if its Present leaves are the nodes of $G$ and the implied interactions are exactly the edges of $G$.

**Validity.** $H$ is *valid* if there are creation and duplication times $t^c_u < t^d_u$ for every node (with $t^d_u = \infty$ for Present leaves and $t^d_u = t^c_v$ for each child $v$ of $u$) and a time $t_{\{u,w\}}$ for every flip edge with

$$t^c_u \le t_{\{u,w\}} < t^d_u \quad\text{and}\quad t^c_w \le t_{\{u,w\}} < t^d_w,$$

i.e. each interaction event happens while both endpoints exist.

**Blocking loops.** A *$k$-blocking loop* is a set of flip edges $\{u_i, v_i\}$, $0 \le i < k$, such that $u_{i+1}$ is an ancestor of $v_i$ in the forest for every $i$ (indices modulo $k$).

**Proposition.** A network history is valid if and only if it contains no blocking loop of any length $k \ge 1$.

**Minimum Flips problem.** Given a duplication forest $F$ and an extant network $G$, find a valid history constructing $G$ with the minimum number of flip edges. Whether this problem is NP-hard or polynomial in general is open; avoiding only 1- and 2-blocking loops can be done optimally in polynomial time, which gives a fast heuristic.

## Expansion

*Necessity.* Along a $k$-blocking loop the constraints chain as $t^d_{u_0} > t_{\{u_0,v_0\}} \ge t^c_{v_0} \ge t^d_{u_1} > t_{\{u_1,v_1\}} \ge \dots \ge t^c_{v_{k-1}} \ge t^d_{u_0}$, because the creation time of $v_i$ is at least the duplication time of its ancestor $u_{i+1}$; this is a contradiction. *Sufficiency.* Assign times by depth-first search along tree edges: the root gets $t^c = 0$, and before recursing into the children of $u$ set $t^d_u = \max\{\max_v t_{\{u,v\}} + 1,\ t^c_u + 1\}$ and give both children creation time $t^d_u$. A node with a flip edge to a not-yet-timed partner is deferred to a queue $Q$ and processed in a later round. If some round made no progress, every $u \in Q$ would have a flip edge to an untimed $v$ whose untimed ancestor lies in $Q$; following these links must revisit a node of the finite set $Q$, producing a blocking loop. Hence without blocking loops the procedure terminates with times satisfying all constraints.

## Sources

- R. Patro, E. Sefer, J. Malin, G. Marçais, S. Navlakha, C. Kingsford, "Parsimonious reconstruction of network evolution", Algorithms for Molecular Biology 7 (2012) 25, Methods (Eqs. (1)–(3), Proposition 1 and Problem 1), <https://doi.org/10.1186/1748-7188-7-25>, PMCID PMC3492119.
