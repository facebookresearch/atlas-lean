# Generalized arc consistency of the global cardinality constraint by flows

A global cardinality constraint with fixed quota intervals has a solution iff its value network has a feasible flow; given one integral feasible flow, a value is unsupported exactly when its arc carries no flow and its endpoints lie in different strongly connected components of the residual graph (Régin, 1996, in the fixed-demand form of van Hoeve and Katriel).

Let $C=\mathrm{GCC}(X,(l_i),(u_i))$ be a [global cardinality constraint](global-cardinality-constraint.md) on $k\ge1$ variables over the fixed value set $V$ of size $d\ge1$, with fixed integer quotas, and let $G(C)$ be its value network (arcs $s\to x_j$ with bounds $[1,1]$, $x_j\to a$ with bounds $[0,1]$ for $a\in D_j$, $a_i\to t$ with bounds $[l_i,u_i]$). Let $m=\sum_j|D_j|$. Every feasible flow of $G(C)$ is an $s$–$t$ flow of value $k$.

**Theorem.**

1. $C$ has an allowed tuple iff $G(C)$ has a feasible flow, and then it has an integral one.
2. Let $f$ be an integral feasible flow of $G(C)$ and $G(C)_f$ its residual graph (an arc $(u,v)$ where $f$ is below the upper bound, a reverse arc $(v,u)$ where $f$ is above the lower bound). A value $a\in D_j$ has a support on $C$ iff $f(x_j,a)=1$ or $x_j$ and $a$ are strongly connected in $G(C)_f$.
3. Hence, given $f$, [generalized arc consistency](../generalized-arc-consistency.md) is enforced by one strongly connected components computation, in time linear in the size of $G(C)$, that is $O(m+k+d)$.

Régin computes the initial flow by augmenting paths and states the cost of GAC on one constraint as $O(k^2d)$, for an input in which domains are listed explicitly and quotas are integers that may be replaced by $\min(u_i,k)$ without changing the constraint. Quimper, López-Ortiz, van Beek and Golynski lowered the cost of GAC to $O(k^{1.5}d)$.

## Depends on

- [Global cardinality constraint and its value network](global-cardinality-constraint.md): the constraint, the network and the tuple–flow bijection.
- [Generalized arc consistency](../generalized-arc-consistency.md): supports and GAC.
- [Strongly connected vertices](../../../../ComputerScience/graph-algorithms/traversal-and-connectivity/strongly-connected-components/strongly-connected.md): the relation used in item 2.

## Proof depends on

- [Flows with bounds and supplies by maximum flow](../../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/circulations-with-bounds-by-maximum-flow.md): a network with bounds has a feasible flow iff an auxiliary maximum flow saturates its source arcs, and then an integral one; used for item 1.
- [Changing the flow on a unit arc of a fixed-value flow](../../../graph-algorithms/spanning-trees-flows-matchings/fixed-value-flow-rerouting/rerouting-a-fixed-value-flow.md): for an unused variable–value arc (bounds $[0,1]$, flow 0), some flow of the same value $k$ uses it iff its endpoints are strongly connected in the residual graph.
- [Topological sort and Kosaraju SCC in O(n + m) word-RAM time](../../../../ComputerScience/graph-algorithms/traversal-and-connectivity/depth-first-search-applications-on-the-word-ram/linear-time-dfs-word-ram.md): its item (iv) computes the strongly connected components of the residual graph in item 3.
- [Linear bound on the cost of BFS with parents](../../../../ComputerScience/graph-algorithms/traversal-and-connectivity/breadth-first-search/bfs-with-parents-time-le.md): each augmenting step of the cost obligations below is one search in the residual graph.

## Expansion

*Item 1.* By the tuple–flow bijection, solutions correspond to integral feasible flows; integral bounds give an integral feasible flow whenever a feasible one exists.

*Item 2* is van Hoeve and Katriel's Corollary 8 (GAC iff every variable–value arc belongs to some integral feasible flow) with their Theorem 9. For an arc $(x_j,a)$ with $f(x_j,a)=0$, which has bounds $[0,1]$, the unit-arc theorem (item 1) says that some integral flow of value $k$ uses it iff $x_j$ and $a$ are strongly connected in $G(C)_f$; if $f(x_j,a)=1$ the value is supported by $f$ itself.

Régin's 1996 paper states the corresponding Corollary 2 in his own network, which orients the arcs from $s$ through values to variables and to $t$, and carries a return arc $(t,s)$ with bounds $[0,\infty)$. With that unfixed return arc in the residual graph, a cycle through its reverse can wrongly certify a support: for $x_1\in\{a,b\}$, $x_2\in\{a\}$ and quotas $[0,1]$ the only solution is $(b,a)$, yet $a\to x_1\to b\to s\to t\to x_2\to a$ is a residual cycle there. In the fixed-demand network above, $x_1$ and $a$ are not strongly connected.

*Item 3.* The network has $k+d+2$ vertices and $m+k+d$ arcs, so its residual graph has $k+d+2$ vertices and at most $2(m+k+d)$ arcs (parallel arcs allowed). Built in compressed sparse row form in $O(m+k+d)$ instructions, its strongly connected components are computed in $O(m+k+d)$ word-RAM instructions by the linked linear-time algorithm (Régin uses Tarjan's; any linear-time algorithm serves), and comparing the component indices of the two endpoints of each variable–value arc takes $O(m)$ more. With $k\ge1$ and $d\ge1$ the size is positive.

*Costs (obligations not expanded here).* Régin's Corollary 1, in his network with the return arc $(t,s)$. Reject at once if $\sum_i l_i>k$; replace each $u_i$ by $\min(u_i,k)$, and cap the return arc, declared $[0,\infty)$, at $k$, which removes no flow because all flow into $t$ arrives on the $k$ variable-to-sink arcs of capacity 1. Then every bound and flow value is at most $k$. Régin's augmentation step, for a *closing arc* $(y,x)$ with $f(y,x)<c(y,x)$: find a simple path $p$ from $x$ to $y$ in the residual graph that does not use the reverse residual copy $(x,y)$ of the closing arc, and add $v=\min(\mathrm{res}(p),c(y,x)-f(y,x))$ to the closing arc and to the forward arcs of $p$, subtracting it on the arcs traversed backward; this keeps every bound, and an arc at its lower bound has no backward residual copy, so lower bounds already met stay met.

*Repair phase.* Starting from the zero flow, while some arc $(y,x)$ has flow below its lower bound, use it as the closing arc; each augmentation raises its flow by at least one unit, since bounds are integral. If for some such arc no path exists, no feasible flow exists and $C$ has no solution: for example, two variables with domains $\{a\},\{a\}$ and quotas $a:[0,2]$, $b:[1,1]$ pass the test $\sum_i l_i\le k$, but no path can bring flow to $b$. Otherwise at most $\sum_i l_i\le k$ augmentations give a feasible flow.

*Maximum-flow phase*, kept separate. Use the capped return arc $(t,s)$ as the closing arc, so each search is for a path from $s$ to $t$ that avoids the residual copy $(s,t)$ of the return arc. Without that exclusion the search can return the one-arc path $s\to t$, and closing it with $(t,s)$ cancels the update: with two variables of domain $\{a\}$, quota $a:[1,2]$ and one unit already routed through the first variable, the excluded search finds $s\to a\to x_2\to t$ and raises the value to 2. Each augmentation raises $f(t,s)$ by at least one, so there are at most $k$; $C$ has a solution iff the final value is $k$.

Each augmentation is one search in a residual graph with $O(m+k+d)$ vertices and arcs (the excluded copy omitted), $O(m+k+d)$ by the [BFS cost bound](../../../../ComputerScience/graph-algorithms/traversal-and-connectivity/breadth-first-search/bfs-with-parents-time-le.md), plus path reconstruction and the update along the path and closing arc, linear as well. This assumes indexed vertices and arc records and a word size large enough for those indices and for flow values up to $k$, as after the normalization above (reading larger quota encodings is charged separately), and gives $O(k(m+k+d))$, which is $O(k^2d)$ since $m\le kd$. His Corollary 4 repairs a flow after deletions along a deletion-only branch.

## Sources

- W.-J. van Hoeve and I. Katriel, "Global constraints", in F. Rossi, P. van Beek and T. Walsh (eds.), *Handbook of Constraint Programming*, Elsevier (2006), chapter 6, 169–208, doi:10.1016/S1574-6526(06)80010-6; author copy [https://www.andrew.cmu.edu/user/vanhoeve/papers/chapter.pdf](https://www.andrew.cmu.edu/user/vanhoeve/papers/chapter.pdf). The fixed-demand network, Theorem 7, Corollary 8, Theorem 9, Fig. 7.4 and the complexity remarks of §7.3.2 (section and theorem numbers of the author copy).
- J.-C. Régin, "Generalized arc consistency for global cardinality constraint", *Proceedings of the Thirteenth National Conference on Artificial Intelligence (AAAI-96)*, AAAI Press (1996), 209–215, [https://aaai.org/papers/031-AAAI96-031-generalized-arc-consistency-for-global-cardinality-constraint/](https://aaai.org/papers/031-AAAI96-031-generalized-arc-consistency-for-global-cardinality-constraint/). Theorem 1 (flow integrality), Proposition 2, Theorems 2–4 and Corollaries 1–4 with proofs, and the conclusion's $O(|X(C)|^2|D(C)|)$ bound, pp. 211–214.
- C.-G. Quimper, A. López-Ortiz, P. van Beek and A. Golynski, "Improved algorithms for the global cardinality constraint", *Principles and Practice of Constraint Programming – CP 2004*, Lecture Notes in Computer Science 3258 (2004), 542–556, doi:10.1007/978-3-540-30201-8_40. The $O(|X|^{1.5}|D|)$ domain consistency algorithm, abstract and §3.
- R. Tarjan, "Depth-first search and linear graph algorithms", *SIAM Journal on Computing* 1(2) (1972), 146–160, doi:10.1137/0201010. Linear-time strongly connected components.
