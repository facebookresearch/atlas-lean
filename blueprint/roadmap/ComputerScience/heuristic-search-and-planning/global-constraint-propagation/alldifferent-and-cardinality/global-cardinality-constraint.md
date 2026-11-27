# Global cardinality constraint and its value network

A global cardinality constraint bounds, for every value, how many of its variables take that value; its value network is a flow network with lower and upper bounds on its arcs in which the integral feasible flows correspond exactly to the solutions.

Let $X=(x_1,\dots,x_k)$, $k\ge1$, be distinct variables with finite domains $D_1,\dots,D_k$, all contained in a fixed finite set of values $V=\{a_1,\dots,a_d\}$, and give each value $a_i$ fixed integers $0\le l_i\le u_i$. For a tuple $P$ write $\#(a,P)$ for the number of positions of $P$ holding $a$. The value set and the quotas are part of the constraint and stay fixed while the domains shrink; a value with $l_i>0$ that disappears from every domain is kept (the constraint then fails) rather than dropped together with its quota.

- The **global cardinality constraint** $\mathrm{GCC}(X,(l_i),(u_i))$ allows exactly the tuples $P\in D_1\times\dots\times D_k$ with $l_i\le\#(a_i,P)\le u_i$ for every $i$. With all $l_i=0$ and $u_i=1$ it is [ALLDIFFERENT](alldifferent-constraint.md).
- The **value network** $G(C)$ has vertices $s$, $t$, one vertex per variable and one per value (all distinct), and the arcs $(s,x_j)$ with bounds $[1,1]$, $(x_j,a_i)$ with bounds $[0,1]$ whenever $a_i\in D_j$ (the value-graph edges oriented from variables to values), and $(a_i,t)$ with bounds $[l_i,u_i]$.
- A **feasible flow** of $G(C)$ is a function $f$ on its arcs with $\mathrm{lower}(e)\le f(e)\le\mathrm{upper}(e)$ on every arc and conservation at every vertex other than $s$ and $t$. Since all arcs leaving $s$ are fixed to 1, every feasible flow sends exactly $k$ units from $s$ to $t$; equivalently it is a [flow with bounds and prescribed net inflows](../../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/circulations-with-bounds-by-maximum-flow.md) $b_s=-k$, $b_t=k$ and $b_v=0$ elsewhere.

The map sending an allowed tuple $P$ to the flow with $f(s,x_j)=1$, $f(x_j,a)=1$ iff $P_j=a$ and $f(a_i,t)=\#(a_i,P)$ is a bijection between allowed tuples and integral feasible flows of $G(C)$.

## Depends on

- [The ALLDIFFERENT constraint and its value graph](alldifferent-constraint.md): the value graph, and the special case $l_i=0$, $u_i=1$.
- [Flows with bounds and supplies by maximum flow](../../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/circulations-with-bounds-by-maximum-flow.md): flows with lower and upper arc bounds and prescribed net inflows.

## Proof depends on

None.

## Expansion

Given an allowed tuple, the flow defined above is conserved at each variable (one unit in, one out) and at each value ($\#(a_i,P)$ units in and out), and respects the bounds because $l_i\le\#(a_i,P)\le u_i$. Conversely, in an integral feasible flow each variable receives exactly one unit from $s$ and so sends one unit along exactly one arc $(x_j,a)$, which exists only when $a\in D_j$; the chosen values form a tuple $P$, and conservation at $a_i$ gives $\#(a_i,P)=f(a_i,t)\in[l_i,u_i]$. This is Theorem 7 of van Hoeve and Katriel's handbook chapter, with this orientation.

Régin's original value network orients the same arcs the other way (from $s$ to the values with bounds $[l_i,u_i]$, from values to variables, from variables to $t$ with bounds $[0,1]$) and adds a return arc $(t,s)$ with bounds $[0,\infty)$; allowed tuples then correspond to integral flows in which the return arc carries $k$ (his Propositions 1–2), and the constraint is satisfiable iff the maximum flow value is $k$. For the residual-graph test of supports the fixed-demand network above is the one to use, since an unfixed return arc creates spurious residual cycles.

## Sources

- W.-J. van Hoeve and I. Katriel, "Global constraints", in F. Rossi, P. van Beek and T. Walsh (eds.), *Handbook of Constraint Programming*, Elsevier (2006), chapter 6, 169–208, doi:10.1016/S1574-6526(06)80010-6; author copy [https://www.andrew.cmu.edu/user/vanhoeve/papers/chapter.pdf](https://www.andrew.cmu.edu/user/vanhoeve/papers/chapter.pdf). Definition 2 (global cardinality constraint), flows with demands in §7.1.2, and the augmented value graph with Theorem 7 and its proof and Fig. 7.4 in §7.3.2 (section and theorem numbers of the author copy).
- J.-C. Régin, "Generalized arc consistency for global cardinality constraint", *Proceedings of the Thirteenth National Conference on Artificial Intelligence (AAAI-96)*, AAAI Press (1996), 209–215, [https://aaai.org/papers/031-AAAI96-031-generalized-arc-consistency-for-global-cardinality-constraint/](https://aaai.org/papers/031-AAAI96-031-generalized-arc-consistency-for-global-cardinality-constraint/). Definition 1 (gcc), Definition 2 (value network), Propositions 1–2 and their proofs, pp. 210–212.
- C. Bessiere, E. Hebrard, B. Hnich and T. Walsh, "The complexity of reasoning with global constraints", *Constraints* 12(2) (2007), 239–259, doi:10.1007/s10601-006-9007-3. ALLDIFFERENT as the gcc with intervals $[0,1]$, §4.4 of arXiv:0903.1139v1, [https://arxiv.org/abs/0903.1139v1](https://arxiv.org/abs/0903.1139v1).
