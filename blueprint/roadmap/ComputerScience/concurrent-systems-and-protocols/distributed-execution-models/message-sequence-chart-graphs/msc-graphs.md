# MSC graphs

A message sequence chart describes one scenario of message exchanges among processes, and an MSC graph combines finitely many charts along the walks of a finite graph; it is bounded when every cycle's communication is strongly connected.

**Message sequence charts.** Fix processes $P_1, \dots, P_n$ and a message alphabet $\Sigma$. The event labels are $\mathrm{send}(i, j, a)$ ($P_i$ sends $a$ to $P_j$) and $\mathrm{receive}(i, j, a)$ ($P_j$ receives $a$ from $P_i$). An MSC $M$ has a finite set of events partitioned into sends and receives, a map $p$ assigning each event to a process, a bijection $f$ from sends to receives, a labeling of events and, for each process $P_i$, a total order $\leq_i$ on its events. Labels are consistent: if a send $s$ is labeled $\mathrm{send}(i, j, a)$, then $p(s) = i$, $f(s)$ is labeled $\mathrm{receive}(i, j, a)$ and $p(f(s)) = j$. The transitive closure of $\bigcup_i \leq_i \cup \{(s, f(s))\}$ must be a partial order. MSCs satisfy the FIFO condition: two messages from $P_i$ to $P_j$ are received in the order they were sent. A *linearization* of $M$ is the word of labels of a linear extension of this partial order, and an MSC is identified with the set of its linearizations.

**MSC graphs.** An MSC graph $G$ is a directed graph with a finite set of vertices, an initial vertex, a set of terminal vertices and a labeling $\mu$ of vertices by MSCs. An *accepting path* is a finite walk $v_0 v_1 \cdots v_k$ from the initial vertex to a terminal vertex; vertices may repeat. The language $L(G)$ consists of the MSCs $\mu(v_0) \cdot \mu(v_1) \cdots \mu(v_k)$ for the accepting paths, where $\cdot$ pastes MSCs process by process. For a set $U$ of vertices, the *communication graph* $H_U$ has the processes as vertices and an arc from $P_i$ to $P_j$ when $P_i$ sends to $P_j$ in $\mu(v)$ for some $v \in U$; the *active processes* of $U$ are those that send or receive in some $\mu(v)$, $v \in U$. $G$ is *bounded* if, for every cycle $\rho$ of $G$ (a closed path, in which vertices may repeat), the subgraph of $H_\rho$ induced by the active processes of $\rho$ is strongly connected.

## Depends on

- [Linear extensions of a finite poset](../../../../Combinatorics/partially-ordered-sets/linear-extensions-of-posets/linear-extensions.md)
- [Walks of a given length](../../../graph-algorithms/traversal-and-connectivity/adjacency-list/walk.md)
- [Strongly connected vertices](../../../graph-algorithms/traversal-and-connectivity/strongly-connected-components/strongly-connected.md)

## Proof depends on

None.

## Expansion

Finiteness of the vertex set matters. Take an infinite one-way ray with every vertex terminal and every vertex labeled by the chart of a single message from $P_1$ to $P_2$. This graph has no cycle, yet its linearizations intersected with $\mathrm{send}^*\mathrm{receive}^*$ are the words $\mathrm{send}^n \mathrm{receive}^n$, $n \ge 1$, which form no regular language. For a single vertex with a self-loop labeled by a one-message chart, $L(G)$ is not regular either, because repeated walks through the loop let sends run arbitrarily far ahead of receives (Section 2.2 of the source).

For bounded MSC graphs the set of linearizations of $L(G)$ is regular, recognized by a nondeterministic automaton exponential in the size of $G$ (Section 2.2 of the source, citing Alur and Yannakakis). Separately, model checking LTL properties of $L(G)$ is undecidable for general MSC graphs and PSPACE-complete for bounded ones (abstract and Section 1 of the source).

## Sources

- Rajeev Alur, Kousha Etessami and Mihalis Yannakakis, "Realizability and verification of MSC graphs", *Theoretical Computer Science* 331(1):97–114, 2005, doi:10.1016/j.tcs.2004.09.034; read in the authors' manuscript of the journal version at <https://www.cis.upenn.edu/~alur/Icalp01.pdf>: the abstract and Section 1 (the LTL model-checking bounds), and Sections 2.1 and 2.2 (MSCs, linearizations, MSC graphs, accepting paths and boundedness) of that copy.
