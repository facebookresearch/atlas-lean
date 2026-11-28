# MSC graphs

A message sequence chart describes one scenario of message exchanges among processes, and an MSC graph combines finitely many charts along the paths of a graph; it is bounded when every cycle's communication is strongly connected.

**Message sequence charts.** Fix processes $P_1, \dots, P_n$ and a message alphabet $\Sigma$. An MSC $M$ has a finite set of events partitioned into sends and receives, a map $p$ assigning each event to a process, a bijection $f$ from sends to receives, labels $\mathrm{send}(i, j, a)$ and $\mathrm{receive}(i, j, a)$ consistent with $p$ and $f$, and a total order $\leq_i$ on the events of each process $P_i$, such that the transitive closure of $\bigcup_i \leq_i \cup \{(s, f(s))\}$ is a partial order. MSCs satisfy the FIFO condition: two messages from $P_i$ to $P_j$ are received in the order they were sent. An MSC is identified with the set of its linearizations, words over the event labels.

**MSC graphs.** An MSC graph $G$ is a directed graph with an initial vertex, a set of terminal vertices and a labeling $\mu$ of vertices by MSCs. Its language $L(G)$ consists of the MSCs $\mu(v_0) \cdot \mu(v_1) \cdots \mu(v_k)$ for paths from the initial vertex to a terminal vertex, where $\cdot$ pastes MSCs process by process. $G$ is *bounded* if for every cycle $\rho$ of $G$ the communication graph of $\rho$ (an arc from $P_i$ to $P_j$ when $P_i$ sends to $P_j$ in some MSC on $\rho$), restricted to the processes active on $\rho$, is strongly connected.

## Depends on

None.

## Proof depends on

None.

## Expansion

For bounded MSC graphs the linearizations of $L(G)$ form a regular language, so model checking LTL properties of $L(G)$ is PSPACE-complete for bounded graphs; it is undecidable for general MSC graphs.

## Sources

- Rajeev Alur, Kousha Etessami and Mihalis Yannakakis, "Realizability and verification of MSC graphs", *Theoretical Computer Science* 331(1):97–114, 2005, doi:10.1016/j.tcs.2004.09.034; read in the authors' open-access copy at <https://www.cis.upenn.edu/~alur/Icalp01.pdf>, which carries the journal text: Sections 2.1 and 2.2 (MSCs, MSC graphs and boundedness) of that copy.
