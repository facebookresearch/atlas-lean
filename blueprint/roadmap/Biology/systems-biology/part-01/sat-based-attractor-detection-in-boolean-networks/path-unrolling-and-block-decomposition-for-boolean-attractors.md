# Path unrolling and block decomposition for Boolean attractors

**Setting.** A synchronous Boolean network on nodes $v_1,\dots,v_n$ has state $s(k) \in \{0,1\}^n$ and update $s_i(k+1) = f_i\big(s_{j}(k) : v_j \in \mathrm{pred}(v_i)\big)$, so the state transition graph (STG) is a functional graph: every state has exactly one successor, and every trajectory ends in an attractor (a cycle of the STG). The transition relation is the Boolean formula $T(s,s') = \bigwedge_i\big(s'_i \leftrightarrow f_i(s)\big)$ and a path of length $k$ is $T(s^0,s^1)\wedge\cdots\wedge T(s^{k-1},s^k)$, a formula that a SAT solver can satisfy.

**Theorem.** In the STG of a synchronous Boolean network, if a path contains a state of an attractor, then the last state of the path belongs to that attractor. Consequently, a satisfying assignment of an unrolled path with $s^k = s^j$ for some $j < k$ exhibits an attractor $\{s^j,\dots,s^{k-1}\}$, and adding the clause excluding its states lets the solver search for the next attractor.

**Block decomposition.** Contract the strongly connected components (SCCs) of the wiring graph to obtain a DAG; the **gradient** of a node is the length of the longest path to it from a root of this DAG. A **block** is a set of nodes with consecutive gradients, and its **decision nodes** are the outside nodes with an edge into the block. The state of a block is determined by its own state and those of its decision nodes, so every attractor of the network is a combination of **local attractors**: those of the root block, then those of each subsequent block driven by the periodic sequences that the earlier blocks impose on its decision nodes. Each block has at least as many local attractors as the network has attractors; unsatisfiable continuations are discarded and multiple continuations branch.

## Expansion

Since successors are unique and the successor of an attractor state stays in the attractor, once a path enters an attractor it can never leave, which proves the theorem by contradiction. The SAT encoding replaces explicit enumeration by bounded model checking with growing unrolling depth. The decomposition exploits that influence flows only downward along the SCC DAG: upstream components evolve autonomously, so their attractors can be computed first and fed as periodic inputs to downstream blocks, which shrinks the state space each SAT call explores and allows independent branches to be processed in parallel.

## Sources

- W. Guo, G. Yang, W. Wu, L. He, M. Sun, "A parallel attractor finding algorithm based on Boolean satisfiability for genetic regulatory networks", PLoS ONE 9(4) (2014) e94258, Methods (Boolean network model; network partition and gradient calculation), Eqs (1)–(4), Theorem 1 and Definitions 1–4, <https://doi.org/10.1371/journal.pone.0094258>, PMCID PMC3981794.
