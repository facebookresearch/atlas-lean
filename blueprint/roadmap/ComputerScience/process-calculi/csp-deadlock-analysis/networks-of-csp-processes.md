# Networks of CSP processes and deadlock

A *network* $V = \Vert_{i=1}^{n} (P_i, A_i)$ is the alphabetized parallel composition of CSP processes $P_1, \dots, P_n$ in which every communication of $P_i$ lies in its alphabet $A_i \subseteq \Sigma$. The standard assumptions on a network are: (A) no $P_i$ can terminate; (B) the network is statically defined as such a composition; (C) it is *triple-disjoint*: $A_i \cap A_j \cap A_k = \emptyset$ for distinct $i, j, k$; (D) it is built by parallel composition alone, with no renaming or hiding; and (E) it is *busy*: every $P_i$ is deadlock-free. Its *communication graph* has a node for each $P_i$ and an edge between $P_i$ and $P_j$ when $A_i \cap A_j \ne \emptyset$, and its *vocabulary* is $\bigcup_{i \ne j} (A_i \cap A_j)$. Under (B), $V$ is a term of the [operational semantics](../csp-semantic-models/csp-operational-semantics.md) built with its generalized parallel operator: for processes whose communications lie in $A$ and $B$, the alphabetized composition is $P \parallel_{A \cap B} Q$, so $V = (\cdots((P_1 \parallel_{A_1 \cap A_2} P_2) \parallel_{(A_1 \cup A_2) \cap A_3} P_3) \cdots) \parallel_{(A_1 \cup \cdots \cup A_{n-1}) \cap A_n} P_n$. In [the stable failures model of CSP](../csp-semantic-models/the-stable-failures-model.md), $V$ is *deadlocked* after a trace $s \in \Sigma^*$ when $(s, \Sigma)$ is a failure of $V$, and *deadlock-free* when it has no such failure.

## Depends on

- [The stable failures model of CSP](../csp-semantic-models/the-stable-failures-model.md)
- [Traces, failures and divergences of a process](../csp-semantic-models/traces-failures-and-divergences-of-a-process.md)
- [The operational semantics of CSP](../csp-semantic-models/csp-operational-semantics.md)

## Sources

- A. W. Roscoe, *The Theory and Practice of Concurrency*, Prentice Hall, 1997; revised edition 2005, author's online version, <https://www.cs.ox.ac.uk/bill.roscoe/publications/68b.pdf>, Section 13.1.1 (assumptions (A)–(E)), the communication graph and vocabulary in Section 13.1.2, and the formal definitions in Section 13.1.2 ("Formal definitions": deadlock as the failure $(s, \Sigma)$), pp. 337–346.
