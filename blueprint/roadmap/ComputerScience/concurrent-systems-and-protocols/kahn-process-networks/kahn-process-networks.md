# Kahn process networks

A *parallel program schema* is a directed graph with labelled nodes (processes) and edges (communication lines), together with incoming edges that have only an end vertex (input lines) and outgoing edges that have only an origin vertex (output lines). Each line $e$ carries objects of a set $D_e$, and its *history* is an element of the [stream domain](streams-and-the-prefix-order.md) $D_e^\omega$. A node with input lines carrying $D_1, \dots, D_n$ and output lines carrying $D'_1, \dots, D'_p$ is interpreted by $p$ continuous functions $f_j : D_1^\omega \times \cdots \times D_n^\omega \to D'^\omega_j$, one per output line. A *Kahn process network* is a schema with such an interpretation. Its system of equations $\Sigma_P$ has a variable $X_e$ ranging over $D_e^\omega$ for each line $e$, an equation $X_e = i_e$ for each input line fed with the sequence $i_e$, and for each node an equation $X'_j = f_j(X_1, \dots, X_n)$ for each of its output lines, where $X_1, \dots, X_n$ are the variables of its input lines.

## Depends on

- [Streams and the prefix order](streams-and-the-prefix-order.md)
- [Streams form a complete partial order](streams-form-a-complete-partial-order.md)

## Sources

- G. Kahn, "The semantics of a simple language for parallel programming", IFIP Congress 74, 1974; retypeset version read at <https://perso.ensta.fr/~chapoutot/various/kahn_networks.pdf>, Sections 2.1 (syntax of schemata), 2.2.3 (domain of interpretation), 2.2.5 (computing stations as continuous functions) and 3 (the system of fixpoint equations $\Sigma_P$).
