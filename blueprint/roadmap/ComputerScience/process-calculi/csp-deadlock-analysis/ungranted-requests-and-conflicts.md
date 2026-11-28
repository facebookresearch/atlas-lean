# Ungranted requests and conflicts in CSP networks

Let $V = \Vert_{i=1}^{n} (P_i, A_i)$ be a [network](networks-of-csp-processes.md). A *state* of $V$ is a tuple $(s, X_1, \dots, X_n)$ with $s \in (\bigcup_i A_i)^*$, $(s \upharpoonright A_i, X_i)$ a failure of $P_i$ and $X_i \supseteq \Sigma \setminus \mathrm{initials}(P_i / (s \upharpoonright A_i))$; it is a *deadlock state* if $\bigcup_i A_i = \bigcup_i (A_i \cap X_i)$. In a state, $P_i$ *makes a request* to a process $P_j$ with $j \ne i$ if $A_j \cap (\Sigma \setminus X_i) \ne \emptyset$, whatever $X_j$ is: it offers an event that $P_j$ must take part in. In the composition $P \mathbin{{}_A\Vert_B} Q$ of two processes with alphabets $A$ and $B$, a state $(s, X_P, X_Q)$ is an *ungranted request* from $P$ to $Q$ with respect to a vocabulary $C \supseteq A \cap B$ if $(\Sigma \setminus X_P) \cup (\Sigma \setminus X_Q) \subseteq C$, $B \cap (\Sigma \setminus X_P) \ne \emptyset$ and $B \cap (\Sigma \setminus X_P) \subseteq X_Q$. A *conflict* is a state that is an ungranted request in both directions, and a *strong conflict* is a conflict in which, moreover, $\Sigma \setminus X_P \subseteq B$ or $\Sigma \setminus X_Q \subseteq A$: one of the two processes has its only requests to the other. $V$ is *free of conflict* (respectively *free of strong conflict*) if no pair of adjacent processes in its communication graph has a state that is a conflict (respectively a strong conflict) with respect to the vocabulary of $V$. In a deadlock state, $P_i$ has an ungranted request to $P_j$ when the corresponding state of $P_i \mathbin{{}_{A_i}\Vert_{A_j}} P_j$ is one with respect to the vocabulary of $V$.

## Depends on

- [Networks of CSP processes and deadlock](networks-of-csp-processes.md)

## Sources

- A. W. Roscoe, *The Theory and Practice of Concurrency*, Prentice Hall, 1997; revised edition 2005, author's online version, <https://www.cs.ox.ac.uk/bill.roscoe/publications/68b.pdf>, Section 13.1.2, "Formal definitions" (states, deadlock states, requests, ungranted requests, conflicts, strong conflicts, freedom from conflict), pp. 346–347.
