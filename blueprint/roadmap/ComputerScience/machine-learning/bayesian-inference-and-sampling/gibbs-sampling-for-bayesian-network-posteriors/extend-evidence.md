# Extending evidence to a full assignment

Let $E \subseteq \{0, \dots, n-1\}$ be a set of evidence nodes, $e : \{0,\dots,n-1\} \to \alpha$ an assignment supplying the evidence values, and $z$ an assignment of values to the nodes outside $E$. The extended assignment $(e, z) : \{0,\dots,n-1\} \to \alpha$ is

$$(e, z)_i = \begin{cases} e_i & i \in E, \\ z_i & i \notin E. \end{cases}$$
