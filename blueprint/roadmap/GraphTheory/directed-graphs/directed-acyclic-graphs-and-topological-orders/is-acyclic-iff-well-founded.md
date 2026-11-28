# Finite acyclic digraphs are those with well-founded adjacency

Let $G$ be a digraph on a finite vertex type $V$. Then $G$ is acyclic (no vertex reaches itself by a directed walk of positive length) if and only if its adjacency relation is well-founded: every nonempty set $S$ of vertices contains a vertex $m$ such that no $u \in S$ has an edge $u \to m$.

Read with $u \to v$ meaning that $u$ is a parent of $v$, this says that on a finite vertex set a parent relation has no directed cycle exactly when it is well-founded.
