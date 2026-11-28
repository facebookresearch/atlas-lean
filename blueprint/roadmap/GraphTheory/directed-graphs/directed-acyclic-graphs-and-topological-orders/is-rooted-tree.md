# Rooted tree (arborescence) in a digraph

A digraph $G$ on a vertex type $V$ is a rooted tree with root $r \in V$ when all of the following hold:

1. $G$ is acyclic: no vertex reaches itself by a directed walk of positive length;
2. $r$ has no parent: there is no edge $u \to r$;
3. every vertex $v \ne r$ has exactly one parent: there is a unique $u$ with an edge $u \to v$;
4. every vertex $v$ is reachable from $r$ by a directed walk of length at least $0$.
