# Leftist heap

A leftist heap over a type $A$ is a binary tree with stored ranks: it is either the empty heap
$E$, or a node $\langle k, x, \ell, r \rangle$ made of a stored rank $k \in \mathbb{N}$, an element
$x \in A$, a left subheap $\ell$ and a right subheap $r$, which are themselves leftist heaps over
$A$. No condition is imposed here; the ordering and balance conditions are separate predicates.
