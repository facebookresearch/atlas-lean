# Lower bound on all elements of a heap

Let $A$ be a type with a relation $\le$ and $a \in A$. The property that $a$ is a lower bound of
a leftist heap is defined recursively: it holds for the empty heap, and it holds for a node
$\langle k, y, \ell, r \rangle$ exactly when $a \le y$ and $a$ is a lower bound of both $\ell$
and $r$. So $a$ is a lower bound exactly when $a \le y$ for every element $y$ stored in the heap.
