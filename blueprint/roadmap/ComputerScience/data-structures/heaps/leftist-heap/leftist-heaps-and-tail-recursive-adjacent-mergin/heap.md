# Min-heap property

Let $A$ be a type with a relation $\le$. The min-heap property of a leftist heap over $A$ is
defined recursively: the empty heap has it, and a node $\langle k, x, \ell, r \rangle$ has it
exactly when $x \le y$ for every element $y$ of $\ell$ and every element $y$ of $r$, and both
$\ell$ and $r$ have the min-heap property.
