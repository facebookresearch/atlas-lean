# Accumulator preorder traversal

For a rooted ordered tree $t$ with root $r$ and child
subtrees $c_1, \dots, c_k$ (in order) and a list $a$, the accumulator traversal $T(t, a)$ is
the list whose first entry is $r$ and whose remaining entries are
$T(c_1, T(c_2, \dots, T(c_k, a) \dots))$; when $k = 0$ the remaining entries are $a$.

The list $T(t, a)$ equals the preorder vertex list of $t$ followed by $a$, so the preorder list
is computed in linear time rather than by repeatedly appending child lists.
