# Heap

`heap t`: `t` is heap-ordered (every node's value is ≤ every value
in its subtrees). This is the definition from
`HOL-Data_Structures.Heaps` (Isabelle distribution, not in the AFP
tree): `heap Leaf = True`, and for a node, both subtrees are heaps and
the root is ≤ every element of both subtrees.
