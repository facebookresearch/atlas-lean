# Expected search cost of a binary search tree

Let $R$ be an additive commutative monoid,
let $n$ be a natural number, and let $p_0, \dots, p_{n-1} \in R$ (key weights) and
$q_0, \dots, q_n \in R$ (dummy-key weights) be given. Let $T$ be a binary tree whose nodes are
labelled by elements of $\{0, \dots, n-1\}$ and whose inorder traversal is $0, 1, \dots, n-1$, so
each key labels exactly one node and $T$ has exactly $n + 1$ empty subtrees. The depth of a node
or empty subtree is its distance from the root, the root having depth $0$; write $d(k)$ for the
depth of the node labelled $k$ and $\ell_0, \dots, \ell_n$ for the depths of the empty subtrees
listed from left to right. The expected search cost of $T$ is

$$\sum_{k=0}^{n-1} (d(k) + 1) \cdot p_k + \sum_{i=0}^{n} (\ell_i + 1) \cdot q_i,$$

where $m \cdot x$ denotes the $m$-fold sum of $x$ in $R$.
