# Preferred children and preferred paths

Let $P$ be the complete (perfect when $n + 1$ is a power of two) BST on $[n]$ used as a reference tree. The *left region* of a node $v$ of $P$ consists of $v$ and its left subtree, and its *right region* of its right subtree. At any time, the *preferred child* of an internal node $v$ is its left child if the most recent access to a key in the subtree of $v$ was in the left region of $v$, its right child if it was in the right region, and undefined if no key in the subtree has been accessed; leaves have no preferred child. Starting from any node that is not a preferred child and repeatedly following preferred children until reaching a node without one yields a *preferred path*; the preferred paths partition the nodes of $P$, and each has at most $\lceil \log_2(n+1) \rceil$ nodes.

## Sources

- Erik D. Demaine, Dion Harmon, John Iacono, Mihai Pătraşcu, "Dynamic Optimality—Almost", SIAM Journal on Computing 37(1) (2007); FOCS (2004).
