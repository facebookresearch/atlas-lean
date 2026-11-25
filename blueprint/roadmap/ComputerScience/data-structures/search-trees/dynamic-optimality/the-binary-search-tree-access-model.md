# The binary search tree access model

Fix $n \ge 1$ and keys $\{1, \dots, n\}$ stored in a binary search tree. A BST algorithm serves an access sequence $X = x_1 \cdots x_m$ with a single pointer that starts at the root for each access and may move to the left child, the right child or the parent, or rotate the current node with its parent; each $x_i$ must be visited by the pointer while serving the $i$-th access. Serving one access costs $1$ plus the number of pointer moves and rotations it performs, so every access costs at least $1$; this unit charge per access is a normalization added to the move-and-rotation count of the source model. $R_A(X)$ is the total cost of algorithm $A$ on $X$ from a given initial tree, and $\mathrm{OPT}(X)$ is the minimum of $R_A(X)$ over all offline algorithms from the same initial tree. An algorithm is *online* if its operations while serving $x_i$ depend only on $x_1, \dots, x_i$.

## Sources

- J. Iacono, "In pursuit of the dynamic optimality conjecture", in *Space-Efficient Data Structures, Streams, and Algorithms*, LNCS 8066, Springer, 2013; <https://arxiv.org/abs/1306.0207>, Section 1 (the BST unit-cost primitives)
- Original formalization: R. E. Wilber, "Lower bounds for accessing binary search trees with rotations", *SIAM Journal on Computing* 18(1):56–67, 1989. The model above follows Iacono, Section 1, which credits its formalization to Wilber.
