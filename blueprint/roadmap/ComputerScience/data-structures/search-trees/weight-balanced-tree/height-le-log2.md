# Height of a weight-balanced tree is logarithmic

Write $|t|$ for the number of keys of a
binary tree $t$ and $h(t)$ for its height, where the empty tree has height $0$ and a node has
height one more than the larger height of its two subtrees. If $t$ is weight-balanced, then
$h(t) \le \lfloor \log_2 ((|t| + 1)^3) \rfloor + 1$.

The proof passes from the exponential weight lower bound in base $4/3$ to base $2$, using
$(4/3)^3 > 2$.
