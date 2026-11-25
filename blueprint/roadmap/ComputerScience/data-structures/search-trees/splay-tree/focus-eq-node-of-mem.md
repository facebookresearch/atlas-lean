# In a search tree the search for a present key ends at its node

If $t$ is a binary search tree containing the key $x$, the [subtree at the end of the search
path](focus.md) $\mathrm{focus}(x, t)$ is rooted at a node holding $x$. So in the [access
lemma](access-lemma-weighted.md) the size $W(\mathrm{focus}(x, t))$ is the size $s(x)$ of the node
holding $x$, which is at least $w(x)$.
