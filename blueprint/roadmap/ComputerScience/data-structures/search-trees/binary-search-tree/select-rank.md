# Selecting the rank of a key returns the key

Let $\alpha$ be a linearly ordered type
and let $t$ be a binary search tree with keys in $\alpha$, that is, at every node each key of the
left subtree is strictly smaller and each key of the right subtree is strictly larger than the
node's key. If $x$ is a key of $t$, then selecting, in $t$, the index equal to the rank of $x$
in $t$ returns $x$.
