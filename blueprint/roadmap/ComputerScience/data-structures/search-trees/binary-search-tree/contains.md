# Search in a binary search tree

For a linearly ordered type $\alpha$, a key $x \in \alpha$ and
a binary tree $t$ with keys in $\alpha$, the search for $x$ in $t$ returns a Boolean: false if $t$
is empty, and if $t$ is a node with key $k$, left subtree $L$ and right subtree $R$, the search
for $x$ in $L$ when $x < k$, the search for $x$ in $R$ when $k < x$, and true otherwise.

Unlike the index of a key in a binary tree, which encodes the root-to-node path as a positive
binary number, this search returns only whether the key was found.
