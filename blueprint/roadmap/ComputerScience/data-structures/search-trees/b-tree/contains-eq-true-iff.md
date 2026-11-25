# Correctness of B-tree search

Let $\alpha$ be linearly ordered and let $T$ be a B-tree
of minimum degree $t$ with keys in $\alpha$. For every key $x \in \alpha$, the search procedure
returns true on $x$ and $T$ if and only if $x$ is a member of $T$, that is, $x$ occurs in the
inorder flattening of $T$.
