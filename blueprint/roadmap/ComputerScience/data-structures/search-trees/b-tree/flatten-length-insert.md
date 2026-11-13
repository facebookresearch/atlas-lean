# Size of a B-tree after insertion

Let $\alpha$ be linearly ordered, let $t \ge 2$, let
$T$ be a B-tree of minimum degree $t$ with keys in $\alpha$, and let $x \in \alpha$. Let $T'$ be
the tree obtained by inserting $x$ into $T$ with minimum degree $t$. If $x$ occurs in the
inorder flattening of $T$, then the flattening of $T'$ has the same length as that of $T$;
otherwise it is one longer.
