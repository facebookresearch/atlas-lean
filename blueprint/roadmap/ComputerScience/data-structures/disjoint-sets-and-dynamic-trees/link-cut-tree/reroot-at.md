# Rerooting a tree at a vertex

For a vertex $x$ and a rooted ordered tree $T$ with root $r$,
rerooting $T$ at $x$ is defined recursively. If $r = x$, the result is $T$ itself. Otherwise let
$C$ be the first child subtree of $r$ that contains $x$, let $p$ be the root of $C$, and let $C'$
be $C$ rerooted at $x$. The result is $C'$ with the tree formed by $r$ and its remaining
children (in their original order) attached as a new last child of the first node of $C'$, in
preorder, labelled $p$. If no child subtree of $r$ contains $x$, rerooting is undefined; thus
rerooting is defined exactly when $x$ is a vertex of $T$.

When the vertices of $T$ are distinct, this reverses the edges on the path from $r$ to $x$ and
keeps every other edge, so the undirected tree is unchanged and only the root moves to $x$. This
is the tree surgery behind making $x$ the root in a link-cut tree.
