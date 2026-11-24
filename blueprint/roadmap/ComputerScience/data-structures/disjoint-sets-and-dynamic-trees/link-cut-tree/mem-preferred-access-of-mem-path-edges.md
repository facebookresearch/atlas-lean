# Access makes the root path preferred

Let $s$ be a link-cut tree state and $x$ a
vertex, let $t$ be the first tree of the represented forest of $s$ that contains $x$, and let
$p$ be the path in $t$ from the root down to the first occurrence of $x$ in preorder. Then every
edge of $p$, taken as the pair (parent, child) of consecutive vertices of $p$, is a preferred
edge of the state obtained from $s$ by accessing $x$.
