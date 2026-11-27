# Correctness of 2-3 tree insertion

Let $\alpha$ be linearly ordered, let $x \in \alpha$,
and let $t$ be an ordered 2-3 tree of height $h$. Then inserting $x$ into $t$ meets the insertion
specification. If the insertion returns a single tree $t'$ of height $h$, then $t'$ is ordered
and its inorder traversal is the ordered insertion of $x$ into the inorder traversal of $t$. If
it returns a split into trees $l$ and $r$ of height $h$ around a promoted key $k$, then $l$ and
$r$ are ordered, every key of $l$ is less than $k$, every key of $r$ is greater than $k$, and
the traversal of $l$ followed by $k$ and then the traversal of $r$ is the ordered insertion of
$x$ into the inorder traversal of $t$.

Balance is automatic from the height index.
