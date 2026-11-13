# Leaf traversal of a range tree with an accumulator

For a range tree $t$ and a list $a$
of integers, $\operatorname{aux}(t, a)$ is $a$ if $t$ is empty, the list $x$ followed by $a$ if
$t$ is a single leaf with value $x$, and $\operatorname{aux}(L, \operatorname{aux}(R, a))$ if $t$
is a node with left subtree $L$ and right subtree $R$.

Equivalently, $\operatorname{aux}(t, a)$ is the leaf list of $t$ followed by $a$, so the leaf list
is computed in linear time rather than by repeatedly appending left leaf lists.
