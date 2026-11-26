# Cutting a subtree out of a Fibonacci tree

For a path $p$ of child indices and a Fibonacci
tree $t$, the cut of $t$ at $p$ is either undefined or a pair of an extracted subtree and an
optional remainder tree. For the empty path, the extracted subtree is $t$ and there is no
remainder. For a path consisting of an index $i$ followed by a path $q$, where $t$ has root $r$
and children $c_0, \dots, c_{k-1}$, the cut is undefined if $i \ge k$ or if the cut of $c_i$
at $q$ is undefined. Otherwise, with $s$ the subtree extracted from $c_i$, the extracted
subtree is $s$ and the remainder is the tree with root $r$ whose children are those of $t$
with $c_i$ removed (if the cut of $c_i$ left no remainder) or with $c_i$ replaced by that
remainder (otherwise), and whose stored degree is its new number of children.

When the cut is defined, there is no remainder exactly when $p$ is empty.
