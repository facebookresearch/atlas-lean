# Cutting a subtree out of a Fibonacci forest

For a forest given as a list of Fibonacci
trees, an index $i$ and a path $p$ of child indices, the cut is undefined if the list has no
tree at position $i$ (counting from $0$) or if cutting that tree $t$ at $p$ is undefined.
Otherwise, if cutting $t$ at $p$ extracts the subtree $s$, the result is $s$ together with the
list in which the tree at position $i$ is removed (if the cut of $t$ left no remainder) or
replaced by the remainder (otherwise).
