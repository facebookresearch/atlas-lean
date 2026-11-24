# The remainder of a cut from a valid tree is valid

Let $t$ be a valid Fibonacci tree
over a type with a relation $\le$, and $p$ a path of child indices. If cutting $t$ at $p$
extracts a subtree and leaves a remainder tree $t'$, then $t'$ is valid: its children are
valid, its stored degree equals its number of children, and its root is $\le$ every element
of $t'$.
