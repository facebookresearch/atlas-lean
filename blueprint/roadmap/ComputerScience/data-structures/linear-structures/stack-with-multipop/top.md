# Stack top

Stacks over a type $\alpha$ are lists of elements of $\alpha$, with the first
element as the top. Reading the top of the empty stack returns underflow (no value) at cost $0$.
Reading the top of a stack with top $v$ returns $v$ at cost $1$ (one successful top event); the
stack itself is not returned or changed.
