# Deletion from a circular list with a sentinel

Let $S$ be a node store with $c$ cells,
each either empty or holding a node (a payload, an optional next address and an optional
previous address in $\{0, \dots, c-1\}$). Let $x$ be an address whose cell holds a node $\nu$
with previous address $p$ and next address $n$, where the cells at $p$ and $n$ are nonempty.
Sentinel deletion of $x$ from $S$ is the timed computation that first sets the next address of
the node at $p$ to $n$, at cost $1$, then sets the previous address of the node at $n$ in the
resulting store to $p$, at cost $1$, and returns the store obtained.

These dereferences are its only preconditions: it does not check that $x$ is not the sentinel
or that $x$ lies on a represented list.
