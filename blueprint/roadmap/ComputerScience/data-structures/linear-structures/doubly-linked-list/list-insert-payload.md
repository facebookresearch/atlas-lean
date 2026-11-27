# Doubly-linked-list insertion preserves payloads

For a store $S$ and allocated cells $x$
and $y$ such that the successor of $y$ in $S$, if any, is allocated, every cell $z$ of the store
returned by inserting $x$ after $y$ is empty exactly when cell $z$ of $S$ is empty, and
otherwise holds a node with the same payload as the node in cell $z$ of $S$.

No hypothesis on the payloads, such as distinct keys, is needed.
