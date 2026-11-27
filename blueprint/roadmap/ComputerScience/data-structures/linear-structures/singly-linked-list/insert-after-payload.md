# Singly-linked-list insertion preserves payloads

Let $S$ be a store assigning to each
identity below $n$ either nothing or a singly linked list node, and let $x$ and $y$ be identities
whose store entries are nodes. For every identity $z$, cell $z$ of the store obtained by inserting
$x$ after $y$ is empty exactly when cell $z$ of $S$ is empty, and otherwise holds a node with the
same payload as the node in cell $z$ of $S$.
