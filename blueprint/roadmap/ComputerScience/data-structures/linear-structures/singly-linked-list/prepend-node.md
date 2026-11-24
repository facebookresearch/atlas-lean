# The prepended node points at the old head

Fix a capacity $n$, let $s$ be a store
assigning to each identity below $n$ either nothing or a singly linked list node, let
$\mathrm{head}$ be an identity below $n$ or NIL, and let $x$ be an identity such that $s(x)$ is a
node. Then the entry at $x$ of the store returned by Prepend on $s$, $\mathrm{head}$ and $x$ is the
node $s(x)$ with its payload kept and its next pointer replaced by $\mathrm{head}$.
