# Pointers of the node prepended to a doubly-linked list

Fix a capacity $n$ and let $s$ be a
store assigning to each identity $i < n$ either a node or nothing, let $\mathrm{head}$ be NIL or an
identity, and let $x$ be an identity such that $s(x)$ is a node and, when $\mathrm{head}$ is an
identity, $s(\mathrm{head})$ is a node. Suppose moreover that $\mathrm{head}$ is not $x$ (it may be
NIL). Let $s'$ be the store returned by List Prepend on $s$, $\mathrm{head}$ and $x$. Then $s'(x)$
is the node $s(x)$ with next pointer $\mathrm{head}$ and previous pointer NIL.
