# Doubly-linked list prepend preserves allocation

Fix a capacity $n$ and let $s$ be a store
assigning to each identity $i < n$ either a node or nothing, let $\mathrm{head}$ be NIL or an
identity, and let $x$ be an identity such that $s(x)$ is a node and, when $\mathrm{head}$ is an
identity, $s(\mathrm{head})$ is a node. Let $s'$ be the store returned by List Prepend on $s$,
$\mathrm{head}$ and $x$. Then for every identity $z$, $s'(z)$ is a node if and only if $s(z)$ is a
node.
