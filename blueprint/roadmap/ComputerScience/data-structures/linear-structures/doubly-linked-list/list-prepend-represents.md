# Correctness of doubly-linked list prepend

Fix a capacity $n$ and let $s$ be a store
assigning to each identity $i < n$ either a node or nothing, let $\mathrm{head}$ be NIL or an
identity, and let $x$ be an identity such that $s(x)$ is a node and, when $\mathrm{head}$ is an
identity, $s(\mathrm{head})$ is a node. Suppose moreover that $s$ with head $\mathrm{head}$
represents a list $L = (\ell_1, \dots, \ell_k)$ of identities, that is, the $\ell_i$ are distinct,
$\mathrm{head}$ is $\ell_1$ (NIL if $k = 0$), and each $s(\ell_i)$ is a node with previous pointer
$\ell_{i-1}$ and next pointer $\ell_{i+1}$ (NIL past the ends of $L$), and that $x$ is not in $L$.
Let $s'$ and $h'$ be the store and head returned by List Prepend on $s$, $\mathrm{head}$ and $x$.
Then $s'$ with head $h'$ represents the list $(x, \ell_1, \dots, \ell_k)$.
