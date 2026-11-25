# Doubly-linked list prepend preserves disjoint lists

Fix a capacity $n$ and let $s$ be a
store assigning to each identity $i < n$ either a node or nothing, let $\mathrm{head}$ be NIL or an
identity, and let $x$ be an identity such that $s(x)$ is a node and, when $\mathrm{head}$ is an
identity, $s(\mathrm{head})$ is a node. Suppose moreover that $s$ with some head $o$ represents a
list $L = (\ell_1, \dots, \ell_k)$ of identities, that is, the $\ell_i$ are distinct, $o$ is
$\ell_1$ (NIL if $k = 0$), and each $s(\ell_i)$ is a node with previous pointer $\ell_{i-1}$ and
next pointer $\ell_{i+1}$ (NIL past the ends of $L$), that $x$ is not in $L$, and that
$\mathrm{head}$ is NIL or an identity not in $L$. Let $s'$ be the store returned by List Prepend on
$s$, $\mathrm{head}$ and $x$. Then $s'$ with head $o$ also represents $L$.
