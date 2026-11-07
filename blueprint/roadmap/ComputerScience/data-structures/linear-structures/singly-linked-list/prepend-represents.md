# Prepending conses onto the represented list

Fix a capacity $n$, let $s$ be a store
assigning to each identity below $n$ either nothing or a singly linked list node, let
$\mathrm{head}$ be an identity below $n$ or NIL, and let $x$ be an identity such that $s(x)$ is a
node. If $s$ and $\mathrm{head}$ represent the list of identities $i_0, \dots, i_{k-1}$ and $x$ is
none of $i_0, \dots, i_{k-1}$, then the store and head returned by Prepend on $s$, $\mathrm{head}$
and $x$ represent the list $x, i_0, \dots, i_{k-1}$.
