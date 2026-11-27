# Represented lists have no missing contents

Fix a capacity $n$, let $s$ be a store
assigning to each identity below $n$ either nothing or a singly linked list node, and let
$\mathrm{head}$ be an identity below $n$ or NIL. If $s$ and $\mathrm{head}$ represent the list of
identities $i_0, \dots, i_{k-1}$, then every entry of the contents of $s$ at $i_0, \dots, i_{k-1}$
is a payload rather than nothing.
