# Predicate on all keys of a 2-3 tree

For a predicate $p$ on keys and a 2-3 tree $t$,
$\mathrm{All}_p(t)$ states that every separator key stored at a node of $t$ satisfies $p$: it
is true at a leaf, and at a node it requires $p$ of each key of the node and
$\mathrm{All}_p$ of each of its subtrees.
