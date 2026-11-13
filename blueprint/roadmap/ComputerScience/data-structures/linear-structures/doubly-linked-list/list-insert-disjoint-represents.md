# Doubly-linked-list insertion preserves disjoint lists

Suppose the store $S$ with head
$h$ represents the list of cells $(i_0, \dots, i_{m-1})$ and with head $h'$ represents a list
$L'$ of cells, and that the two lists have no cell in common. Let $k < m$, let $x$ be an
allocated cell not in $L'$, and assume that cell $i_k$ and its successor in $S$, if any, are
allocated. Then the store returned by inserting $x$ after $i_k$, with head $h'$, still
represents $L'$.
