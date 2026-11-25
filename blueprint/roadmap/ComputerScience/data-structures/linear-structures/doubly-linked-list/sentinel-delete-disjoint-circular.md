# Sentinel deletion preserves disjoint circular lists

Let $S$ be a node store and $x$ an
address whose cell holds a node with previous address $p$ and next address $n$, where the cells
at $p$ and $n$ are nonempty. Suppose $S$ represents a circular doubly linked list with sentinel
$s$ and data addresses $\ell$, with $x$ in $\ell$, and also one with sentinel $t$ and data
addresses $m$, such that no address occurs both among $s$ and $\ell$ and among $t$ and $m$.
Then the store returned by sentinel deletion of $x$ from $S$ still represents the circular
doubly linked list with sentinel $t$ and data addresses $m$.
