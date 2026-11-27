# Sentinel deletion removes a node from its circular list

Let $S$ be a node store and $x$
an address whose cell holds a node with previous address $p$ and next address $n$, where the
cells at $p$ and $n$ are nonempty. If $S$ represents a circular doubly linked list with sentinel
$s$ and data addresses $\ell$, and $x$ occurs in $\ell$, then the store returned by sentinel
deletion of $x$ from $S$ represents a circular doubly linked list with sentinel $s$ and the
list of data addresses obtained from $\ell$ by removing the first occurrence of $x$.
