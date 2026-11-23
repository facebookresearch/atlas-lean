# Aggregate after a point update of a built segment tree

Let $L = (x_0, \dots, x_{n-1})$
be a list with entries in an additive monoid, let $i < n$, and let $y$ be an element of the
monoid. Applying the point update at index $i$ with value $y$ to the segment tree built from $L$
gives a tree whose aggregate is the sum, taken from left to right, of the list obtained from $L$
by replacing $x_i$ with $y$.
