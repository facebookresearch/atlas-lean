# Binary heap extraction splits off the minimum

Let $h$ be a binary min-heap over a linearly
ordered type. If extracting the minimum of $h$ succeeds and returns the value $x$ and the heap
$h'$, then the multiset of elements of $h$ equals the multiset of elements of $h'$ with one copy
of $x$ added.

The statement is phrased by adding $x$ back, not by erasing it from the multiset of $h$.
