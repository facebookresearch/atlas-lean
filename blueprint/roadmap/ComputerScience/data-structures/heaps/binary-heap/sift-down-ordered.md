# Sift-down restores heap order

Let $a$ be an array over a linearly ordered type that
satisfies the sift-down precondition at a valid index $i$: the only edges that may violate heap
order are those leaving $i$, and moving either child of $i$ up to position $i$ keeps the edge
entering $i$ ordered. Then the array obtained by sifting down $a$ from $i$ is heap-ordered.
