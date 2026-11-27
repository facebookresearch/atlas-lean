# Timed smaller-child selection

Let $a$ be an array over a linearly ordered type and $i$
an index, with left child $2i + 1$ and right child $2i + 2$; cost is counted as the pair
(value comparisons, array swaps). If both children are valid indices of $a$, the selection costs
$(1, 0)$ and returns the right child when its value is strictly less than the value at the left
child, and the left child otherwise. If only the left child is a valid index, it returns the
left child at cost $(0, 0)$. If the left child is not a valid index, it returns no child at cost
$(0, 0)$.
