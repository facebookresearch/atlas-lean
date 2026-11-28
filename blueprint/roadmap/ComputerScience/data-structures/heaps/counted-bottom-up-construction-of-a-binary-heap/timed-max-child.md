# Timed Max Child

For an array $a$ of size $n$ and a position $i$, the larger child of $i$ in the max-heap order is computed as follows: if $2i + 1 \ge n$ there is no child; if only the left child $2i + 1$ exists it is returned; if both children $2i + 1$ and $2i + 2$ exist, one comparison is charged and the right child is returned when $a[2i+1] < a[2i+2]$, otherwise the left child, so ties go to the left child. Only the two-child comparison is charged.
