# Heapify Down

For an array $a$ and a position $i$, sift-down for a max-heap selects the [larger child](timed-max-child.md) $j$ of $i$; if there is none it stops. Otherwise it charges one comparison and, when $a[i] < a[j]$, charges one swap, swaps $a[i]$ and $a[j]$ and continues from $j$; when $a[i] \ge a[j]$ it stops. The cost is a pair counting comparator calls and executed swaps, including the comparisons made by child selection.
