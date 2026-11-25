# Median-of-medians selection agrees with sorting

For every list $L$ over a linearly
ordered type and every natural number $k$, median-of-medians selection of rank $k$ in $L$ returns
the entry at zero-based position $k$ of the insertion sort of $L$ by $\le$ when $k$ is less than
the length of $L$, and returns nothing otherwise.
