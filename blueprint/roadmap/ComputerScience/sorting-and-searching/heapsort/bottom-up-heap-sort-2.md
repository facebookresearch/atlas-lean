# Heapsort with bottom-up heap construction, with comparison and swap counts

For a list
$xs$ of elements of a linearly ordered type, timed heapsort runs timed bottom-up heap
construction on the array of the entries of $xs$. Then, as long as the array is nonempty, it
outputs the root entry, moves the last entry to the root and deletes the last position at the
cost of one array swap, and runs timed sift-down from index $0$ on the new array. Costs are
pairs (value comparisons, array swaps), added componentwise; the output is as in heapsort with
bottom-up heap construction.
