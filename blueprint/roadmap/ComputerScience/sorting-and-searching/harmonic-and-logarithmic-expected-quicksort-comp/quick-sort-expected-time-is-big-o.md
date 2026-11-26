# Quick Sort expected Time is Big O

For any family of duplicate-free lists $xs_n$ of length $n$, the expected number of comparisons made by quicksort (which takes the first element as pivot) on a uniformly random permutation of $xs_n$ is $O(n \log n)$. The randomness is the uniform permutation of each given list, and only the sort's comparisons are counted; the family need not be sorted or have any prescribed values. This is not a bound for the order supplied by the caller: on the increasing list, without the shuffle, the sort makes $(n-1) + \dots + 1$ comparisons.
