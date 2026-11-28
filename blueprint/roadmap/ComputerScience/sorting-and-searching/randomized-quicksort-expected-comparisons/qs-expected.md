# Expected comparisons of randomized quicksort

The expected number $E_n$ of comparisons of randomized quicksort on $n$ distinct keys, defined by the
recurrence $E_0 = 0$ and $E_{n+1} = n + \frac{2}{n+1} \sum_{k \le n} E_k$. It equals the expected
comparison count of quicksort on a uniformly random ordering of any duplicate-free list of length $n$.
