# Quicksort's expected comparisons satisfy the recurrence

For a duplicate-free list of length $n$, the expected number of comparisons of quicksort on a
uniformly random ordering of it equals $E_n$, the solution of $E_0 = 0$,
$E_{n+1} = n + \frac{2}{n+1} \sum_{k \le n} E_k$.
