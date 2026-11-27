# Expected comparisons of randomized quicksort are at most 2nH_n

The expected number $E_n$ of comparisons of randomized quicksort on $n$ distinct keys, given by the recurrence $E_0 = 0$ and $E_{n+1} = n + \frac{2}{n+1} \sum_{k \le n} E_k$, is at most $2 n H_n$, where $H_n$ is the $n$-th harmonic number.
