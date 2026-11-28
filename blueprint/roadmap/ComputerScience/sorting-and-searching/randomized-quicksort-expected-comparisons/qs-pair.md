# Qs Pair

The pair $(E_n, S_n)$ of the randomized-quicksort expected comparison count $E_n$ and its running sum $S_n = \sum_{k \le n} E_k$, computed together: the base is $(0, 0)$, and from $(E_n, S_n)$ the next pair is $(e, S_n + e)$ with $e = n + 2 S_n / (n + 1)$. Its first component satisfies $E_0 = 0$ and $E_{n+1} = n + \frac{2}{n+1} \sum_{k \le n} E_k$ (the pivot is uniform, and the two subproblems have sizes $k$ and $n - k$).
