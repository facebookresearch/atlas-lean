# Exact cost of bucket sort

Let $R$ be a linearly ordered field with a floor function
and let $x_1, \dots, x_n$ be an array of elements of $R$ that all lie in $[0, 1)$. For
$0 \le i < n$ let $B_i$ be the list of the entries $x_j$ with $\lfloor n x_j \rfloor = i$,
in decreasing order of $j$, and let $T(B_i)$ be the number of comparisons insertion sort makes
on $B_i$. Then the cost of bucket sort on this array equals $5n + \sum_{i=0}^{n-1} T(B_i)$.
