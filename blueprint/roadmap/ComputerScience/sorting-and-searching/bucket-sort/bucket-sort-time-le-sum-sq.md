# Bound on the cost of bucket sort via squared bucket sizes

Let $R$ be a linearly
ordered field with a floor function and let $x_1, \dots, x_n$ be an array of elements of $R$
that all lie in $[0, 1)$. For $0 \le i < n$ let $c_i$ be the number of indices $j$ with
$\lfloor n x_j \rfloor = i$. Then the cost of bucket sort on this array is at most
$5n + \sum_{i=0}^{n-1} c_i^2$.
