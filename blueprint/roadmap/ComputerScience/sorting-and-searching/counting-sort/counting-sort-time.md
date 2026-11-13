# Running time of counting sort

Let $k$ be a natural number, let $\mathrm{key}$ assign to
each record a key in $\{0, \dots, k-1\}$, and let $A$ be an array of $n$ records. Counting sort on
$A$ with this key is charged at most $7n + 3k$ operations, where one operation is charged for each
counter initialization, key evaluation, counter read, counter write and output write.
