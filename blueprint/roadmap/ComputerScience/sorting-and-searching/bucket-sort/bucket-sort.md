# Bucket sort

Let $R$ be a linearly ordered field with a floor function and let
$x_1, \dots, x_n$ be an array of elements of $R$ that all lie in $[0, 1)$. If $n = 0$, bucket
sort returns the empty array at zero cost. Otherwise it creates $n$ empty buckets indexed by
$0, \dots, n - 1$, visits the entries in order and prepends each entry $x$ to bucket
$\lfloor n x \rfloor$, sorts each bucket with insertion sort, and concatenates the sorted
buckets in increasing order of index. The cost is $n$ for creating the buckets, plus one per
entry placed, plus one per bucket sorted together with the comparisons insertion sort makes on
it, plus one per bucket and one per entry during concatenation.
