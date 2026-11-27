# Correctness of counting sort

Let $k$ be a natural number, let $\mathrm{key}$ assign to
each record a key in $\{0, \dots, k-1\}$, and let $A$ be an array of records. The array that
counting sort returns on $A$ lists its records in nondecreasing order of key, is a permutation of
$A$, and is stable: for every key $q < k$, the records of the output with key $q$, read from left
to right, form the same sequence as the records of $A$ with key $q$.
