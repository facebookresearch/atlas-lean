# Counting sort

Let $k$ be a natural number and let $\mathrm{key}$ assign to each record a
key in $\{0, \dots, k-1\}$. Counting sort of an array $A$ of records returns an array together
with a count of charged operations. It starts $k$ counters at zero, counts the records of $A$ with
each key, replaces the counters by cumulative counts so that the counter of key $q$ holds the
number of records with key at most $q$, and then scans $A$ from right to left: for each record it
decrements the counter of the record's key and writes the record at the resulting position of the
output, which starts as a copy of $A$. One operation is charged for each counter initialization,
key evaluation, counter read, counter write and output write.
