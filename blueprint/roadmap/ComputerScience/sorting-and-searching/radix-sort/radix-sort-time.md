# Cost bound for radix sort

Let $b \ge 2$ and let every record carry a key that is a vector
of $d$ digits in $\{0, \dots, b-1\}$. On an array of $n$ records, radix sort uses at most
$d(7n + 3b)$ charged operations, where each counting-sort pass charges one unit for every counter
initialization, key evaluation, counter read, counter write and output write.
