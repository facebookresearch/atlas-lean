# Correctness and comparison bound for heapsort with bottom-up construction

For every
list $xs$ of length $n$ over a linearly ordered type, the list returned by timed heapsort with
bottom-up heap construction on $xs$ is sorted in nondecreasing order and is a permutation of
$xs$, and the number of value comparisons it counts is at most
$2n(\lfloor \log_2 n \rfloor + 1)$, where $\lfloor \log_2 0 \rfloor$ is read as $0$.

**Proof.** [Bottom-up heap construction](../../data-structures/heaps/binary-heap/bottom-up-heap-construction-takes-linear-time.md) returns a heap-ordered permutation of the input after at most $2n$ comparisons. Each extraction outputs the root, which is a minimum of the remaining entries, and moving the last entry to the root and sifting it down leaves a heap-ordered permutation of the other entries; so the output is sorted and is a permutation of $xs$. Each of the $n$ sift-downs starts at the root of an array with fewer than $n$ entries and makes at most $2 \lfloor \log_2 n \rfloor$ [comparisons](../../data-structures/heaps/binary-heap/sift-down-comparisons-le.md), for at most $2n + 2n \lfloor \log_2 n \rfloor$ in total.
