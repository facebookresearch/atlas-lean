# Partition hash table with fingerprint-indexed buckets

A *partition hash table* for at most $n$ keys of $w$ bits, with machine word size $w = \Theta(\log n)$ and a fully random bucket hash, splits the keys into $n/\log^3 n$ buckets, each an array of $\log^3 n + c\log^2 n$ slots for a constant $c>0$, so that the expected load of a bucket is at most $\log^3 n$. The items of a bucket are kept left-justified, with an $O(\log\log n)$-bit counter, and a bucket overflow triggers a rebuild of the whole table. Inside a bucket, keys are located through a *query mapper* indexed by fingerprints of $\Theta(\log \log n)$ bits that are distinct within the bucket (a fingerprint collision makes the bucket pick a fresh fingerprint function and rebuild its mapper): a B-tree with $B = \sqrt{\log n}$ whose nodes, of $O(\sqrt{\log n}\,\log\log n) = o(\log n)$ bits, are operated on by table lookup, mapping fingerprints to slot positions inside the bucket. This indexed partition hash table uses $nw + O(n \log \log n)$ bits, answers queries and deletions in worst-case $O(1)$ time and insertions in $O(1)$ expected time.

Variants used in this chapter store in each bucket only the Feistel quotient of a key instead of the key, as in the quotienting of Arbitman, Naor and Segev and of Iceberg hashing, send keys that overflow their bucket to a shared backyard pool, as in Iceberg hashing, and send keys whose fingerprints collide to a small buffer; these variants are not in the cited sources.

## Depends on

- [One-round Feistel quotienting of keys](one-round-feistel-quotienting.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, "Modern Hashing Made Simple", Proceedings of the 2024 SIAM Symposium on Simplicity in Algorithms (SOSA), pp. 363-373, 2024 (Sections 3 and 4, Lemmas 4.1-4.3).
- M. A. Bender, A. Conway, M. Farach-Colton, W. Kuszmaul and G. Tagliavini, "Iceberg Hashing: Optimizing Many Hash-Table Criteria at Once", Journal of the ACM 70(6), 2023; arXiv:2109.04548.
- Y. Arbitman, M. Naor and G. Segev, "Backyard Cuckoo Hashing: Constant Worst-Case Operations with a Succinct Representation", Proceedings of the 51st IEEE Symposium on Foundations of Computer Science (FOCS), pp. 787-796, 2010.
