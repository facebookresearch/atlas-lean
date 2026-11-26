# Deamortized global rebuilding by epochs

Divide the operation sequence into epochs of $q$ operations. Suppose the background work of an epoch (rebuilding dirty buckets with fresh salts into per-bucket *shadow* copies, draining the old collision buffer into its new position, and clearing the old buffer's nodes) consists of at most $cq$ steps for a constant $c$, each taking $O(1)$ worst-case time, that these steps remain correct under any interleaving with foreground operations, and that a completed shadow copy replaces its live copy in $O(1)$ time. *Deamortized global rebuilding* runs $\lceil c \rceil$ background steps after each foreground operation. Then every operation, including its background steps, takes $O(1)$ worst-case time beyond the foreground work, and all background work of an epoch is finished by the end of that epoch, since $q\lceil c\rceil \ge cq$.

## Depends on

- [Partition hash table with fingerprint-indexed buckets](../succinct-hash-tables/partition-hash-table.md)

## Sources

- M. H. Overmars, "The Design of Dynamic Data Structures", Lecture Notes in Computer Science 156, Springer, 1983.
- M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, "Modern Hashing Made Simple", Proceedings of the 2024 SIAM Symposium on Simplicity in Algorithms (SOSA), 2024.
