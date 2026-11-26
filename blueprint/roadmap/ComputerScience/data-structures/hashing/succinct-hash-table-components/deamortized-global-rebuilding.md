# Deamortized global rebuilding by epochs

*Deamortized global rebuilding* keeps a data structure in a good shape by dividing time into epochs of $q$ operations and, during each epoch, performing a constant amount of background work after each foreground operation: rebuilding dirty buckets with fresh salts, draining an old collision buffer into its new position, and clearing the old buffer's nodes. A per-bucket *shadow* copy is rebuilt alongside the live copy and swapped in when complete. If the total background work of an epoch is at most a constant times $q$, every operation does $O(1)$ worst-case work and the rebuilt structure is ready by the end of the epoch.

## Depends on

- [Partition hash table with fingerprint-indexed buckets](../succinct-hash-tables/partition-hash-table.md)

## Sources

- M. H. Overmars, "The Design of Dynamic Data Structures", Lecture Notes in Computer Science 156, Springer, 1983.
- M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, "Modern Hashing Made Simple", Proceedings of the 2024 SIAM Symposium on Simplicity in Algorithms (SOSA), 2024.
