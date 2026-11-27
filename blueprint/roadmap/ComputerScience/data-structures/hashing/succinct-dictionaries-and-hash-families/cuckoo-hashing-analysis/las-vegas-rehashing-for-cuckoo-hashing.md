# Las Vegas rehashing for cuckoo hashing

In a cuckoo dictionary whose seeds are drawn uniformly from a finite seed set and that, when an insertion exceeds the eviction cap, repeatedly draws a fresh hash pair, clears both sub-tables and reinserts all stored keys in insertion order until every key is placed, the seed in use after rehashing is uniformly distributed over the seeds under which the stored key sequence is placed without exceeding the cap. Consequently, if the seed law is a good cuckoo hash pair, a rehash takes an expected $O(1)$ attempts, each costing $O(n)$ expected work, and since rehashing is triggered with probability $O(1/n^2)$ per insertion, rehashing contributes $o(1)$ expected work per operation.

## Proof sketch

Each attempt is an independent draw; conditioning a uniform law on the event that the attempt succeeds yields the uniform law on the successful seeds. Success has probability at least $1/2$, so the number of attempts is dominated by a geometric variable with mean at most $2$.

## Depends on

- [Good cuckoo hash-pair contract](good-cuckoo-hash-pair-contract.md)

## Sources

- R. Pagh and F. F. Rodler, "Cuckoo Hashing", Journal of Algorithms 51(2), 2004 (Section 2.3, cost of forced rehashes).
