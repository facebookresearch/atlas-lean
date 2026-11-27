# Las Vegas rehashing for cuckoo hashing

In a cuckoo dictionary whose seeds are drawn uniformly from a finite seed set and that, when an insertion exceeds the eviction cap, repeatedly draws a fresh hash pair, clears both sub-tables and reinserts all stored keys in insertion order until every key is placed, the seed in use after rehashing is uniformly distributed over the seeds under which the stored key sequence is placed without exceeding the cap. Consequently, if the seed law is a good cuckoo hash pair, a rehash takes an expected $O(1)$ attempts, each costing $O(n + r)$ expected work ($\Theta(r)$ to clear the two sub-tables of size $r$, and expected $O(1)$ displacement rounds for each of the at most $n$ reinsertions), and since rehashing is triggered with probability $O(1/n^2)$ per insertion (for $n \ge 3$), rehashing contributes $O((n + r)/n^2)$ expected work per operation, which is $o(1)$ when $r = o(n^2)$, for instance for Pagh and Rodler's sub-tables of size $r = (1 + \varepsilon) n$.

## Proof sketch

Each attempt is an independent draw; conditioning a uniform law on the event that the attempt succeeds yields the uniform law on the successful seeds. Success has probability at least $1/2$, so the number of attempts is dominated by a geometric variable with mean at most $2$; since the number of attempts is a stopping time for the independent attempts, Wald's identity multiplies its mean by the expected cost of one attempt.

## Depends on

- [Good cuckoo hash-pair contract](good-cuckoo-hash-pair-contract.md)

## Sources

- R. Pagh and F. F. Rodler, "Cuckoo Hashing", Journal of Algorithms 51(2), 2004 (Section 2.3, cost of forced rehashes).
