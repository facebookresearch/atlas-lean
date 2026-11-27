# Cardinality conditions for threshold Byzantine quorum systems and masking-register safety

For the family of all subsets of size $q$ of $n$ servers, with availability read as on the linked definition (for every set $B$ of at most $b$ servers some quorum is disjoint from $B$), the system is a dissemination quorum system against $b$ faults iff $2q - n \ge b + 1$ and $q \le n - b$ (feasible iff $n > 3b$), and a masking quorum system iff $2q - n \ge 2b + 1$ and $q \le n - b$ (feasible iff $n > 4b$). In a masking quorum system, a read that is concurrent with no write, which queries a quorum and returns the highest-timestamped value/timestamp pair reported by at least $b + 1$ of its servers, returns the value written by the last preceding write in some serialization of all preceding writes. The two cardinality characterisations are derived here from Malkhi and Reiter's Definitions 4.1 and 5.1; Malkhi and Reiter state the feasibility thresholds $n > 4b$ and $n > 3b$ (Corollaries 4.4 and 5.5), the dissemination quorum size $\lceil (n + b + 1)/2 \rceil$ (Example 5.6) and the read guarantee (Lemma 4.2).

## Proof sketch

Two $q$-subsets of an $n$-set intersect in at least $2q - n$ elements, with equality attainable when $n \le 2q \le 2n$, and the linked definition asks every two quorums to meet in at least $b + 1$ (resp. $2b + 1$) servers. For $b \le n$, availability against a faulty set of size $b$ requires a $q$-subset of the remaining $n - b$ servers, that is, $q \le n - b$; for $b > n$ neither side of either equivalence holds (for $q \le n$ two quorums meet in at most $n < b + 1$ servers, and for $q > n$ there is no quorum). An integer $q$ with $n + b + 1 \le 2q \le 2(n - b)$ exists iff $n \ge 3b + 1$, and one with $n + 2b + 1 \le 2q \le 2(n - b)$ iff $n \ge 4b + 1$. In a masking system the latest write's quorum meets the read quorum in at least $2b + 1$ servers, of which at least $b + 1$ are correct and report it, while faulty servers alone cannot reach $b + 1$.

## Depends on

- [Dissemination, masking and opaque Byzantine quorum systems](dissemination-masking-and-opaque-byzantine-quorum-systems.md)

## Sources

- Dahlia Malkhi and Michael Reiter, "Byzantine Quorum Systems", Distributed Computing 11, 1998, Definitions 4.1 and 5.1, Lemma 4.2, Corollaries 4.4 and 5.5, and Example 5.6.
