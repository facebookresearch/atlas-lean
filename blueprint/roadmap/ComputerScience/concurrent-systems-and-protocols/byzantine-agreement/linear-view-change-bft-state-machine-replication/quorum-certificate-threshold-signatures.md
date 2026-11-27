# Quorum certificate from threshold signatures

A $(k, n)$-threshold signature scheme provides each replica $i$ with a signing key share; a signature share $\sigma_i(m)$ on a message $m$ can be verified with a public key, any $k$ valid shares on $m$ combine into a single signature $\sigma(m)$ verifiable against a single public key, and without $k$ shares no valid combined signature can be produced except with negligible probability. In leader-based BFT protocols with $k = n - f$, a quorum certificate (QC) for a block $B$ in view $v$ and phase $\phi$ is a combined threshold signature on $(B, v, \phi)$; its size is constant (independent of $n$), so a leader can forward a QC to all replicas with $O(n)$ total communication.

If $n \ge 3f + 1$ and at most $f$ replicas are Byzantine, a QC with $k = n - f$ shares determines its value uniquely per view and phase: any two sets of $n - f$ replicas intersect in at least $2(n - f) - n = n - 2f \ge f + 1$ replicas (the cardinality condition for threshold quorum systems with quorum size $q = n - f$ and $b = f$; larger sets contain such quorums), hence in a correct replica. So if every correct replica signs at most one value per view and phase, two QCs for conflicting values in the same view and phase cannot both exist.

## Depends on

- [Byzantine fault-tolerant state machine replication under partial synchrony](byzantine-state-machine-replication.md)
- [Cardinality conditions for threshold Byzantine quorum systems and masking-register safety](../byzantine-broadcast-and-quorum-systems/cardinality-conditions-for-threshold-byzantine-quorum-systems-and-masking-regist.md)

## Sources

- M. Yin, D. Malkhi, M. K. Reiter, G. Golan Gueta, I. Abraham, "HotStuff: BFT Consensus with Linearity and Responsiveness", PODC 2019, arXiv:1803.05069.
- C. Cachin, K. Kursawe, V. Shoup, "Random Oracles in Constantinople: Practical Asynchronous Byzantine Agreement Using Cryptography", Journal of Cryptology 18(3) (2005); PODC 2000.
