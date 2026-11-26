# Quorum certificate from threshold signatures

A $(k, n)$-threshold signature scheme provides each replica $i$ with a signing key share; a signature share $\sigma_i(m)$ on a message $m$ can be verified with a public key, any $k$ valid shares on $m$ combine into a single signature $\sigma(m)$ verifiable against a single public key, and without $k$ shares no valid combined signature can be produced except with negligible probability. In leader-based BFT protocols with $k = n - f$, a quorum certificate (QC) for a block $B$ in view $v$ and phase $\phi$ is a combined threshold signature on $(B, v, \phi)$; its size is constant (independent of $n$), so a leader can forward a QC to all replicas with $O(n)$ total communication.

## Depends on

- [Byzantine fault-tolerant state machine replication under partial synchrony](byzantine-state-machine-replication.md)

## Sources

- M. Yin, D. Malkhi, M. K. Reiter, G. Golan Gueta, I. Abraham, "HotStuff: BFT Consensus with Linearity and Responsiveness", PODC 2019, arXiv:1803.05069.
- C. Cachin, K. Kursawe, V. Shoup, "Random Oracles in Constantinople: Practical Asynchronous Byzantine Agreement Using Cryptography", Journal of Cryptology 18(3) (2005); PODC 2000.
