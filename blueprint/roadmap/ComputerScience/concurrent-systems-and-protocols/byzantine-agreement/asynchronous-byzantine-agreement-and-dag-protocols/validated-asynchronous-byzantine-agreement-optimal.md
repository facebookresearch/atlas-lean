# Validated asynchronous Byzantine agreement with optimal expected quadratic communication

In validated asynchronous Byzantine agreement (VABA), processes propose values from an arbitrary domain together with an externally checkable validity predicate, and must decide a common value satisfying the predicate (external validity). Assuming a trusted setup for threshold signatures and $n \ge 3t + 1$, there is a VABA protocol with expected $O(1)$ rounds (asynchronous time) and expected $O(n^2)$ words of communication, which is asymptotically optimal in resilience, time and word complexity.

## Proof sketch

Each process runs, in parallel, a leader-based "promotion" procedure that drives its own proposal through several phases of threshold-signed certificates, each with linear communication. After $n - t$ processes complete their promotion, a threshold coin elects a leader retrospectively; with probability at least $2/3$ the elected leader's promotion has completed, and a view-change step in which processes report their highest certificates for the elected leader ensures agreement. Each view costs $O(n^2)$ words and an expected constant number of views suffices.

## Depends on

- [Asynchronous binary Byzantine agreement and common coins](asynchronous-binary-byzantine-agreement.md)
- [Quorum certificate from threshold signatures](../linear-view-change-bft-state-machine-replication/quorum-certificate-threshold-signatures.md)

## Proof depends on

- [Quorums of size n - f intersect in a correct replica when n is at least 3f + 1](../linear-view-change-bft-state-machine-replication/byzantine-quorum-intersection.md)
- [Signature-free asynchronous binary Byzantine agreement with O(n^2) messages per round](signature-free-asynchronous-binary-agreement.md)

## Sources

- I. Abraham, D. Malkhi, A. Spiegelman, "Asymptotically Optimal Validated Asynchronous Byzantine Agreement", PODC 2019.
- C. Cachin, K. Kursawe, F. Petzold, V. Shoup, "Secure and Efficient Asynchronous Broadcast Protocols", CRYPTO 2001.
