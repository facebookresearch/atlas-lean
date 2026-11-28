# Validated asynchronous Byzantine agreement with optimal expected quadratic communication

In validated asynchronous Byzantine agreement (VABA, Abraham–Malkhi–Spiegelman Definition 4), processes propose values from a finite domain together with an externally checkable validity predicate, and, except with negligible probability: every value an honest process decides satisfies the predicate (validity); all honest processes that terminate decide the same value (agreement); the decided value was proposed by an honest process with probability at least $1/2$ (quality); if all honest processes start with externally valid values and all messages among honest processes are delivered, then all honest processes decide (termination); and the number of messages of honest processes is probabilistically uniformly bounded (efficiency). Quality excludes trivial protocols that always decide one fixed valid value. A word contains a constant number of signatures and domain values. Assuming a trusted setup for threshold signatures and $n \ge 3t + 1$, there is a VABA protocol secure against an adaptive adversary controlling up to $t$ processes, with expected $O(1)$ running time and expected $O(n^2)$ words of communication, which is asymptotically optimal in resilience, time and word complexity against adaptive adversaries.

## Proof sketch

Each process runs, in parallel, a leader-based "promotion" procedure that drives its own proposal through several phases of threshold-signed certificates, each with linear communication. After $n - t$ processes complete their promotion, a threshold coin elects a leader retrospectively; with probability at least $2/3$ the elected leader's promotion has completed, and a view-change step in which processes report their highest certificates for the elected leader ensures agreement. Each view costs $O(n^2)$ words and an expected constant number of views suffices.

## Depends on

- [Asynchronous binary Byzantine agreement and common coins](asynchronous-binary-byzantine-agreement.md)
- [Quorum certificate from threshold signatures](../linear-view-change-bft-state-machine-replication/quorum-certificate-threshold-signatures.md)

## Proof depends on

- [Cardinality conditions for threshold Byzantine quorum systems and masking-register safety](../byzantine-broadcast-and-quorum-systems/cardinality-conditions-for-threshold-byzantine-quorum-systems-and-masking-regist.md)
- [Signature-free asynchronous binary Byzantine agreement with O(n^2) messages per round](signature-free-asynchronous-binary-agreement.md)

## Sources

- I. Abraham, D. Malkhi, A. Spiegelman, "Asymptotically Optimal Validated Asynchronous Byzantine Agreement", PODC 2019, arXiv:1811.01332, Theorem 1, Section 2 and Definition 4.
- C. Cachin, K. Kursawe, F. Petzold, V. Shoup, "Secure and Efficient Asynchronous Broadcast Protocols", CRYPTO 2001.
