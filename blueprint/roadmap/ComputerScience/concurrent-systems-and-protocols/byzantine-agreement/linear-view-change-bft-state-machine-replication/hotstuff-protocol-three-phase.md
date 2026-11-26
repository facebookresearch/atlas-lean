# Chained HotStuff with locking and three-phase commit

In HotStuff, time is divided into views with a deterministic leader rotation. In each view, the leader proposes a block extending the block of the highest QC it knows (the high QC), and replicas vote by sending signature shares to the leader if the proposal is safe: it extends the replica's locked block, or its justifying QC has a higher view than the locked block's QC. Votes combine into a QC, and a block is committed by a replica when it heads a chain of three blocks with QCs formed in consecutive views (a three-chain); a replica locks on the first block of the latest two-chain it has seen. On view change, replicas send their high QC to the next leader, which proceeds after receiving $n - f$ of them without any further view-change subprotocol.

## Depends on

- [Quorum certificate from threshold signatures](quorum-certificate-threshold-signatures.md)
- [Quorums of size n - f intersect in a correct replica when n is at least 3f + 1](byzantine-quorum-intersection.md)

## Sources

- M. Yin, D. Malkhi, M. K. Reiter, G. Golan Gueta, I. Abraham, "HotStuff: BFT Consensus with Linearity and Responsiveness", PODC 2019, arXiv:1803.05069.
