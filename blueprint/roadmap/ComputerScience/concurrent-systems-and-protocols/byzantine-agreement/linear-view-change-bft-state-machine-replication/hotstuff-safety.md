# Safety of HotStuff with 3f + 1 replicas

In HotStuff with a fixed set of $n = 3f + 1$ replicas, at most $f$ of them Byzantine, and secure threshold signatures with threshold $k = 2f + 1$, no two correct replicas commit conflicting blocks (blocks neither of which extends the other), regardless of message delays.

## Proof sketch

Suppose block $B$ is committed via a three-chain with QCs in views $v, v+1, v+2$. Any two sets of $2f + 1$ of the $3f + 1$ replicas share at least $f + 1$ replicas, hence at least one correct replica. Of the $2f + 1$ votes forming the QC of view $v + 2$, at least $f + 1$ come from correct replicas, which locked on $B$ (or a descendant) when voting, and a correct replica only votes for a conflicting proposal whose justifying QC has view higher than its lock. By induction on views above $v$, every QC formed in a view greater than $v + 2$ certifies a descendant of $B$, since forming it needs a vote from one of these locked replicas; hence any later committed block extends $B$.

## Depends on

- [Chained HotStuff with locking and three-phase commit](hotstuff-protocol-three-phase.md)
- [Quorum certificate from threshold signatures](quorum-certificate-threshold-signatures.md)

## Proof depends on

- [Cardinality conditions for threshold Byzantine quorum systems and masking-register safety](../byzantine-broadcast-and-quorum-systems/cardinality-conditions-for-threshold-byzantine-quorum-systems-and-masking-regist.md)

## Sources

- M. Yin, D. Malkhi, M. K. Reiter, G. Golan Gueta, I. Abraham, "HotStuff: BFT Consensus with Linearity and Responsiveness", PODC 2019, arXiv:1803.05069, Section 3 (a fixed set of $n = 3f + 1$ replicas, threshold $k = 2f + 1$), Lemma 1 and Theorem 2.
