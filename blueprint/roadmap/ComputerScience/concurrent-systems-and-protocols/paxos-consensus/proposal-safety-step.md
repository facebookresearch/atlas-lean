# Paxos proposal-safety step

Suppose a majority of $n$ acceptors accepted the proposal $(b, v)$, and a proposer at ballot $b' > b$ reads a majority quorum $Q$, each member reporting the highest-ballot proposal it had accepted (or nothing). Assume every report is a proposal its acceptor accepted at a ballot below $b'$; every acceptance of a member of $Q$ below $b'$ is at a ballot no higher than its report; and every proposal accepted in $Q$ at a ballot in $[b, b')$ has value $v$. Then some member of $Q$ reports a ballot at least $b$ with value $v$, and every highest-ballot report in $Q$ has value $v$, so the proposer of $b'$ proposes $v$.

## Sources

- L. Lamport, "Paxos made simple", *ACM SIGACT News* 32 (2001).
