# Paxos proposal-safety step

Let $b < b'$ be ballots. Suppose a set of more than $n/2$ of the $n$ acceptors all accepted the proposal $(b, v)$, and each member of a set $Q$ of more than $n/2$ acceptors gives a report, either nothing or a proposal $(c, w)$. Assume every report $(c, w)$ of a member of $Q$ is a proposal that member accepted, with $c < b'$; every acceptance by a member of $Q$ at a ballot below $b'$ is at a ballot no higher than the ballot of its report (in particular, that member reports a proposal); and every proposal accepted by a member of $Q$ at a ballot in $[b, b')$ has value $v$. Then some member of $Q$ reports a ballot at least $b$ with value $v$, and every report in $Q$ of highest ballot among the reports in $Q$ has value $v$.

## Sources

- L. Lamport, "Paxos made simple", *ACM SIGACT News* 32 (2001).
