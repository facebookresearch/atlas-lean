# Only a proposed value is chosen

In every [Paxos voting history](voting.md), for any quorum system, a chosen value is the value of some issued proposal: if $v$ is chosen, then a proposal $(b, v)$ was issued for some number $b$ (Lamport, *Paxos Made Simple*, Section 2.1, first safety requirement). A quorum is nonempty, so some acceptor accepted the chosen proposal, which was therefore issued.

## Sources

- L. Lamport, *Paxos Made Simple*, ACM SIGACT News 32(4), December 2001, 51–58; author's version dated 01 Nov 2001: Section 2.2.
