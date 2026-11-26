# Round-robin coordinators reach every process and avoid faulty ones

Let $L$ be a duplicate-free enumeration of $n$ processes and let the coordinator of round $r$ be $L[r \bmod n]$. Every process becomes coordinator within any $n$ consecutive rounds. If at most $t < n$ processes are faulty, then every window of $t + 1$ consecutive rounds contains a round whose coordinator is correct.

## Proof sketch

Consecutive rounds visit distinct positions of $L$ until all $n$ have been visited; $t + 1$ consecutive rounds name $t + 1$ distinct processes, not all faulty, by pigeonhole.

## Depends on

- [Safety of rotating-coordinator consensus](../safety-of-rotating-coordinator-consensus.md)

## Sources

- Tushar Deepak Chandra and Sam Toueg, "Unreliable Failure Detectors for Reliable Distributed Systems", Journal of the ACM, 1996.
- Cynthia Dwork, Nancy Lynch and Larry Stockmeyer, "Consensus in the Presence of Partial Synchrony", Journal of the ACM, 1988.
