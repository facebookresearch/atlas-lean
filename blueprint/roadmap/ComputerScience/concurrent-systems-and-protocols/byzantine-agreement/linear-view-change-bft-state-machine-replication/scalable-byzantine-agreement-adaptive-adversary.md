# Byzantine agreement with subquadratic total communication against an adaptive adversary

In the synchronous full-information model with private channels, there is a randomized Byzantine agreement protocol tolerating $t < (1/3 - \varepsilon) n$ adaptive Byzantine corruptions in which each correct process sends $\tilde O(\sqrt n)$ bits, for $\tilde O(n^{3/2})$ total communication, and which terminates in polylogarithmic rounds with high probability; this breaks the $\Omega(n^2)$ barrier that holds for deterministic protocols.

## Proof sketch

Correct processes jointly generate shared random coins by a scalable variant of Bracha's coin-flipping with secret sharing among small committees, and agreement proceeds by sampling: each process queries $\tilde O(\sqrt n)$ random processes for their current values, and sampling arguments based on birthday-type intersections ensure any two correct processes' samples overlap in many correct processes. The adaptive adversary cannot predict which processes will be queried, so it cannot bias enough samples.

## Depends on

- [Byzantine fault-tolerant state machine replication under partial synchrony](byzantine-state-machine-replication.md)
- [Reaching Byzantine agreement](../solves.md)

## Proof depends on

- [Byzantine agreement requires quadratic communication](dolev-reischuk-quadratic-lower-bound.md)

## Sources

- V. King, J. Saia, "Breaking the O(n^2) Bit Barrier: Scalable Byzantine Agreement with an Adaptive Adversary", Journal of the ACM 58(4) (2011); PODC 2010.
