# Asynchronous Byzantine reliable broadcast requires n > 3t

In the asynchronous message-passing model with authenticated channels and $t$ static Byzantine faults, no deterministic protocol on $n$ processes with $3 \le n \le 3t$ solves reliable broadcast (validity, consistency, totality, no spurious delivery), even over a singleton value set; consistent broadcast (validity and consistency only) is impossible for $3 \le n \le 3t$ over every value set with at least two elements. Combined with Bracha's protocol, deterministic asynchronous Byzantine reliable broadcast tolerating $t$ faults exists if and only if $n \le 2$ or $n > 3t$.

## Proof sketch

Partition processes into three groups of size at most $t$. Delay all messages between two groups indefinitely; a correct group must deliver without hearing from the delayed group, which might be correct, while the third group equivocates. Replaying the resulting views yields two correct processes delivering different values, or a delivery forced in a run where the sender is silent.

## Depends on

- [Reliable broadcast](../../replication-and-consistency/reliable-broadcast.md)
- [Asynchronous message-passing systems](../../distributed-execution-models/asynchronous-message-passing-systems.md)
- [Fail-stop, omission and Byzantine faults](../../distributed-execution-models/fail-stop-omission-and-byzantine-faults.md)

## Proof depends on

- [Bracha's Byzantine reliable broadcast](../../replication-and-consistency/bracha-s-byzantine-reliable-broadcast.md)

## Sources

- Gabriel Bracha and Sam Toueg, "Asynchronous Consensus and Broadcast Protocols", Journal of the ACM, 1985.
- Gabriel Bracha, "Asynchronous Byzantine Agreement Protocols", Information and Computation, 1987.
