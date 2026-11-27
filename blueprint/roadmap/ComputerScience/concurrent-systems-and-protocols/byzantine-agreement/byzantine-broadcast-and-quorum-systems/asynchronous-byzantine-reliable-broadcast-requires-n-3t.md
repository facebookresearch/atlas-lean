# Asynchronous Byzantine reliable broadcast requires n > 3t

In the asynchronous message-passing model with authenticated channels and $t$ static Byzantine faults, no deterministic protocol on $n$ processes with $3 \le n \le 3t$ solves consistent broadcast (validity and consistency) over a value set with at least two elements, and hence none solves reliable broadcast (validity, consistency, totality, no spurious delivery) over such a value set (Bracha and Toueg, Theorem 5, whose three-group argument uses only validity and consistency, over two values). The echo/ready protocol solves reliable broadcast whenever $n > 3t$ (Bracha and Toueg, Theorem 6). Hence, for $n \ge 3$ and value sets with at least two elements, deterministic asynchronous Byzantine reliable broadcast tolerating $t$ faults exists if and only if $n > 3t$.

## Proof sketch

Partition processes into three groups of size at most $t$. Delay all messages between two groups indefinitely; a correct group must deliver without hearing from the delayed group, which might be correct, while the third group equivocates. Replaying the resulting views yields two correct processes delivering different values. The same covering argument, using totality and no spurious delivery instead of a second value, shows that reliable broadcast is impossible for $3 \le n \le 3t$ even over a singleton value set, a delivery being forced in a run where the sender is silent; and for $n \le 2$ reliable broadcast is trivially solvable. These two derived remarks are not stated in the cited sources.

## Depends on

- [Reliable broadcast](../../replication-and-consistency/reliable-broadcast.md)
- [Asynchronous message-passing systems](../../distributed-execution-models/asynchronous-message-passing-systems.md)
- [Fail-stop, omission and Byzantine faults](../../distributed-execution-models/fail-stop-omission-and-byzantine-faults.md)

## Proof depends on

- [Bracha's Byzantine reliable broadcast](../../replication-and-consistency/bracha-s-byzantine-reliable-broadcast.md)

## Sources

- Gabriel Bracha and Sam Toueg, "Asynchronous Consensus and Broadcast Protocols", Journal of the ACM 32(4), 1985, §5, Theorems 5 and 6.
- Gabriel Bracha, "Asynchronous Byzantine Agreement Protocols", Information and Computation, 1987.
