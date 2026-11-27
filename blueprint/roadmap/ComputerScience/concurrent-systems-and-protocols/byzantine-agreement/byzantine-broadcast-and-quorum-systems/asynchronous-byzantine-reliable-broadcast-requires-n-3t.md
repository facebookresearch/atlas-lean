# Asynchronous Byzantine reliable broadcast requires n > 3t

In the asynchronous message-passing model with authenticated channels and $t \ge 1$ static Byzantine faults, call a protocol in which a designated transmitter sends a binary value a *Byzantine reliable broadcast* if (validity) when the transmitter is correct, all correct processes decide on its value, and (consistency and totality) when the transmitter is faulty, either no correct process decides or all correct processes decide on the same value; this is the asynchronous Byzantine Agreement of Bracha and Toueg. No deterministic protocol on $n$ processes with $3 \le n \le 3t$ achieves it (Bracha and Toueg, Theorem 5, whose three-group argument uses only validity and consistency, over two values). Their echo/ready protocol (Figure 3) achieves it whenever $n > 3t$ (Bracha and Toueg, Theorem 6). Hence, for $t \ge 1$ and $n \ge 3$, deterministic asynchronous Byzantine reliable broadcast of binary values tolerating $t$ faults exists if and only if $n > 3t$.

## Proof sketch

Partition processes into three groups of size at most $t$. Delay all messages between two groups indefinitely; a correct group must deliver without hearing from the delayed group, which might be correct, while the third group equivocates. Replaying the resulting views yields two correct processes delivering different values. For $n > 3t$, the proof of Theorem 6 shows that no two correct processes send ready messages with different values (each would need more than $(n + t)/2$ echoes, and two such sets share a correct process), and that a decision on $i$, which needs $2t + 1$ ready messages for $i$, at least $t + 1$ of them from correct processes, makes every correct process send a ready message for $i$, so that every correct process receives $2t + 1$ of them and decides $i$: this is the totality half of the second condition. The same primitive is the broadcast that Bracha (1987) builds his asynchronous Byzantine agreement protocol on. Three derived remarks are not stated in the cited theorems: the impossibility holds over every value set with at least two elements (restrict to two values) and the echo/ready protocol works verbatim over any value set; the covering argument, using totality and no spurious delivery instead of a second value, shows that reliable broadcast is impossible for $3 \le n \le 3t$ even over a singleton value set, a delivery being forced in a run where the sender is silent; and for $n \le 2$ reliable broadcast is trivially solvable.

## Depends on

- [Reliable broadcast](../../replication-and-consistency/reliable-broadcast.md)
- [Asynchronous message-passing systems](../../distributed-execution-models/asynchronous-message-passing-systems.md)
- [Fail-stop, omission and Byzantine faults](../../distributed-execution-models/fail-stop-omission-and-byzantine-faults.md)

## Proof depends on

- [Bracha's Byzantine reliable broadcast](../../replication-and-consistency/bracha-s-byzantine-reliable-broadcast.md)

## Sources

- Gabriel Bracha and Sam Toueg, "Asynchronous Consensus and Broadcast Protocols", Journal of the ACM 32(4), 1985, §5, Theorem 5 (no asynchronous Byzantine Agreement with $k \ge n/3$ faulty processes), Figure 3 and Theorem 6 (the echo/ready protocol achieves it for $k = 1, \dots, \lfloor (n - 1)/3 \rfloor$).
- Gabriel Bracha, "Asynchronous Byzantine Agreement Protocols", Information and Computation 75(2), 1987, pp. 130-143.
