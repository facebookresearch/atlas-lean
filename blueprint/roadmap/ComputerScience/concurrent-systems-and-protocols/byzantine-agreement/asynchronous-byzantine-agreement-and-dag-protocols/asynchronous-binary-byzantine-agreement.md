# Asynchronous binary Byzantine agreement and common coins

In the asynchronous model, $n$ processes communicate over reliable authenticated channels with arbitrary finite delays chosen by an adversary, and at most $t$ processes are Byzantine. Each process has an input bit; a protocol solves binary Byzantine agreement if every correct process decides a bit (termination with probability $1$), no two correct processes decide differently (agreement), and if all correct processes have the same input $b$ then $b$ is the only possible decision (validity). A common coin is a primitive that, in each round $r$, returns to every correct process the same uniformly random bit $s_r$, unpredictable to the adversary until $t + 1$ processes have invoked it. Two separate facts limit the problem. The FLP theorem rules out deterministic protocols: no deterministic asynchronous protocol guarantees termination with even one crash fault, and a Byzantine process can behave as a crashed one, so deterministic protocols fail already for $t = 1$; randomization (here, the common coin) is what makes termination with probability $1$ possible. Independently, the resilience bound of Bracha and Toueg shows that $n \ge 3t + 1$ is necessary for asynchronous Byzantine agreement, randomized protocols included.

## Depends on

- [Asynchronous message-passing systems](../../distributed-execution-models/asynchronous-message-passing-systems.md)
- [Fail-stop, omission and Byzantine faults](../../distributed-execution-models/fail-stop-omission-and-byzantine-faults.md)
- [FLP impossibility of asynchronous consensus with agreement, validity and termination](../../flp-impossibility/flp-impossibility.md)

## Sources

- A. Mostéfaoui, H. Moumen, M. Raynal, "Signature-Free Asynchronous Binary Byzantine Consensus with t < n/3, O(n^2) Messages, and O(1) Expected Time", Journal of the ACM 62(4) (2015); PODC 2014.
- M. J. Fischer, N. A. Lynch, M. S. Paterson, "Impossibility of Distributed Consensus with One Faulty Process", Journal of the ACM 32(2) (1985).
- G. Bracha, S. Toueg, "Asynchronous Consensus and Broadcast Protocols", Journal of the ACM 32(4) (1985).
