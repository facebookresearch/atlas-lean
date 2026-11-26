# Expected constant-round authenticated Byzantine agreement with honest majority

In the synchronous model with a public-key infrastructure and digital signatures, for $n \ge 2t + 1$ there is a randomized Byzantine agreement protocol (and Byzantine broadcast) tolerating $t$ Byzantine corruptions that terminates in an expected constant number of rounds; in contrast, every deterministic protocol needs $t + 1$ rounds in the worst case.

## Proof sketch

Build a moderated gradecast primitive from signatures that lets parties detect and grade a dealer's consistency in a constant number of rounds, and use verifiable secret sharing to generate an unpredictable common coin known to all parties after reconstruction. Each iteration of a Feldman–Micali style agreement loop succeeds with constant probability thanks to the coin, while signatures make conflicting claims detectable, which is what allows tolerating a dishonest minority rather than a third.

## Depends on

- [Reaching Byzantine agreement](../solves.md)
- [Fail-stop, omission and Byzantine faults](../../distributed-execution-models/fail-stop-omission-and-byzantine-faults.md)

## Proof depends on

- [Asynchronous binary Byzantine agreement and common coins](../asynchronous-byzantine-agreement-and-dag-protocols/asynchronous-binary-byzantine-agreement.md)

## Sources

- J. Katz, C.-Y. Koo, "On expected constant-round protocols for Byzantine agreement", Journal of Computer and System Sciences 75(2) (2009).
