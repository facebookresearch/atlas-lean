# Expected constant-round authenticated Byzantine agreement with honest majority

Consider the synchronous model with a public-key infrastructure, digital signatures and pairwise channels that are both authenticated and private (signatures give authentication, not confidentiality; privacy can be realized with public-key encryption), against a rushing adversary who may adaptively corrupt up to $t$ parties. For $n \ge 2t + 1$ there is a randomized Byzantine agreement protocol (and Byzantine broadcast) tolerating $t$ such corruptions that terminates in an expected constant number of rounds; in contrast, every deterministic protocol needs $t + 1$ rounds in the worst case.

## Proof sketch

All primitives are synchronous. A constant-round authenticated gradecast tolerating $t < n/2$ is built from signatures. Replacing each broadcast of a verifiable secret sharing protocol by two gradecasts, one by the sender and one by a moderator, gives moderated verifiable secret sharing, in which an honest moderator guarantees the properties of VSS. Each party shares random values by moderated VSS with each other party as moderator, which yields oblivious leader election: with constant probability all honest parties output the same honest leader. A Feldman–Micali style agreement loop in which each iteration uses such a leader succeeds with constant probability, giving an expected constant number of rounds; signatures make conflicting claims detectable, which is what allows tolerating a dishonest minority rather than a third.

## Depends on

- [Reaching Byzantine agreement](../solves.md)
- [Fail-stop, omission and Byzantine faults](../../distributed-execution-models/fail-stop-omission-and-byzantine-faults.md)

## Sources

- J. Katz, C.-Y. Koo, "On expected constant-round protocols for Byzantine agreement", Journal of Computer and System Sciences 75(2) (2009), Sections 2 and 3 (gradecast, moderated VSS, oblivious leader election).
