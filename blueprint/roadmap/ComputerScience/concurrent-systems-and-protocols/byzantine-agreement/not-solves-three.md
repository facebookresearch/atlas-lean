# No synchronous protocol for three processes reaches Byzantine agreement with one fault

Let there be at least two values. No deterministic synchronous protocol for three processes reaches Byzantine agreement with one faulty process, in any number of rounds. This is the case $n = 3$, $m = 1$ of the general bound, which Fischer, Lynch and Merritt (1986, §3.1) prove first, by the hexagon argument: six copies of the three devices, arranged in a ring with inputs $0, 0, 0, 1, 1, 1$, look locally like three correct executions with one faulty process each, whose validity and agreement requirements contradict one another.

The model is the one of [Synchronous Byzantine agreement protocol](agreement-protocol.md): synchronous rounds, Byzantine failures, a complete network of reliable links with known senders, no signatures.

## Informally uses

- [No synchronous protocol reaches Byzantine agreement when $3 \le n \le 3m$](not-solves-of-card-le-three-mul.md): the general bound, of which this is the case $n = 3$, $m = 1$.

## Background

- [No protocol for three generals tolerates one traitor](../byzantine-generals-problem/exists-violation-three.md): the commander version, proved by a commander form of the hexagon argument.

## Sources

- M. J. Fischer, N. A. Lynch, M. Merritt, *Easy impossibility proofs for distributed consensus problems*, Distributed Computing 1(1), 1986, 26–39: §3.1.
