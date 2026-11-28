# Byzantine agreement requires quadratic communication

Consider deterministic protocols solving Byzantine agreement (Byzantine broadcast from a transmitter) among $n$ processes tolerating $f < n - 1$ Byzantine faults in the synchronous model.

- (Authenticated protocols, signature bound; Theorem 1.) If processes share an unforgeable signature scheme, there is an execution in which correct processes send at least $n(f+1)/4$ signatures in total. The bound counts signatures under the technical assumption that every message carries at least its sender's signature; without that convention, a protocol could send unsigned messages, and the bound is then on the number of signatures plus the number of unsigned messages.
- (Unauthenticated protocols.) Treating each message of an unauthenticated protocol as carrying exactly one signature, that of its sender, the same argument shows that at least $n(f+1)/4$ messages are necessary.
- (Message bound for all deterministic protocols, authenticated included; Theorem 2.) There is an execution in which correct processes send at least $\max\{(n-1)/2,\ (1+f/2)^2\}$ messages.

For $f = \Theta(n)$ each bound is $\Omega(n^2)$.

## Proof sketch

For the message bound, let a set $B$ of about $f/2$ processes be Byzantine: they behave correctly except that they ignore the first $f/2$ messages sent to them and do not communicate among themselves. If fewer than $(f/2)^2$ messages are sent to $B$, some $p \in B$ receives at most $f/2$ messages; a second adversary leaves $p$ correct, corrupts the at most $f/2$ processes that sent to $p$ and suppresses those messages, so $p$ sees no messages while the other correct processes see the same execution. Then $p$ must decide the value it decides on receiving nothing, and choosing the transmitter's input accordingly forces disagreement. The signature bound plays the same game with the set of processes whose signatures a correct process exchanges.

## Depends on

- [Reaching Byzantine agreement](../solves.md)
- [Fail-stop, omission and Byzantine faults](../../distributed-execution-models/fail-stop-omission-and-byzantine-faults.md)

## Sources

- D. Dolev, R. Reischuk, "Bounds on Information Exchange for Byzantine Agreement", Journal of the ACM 32(1) (1985), Sections 3 and 4 (Theorems 1 and 2).
- I. Abraham, T.-H. H. Chan, D. Dolev, K. Nayak, R. Pass, L. Ren, E. Shi, "Communication Complexity of Byzantine Agreement, Revisited", PODC 2019; Distributed Computing 36 (2023), arXiv:1805.03391 (warmup to its lower bound, recalling the Dolev–Reischuk argument).
