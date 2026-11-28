# Randomized Byzantine agreement against adaptive adversaries needs quadratic messages

Any randomized Byzantine agreement protocol (or Byzantine broadcast with a designated sender) that tolerates $f \ge c n$ corruptions for a constant $c > 0$ by a strongly adaptive adversary, which may corrupt a party after observing its message and remove that message (after-the-fact removal), must have expected message complexity $\Omega(f^2)$, even with a trusted setup and signatures. Against a weakly adaptive adversary without after-the-fact removal, there are protocols with subquadratic message complexity $\tilde O(n)$ under cryptographic setup assumptions.

## Proof sketch

If correct parties send $o(f^2)$ messages in expectation, some party receives few messages; the strongly adaptive adversary corrupts each party that sends to it, erasing those messages, and isolates it at low cost, after which the isolated correct party cannot distinguish executions requiring different outputs, violating agreement or validity with constant probability. Without removal, protocols elect small committees via verifiable random functions so that only committee members speak, and an adversary that learns the committee members only after they speak cannot suppress their messages.

## Depends on

- [Reaching Byzantine agreement](../solves.md)
- [Fail-stop, omission and Byzantine faults](../../distributed-execution-models/fail-stop-omission-and-byzantine-faults.md)

## Proof depends on

- [Byzantine agreement requires quadratic communication](dolev-reischuk-quadratic-lower-bound.md)

## Sources

- I. Abraham, T.-H. H. Chan, D. Dolev, K. Nayak, R. Pass, L. Ren, E. Shi, "Communication Complexity of Byzantine Agreement, Revisited", PODC 2019; Distributed Computing 36 (2023), arXiv:1805.03391.
