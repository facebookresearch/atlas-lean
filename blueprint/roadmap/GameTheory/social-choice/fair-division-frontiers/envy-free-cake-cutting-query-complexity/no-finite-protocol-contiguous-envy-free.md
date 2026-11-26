# No finite protocol finds contiguous envy-free divisions for three or more agents

For $n \ge 3$ agents with nonatomic valuations on $[0, 1]$, there is no finite (bounded or unbounded but always terminating) protocol in the Robertson–Webb query model that always outputs an envy-free allocation in which every agent receives a single interval, even though such allocations always exist by Stromquist's moving-knife theorem.

## Proof sketch

Assume a finite protocol exists. An adversary maintains a family of valuations consistent with the answers so far and, since the protocol eventually outputs finitely many cut points determined by finitely many query answers, it can perturb the valuations near the cut points without changing any answer so that some agent strictly prefers an adjacent interval. The perturbation keeps valuations nonatomic and consistent with all queries, contradicting envy-freeness.

## Depends on

- [Cake cutting in the Robertson-Webb query model](../../cake-cutting-in-the-robertson-webb-query-model.md)

## Proof depends on

- [Cake cutting in the Robertson-Webb query model](../../cake-cutting-in-the-robertson-webb-query-model.md)

## Sources

- W. Stromquist, "Envy-free cake divisions cannot be found by finite protocols", Electronic Journal of Combinatorics 15 (2008), R11.
