# Gao–Rexford conditions guarantee BGP stability

Suppose each link of an AS graph is labelled customer–provider or peer–peer, the provider-to-customer relation is acyclic, permitted paths are valley-free (after a peer or customer edge every subsequent edge goes to a customer), and every AS prefers paths through customers over paths through peers or providers. Then the stable paths problem has no dispute wheel; hence it has a unique stable assignment and best-response routing dynamics converge.

## Proof sketch

In a dispute wheel each rim path is preferred to the spoke, so by the preference condition it starts with a customer edge whenever the spoke does not, and valley-freeness then forces the rim to descend through customers; following the wheel produces a customer–provider cycle, contradicting acyclicity.

## Depends on

- [Stable paths problem and dispute wheels](stable-paths-problem-and-dispute-wheels.md)

## Proof depends on

- [Absence of dispute wheels guarantees a unique stable assignment and convergence](absence-of-dispute-wheels-guarantees-a-unique-stable-assignment-and-convergence.md)

## Sources

- Lixin Gao and Jennifer Rexford, "Stable Internet Routing Without Global Coordination", IEEE/ACM Transactions on Networking, 2001.
- Joan Feigenbaum, Michael Schapira and Scott Shenker, "Distributed Algorithmic Mechanism Design", Algorithmic Game Theory, Cambridge University Press, 2007.
