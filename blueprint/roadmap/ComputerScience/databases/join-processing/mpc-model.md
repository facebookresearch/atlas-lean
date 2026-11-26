# MPC(ε) communication for database queries

Beame, Koutris and Suciu's massively parallel communication model distributes an input of $M$ bits evenly among $p\geq1$ workers. The workers have unlimited local computation and exchange private messages in synchronous rounds. With space exponent $0\leq\varepsilon\leq1$, a worker may receive a **total** of $O(M/p^{1-\varepsilon})$ bits from the other workers combined in a round. The hidden constant is independent of $M$ and $p$. This is neither an outgoing-traffic bound nor a local-memory bound. Common random bits are independent of the input. In query reporting the union of the local reports must be the answer with probability at least $1-\eta$ on each input. Randomised load balancing with abort before an excessive delivery is the example in §2.2.

In the input-server variant each relation resides on its own server, which sends only in the first round. The source's comparison in §2.4 is part of the model description: lower bounds established using separate relation inputs carry over to standard distributed inputs **in the setting of its simulation**. The argument selects a legal placement grouping workers by relation and simulates their first local computations at their relation servers. Applying it to a bit-level representation requires a suitable grouped placement and a first-round encoding that preserves the receive bound; it is not an equivalence of arbitrary input formats at all parameter values.

The [raw-position model](../parallel-query-communication/raw-position-communication.md) specifies public input shapes and wiring, integer load caps and the semantics of an aborted round. Its reporting guarantee must be instantiated with the public parameter domain and failure tolerance of the result in question, not necessarily all worker counts at each fixed input size. Its definition alone does not establish the source's simulation. Section 2.3 studies full conjunctive queries without self-joins: $q(x)=S(x,y)$ is not full, and $S(x,y),S(y,z)$ repeats a relation. Reporting all tuples differs from producing one witness.

## Depends on

- [Query reporting with public raw-bit layouts](../parallel-query-communication/raw-position-communication.md)

## Proof depends on

- [Simulating the first round with relation input servers](input-server-simulation.md)

## Sources

- Paul Beame, Paraschos Koutris and Dan Suciu, *Communication Steps for Parallel Query Processing*, PODS 2013, §§2.1–2.4. [Authors' copy](https://homes.cs.washington.edu/~beame/papers/mpcpods.pdf).
