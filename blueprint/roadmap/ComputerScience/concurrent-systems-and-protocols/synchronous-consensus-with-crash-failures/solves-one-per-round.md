# Solving consensus against at most one crash per round

Let $Q$ be a [synchronous protocol with crash failures](crash-protocol.md) and $T \in \mathbb{N}$. The protocol $Q$ solves consensus in $T$ rounds against at most one crash per round if, for every assignment of inputs $x$ and every [admissible crash pattern for $T$ rounds](good.md) $\pi$ (crashes before round $T$, at most one per round), no two correct processes decide differently after $T$ rounds, and the value decided by a correct process is the input of some process. This is the system of Aguilera and Toueg's Theorem 1.

Since an admissible pattern has at most $T$ faulty processes, this is implied by solving consensus against any $f \ge T$ crashes ([Solving consensus against $f \ge T$ crashes includes one crash per round](solves-one-per-round-of-solves.md)).

## Sources

- M. K. Aguilera, S. Toueg, *A simple bivalency proof that t-resilient consensus requires t + 1 rounds*, Information Processing Letters 71(3–4), 1999, 155–158: Theorem 1.
