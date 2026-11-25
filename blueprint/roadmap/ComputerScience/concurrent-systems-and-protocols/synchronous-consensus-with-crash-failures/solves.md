# Solving consensus with crash failures

Let the set of processes be finite, $Q$ a [synchronous protocol with crash failures](crash-protocol.md) and $f, T \in \mathbb{N}$. The protocol $Q$ solves consensus tolerating $f$ crashes in $T$ rounds if, for every assignment of inputs $x$ and every [crash pattern](crash-pattern.md) with at most $f$ [faulty processes](faulty.md), no two correct processes decide differently after $T$ rounds (agreement), and the value decided by a correct process is the input of some process (validity).

Termination is built in: every correct process decides at the end of round $T$. Faulty processes are not required to decide or to agree (agreement is not uniform).
