# Solving consensus against $f \ge T$ crashes includes one crash per round

Let the set of processes be finite and let $Q$ be a [synchronous protocol with crash failures](crash-protocol.md). If $Q$ [solves consensus](solves.md) in $T$ rounds against every crash pattern with at most $f$ faulty processes, and $T \le f$, then it [solves consensus against every pattern admissible for $T$ rounds](solves-one-per-round.md), with crashes before round $T$, at most one per round.

## Informally uses

- [An admissible pattern has at most $T$ faulty processes](card-faulty-le.md): such patterns have at most $T \le f$ faults.
