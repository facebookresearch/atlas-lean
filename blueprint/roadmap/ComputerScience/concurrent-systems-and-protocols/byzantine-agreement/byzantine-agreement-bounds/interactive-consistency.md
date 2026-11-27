# Interactive consistency

In the synchronous complete-network model with $n$ processes, each holding a private input from a set $V$, a deterministic protocol solves *interactive consistency* against $t$ Byzantine faults in $R$ rounds if, for every set $F$ of at most $t$ faulty processes sending arbitrary (possibly recipient-dependent) messages, after round $R$ all correct processes output the same vector in $V^n$ whose entry for every correct process $i$ is $i$'s input.

## Depends on

- [Reaching Byzantine agreement](../solves.md)
- [Fail-stop, omission and Byzantine faults](../../distributed-execution-models/fail-stop-omission-and-byzantine-faults.md)

## Sources

- Marshall Pease, Robert Shostak and Leslie Lamport, "Reaching Agreement in the Presence of Faults", Journal of the ACM, 1980.
- Michael J. Fischer and Nancy A. Lynch, "A Lower Bound for the Time to Assure Interactive Consistency", Information Processing Letters, 1982.
