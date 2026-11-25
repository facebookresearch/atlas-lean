# Block extraction plans with precedence

Consider three blocks $A$, $B$, $C$ and two periods, where $A$ must be extracted strictly before $B$ and $C$ is unconstrained. Each block
has positive tonnage, grade and recovery fractions in $[0, 1]$, a commodity price and a cost per tonne, and its value is the revenue
of the recovered commodity minus the extraction cost. A plan assigns each block to at most one period, respects nonnegative tonnage
capacities in each period and the precedence (if $B$ is extracted in a period, $A$ is extracted in an earlier one). Geomechanical
feasibility is a supplied constraint, not a certified safety property, and acyclic precedence alone does not make a plan feasible.

## Depends on

## Proof depends on

## Expansion

Bind this finite model to a production-planning or time-indexed scheduling formulation from a checked source, and state what is proved
about it there; ultimate-pit algorithms are a separate topic.

## Sources

- T. B. Johnson, *Optimum Open Pit Mine Production Scheduling*, PhD thesis, University of California, Berkeley, 1968.
