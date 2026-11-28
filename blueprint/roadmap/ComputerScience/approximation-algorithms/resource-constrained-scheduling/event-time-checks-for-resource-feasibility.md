# Event-time checks for resource feasibility

Consider finitely many nonpreemptive jobs with start times $s_j$ and durations $p_j \ge 0$, each occupying the half-open interval
$[s_j, s_j + p_j)$, so a job of zero duration occupies no time. Let job $j$ demand $d_{jr} \ge 0$ of resource $r$, with nonnegative
capacities $c_r$, and let each job be assigned only to crews eligible for it. The load $D_r(t) = \sum_{j : t \in [s_j, s_j + p_j)} d_{jr}$
is constant on each interval between consecutive distinct event times $s_j$, $s_j + p_j$, and is zero before the first and after the last
event. Hence $D_r(t) \le c_r$ for every real $t$ if and only if $D_r(e) \le c_r$ at every event time $e$: checking the finitely many
events is a complete certificate of resource feasibility. Calendars must be added as extra event times or are excluded; no optimality
or approximation guarantee is claimed.

## Depends on

## Proof depends on

## Expansion

Check the statement against a scheduling source for the time-indexed or event-based feasibility test, and state the exact certificate
predicate together with its input conventions; the argument above is elementary but has not been independently checked.

## Sources

- P. Brucker, A. Drexl, R. Möhring, K. Neumann and E. Pesch, Resource-constrained project scheduling: notation, classification, models, and methods, *European Journal of Operational Research* 112 (1999) 3–41.
