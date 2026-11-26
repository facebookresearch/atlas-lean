# Makespan

Project makespan read from the forward run at the sink: the longest source-to-sink path
weight (`makespan_exists`), `none` when the sink is unreachable. It lower-bounds the sink time of
every feasible schedule (`makespan_le_completion`) and is the earliest feasible sink time only on
covered projects with nonnegative durations (`earliestSchedule_feasible`): an occurrence off
every source-to-sink path can force a later sink. It is not the largest machine load that the
list-scheduling `Cslib.Algorithms.Lean.Scheduling.makespan` measures. (`C5`)
