# Running the sweep over a list of events

Starting from a status list $T$, the sweep steps
are applied to the events in order, each to the status list left by the previous one. The result
is the final status list, or no result as soon as some step reports an intersection; on the empty
list of events the result is $T$.
