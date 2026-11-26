# Eventual Convergence

If two correct replicas have equal cumulative delivered sets throughout a tail, then
at every tick of some later tail their states are equivalent under `stateEq` (e.g. give the
same answers to all queries). An isolated equality of delivered sets is not enough.
