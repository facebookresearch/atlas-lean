# Run State stateless map fst

A stateless randomized oracle is the special case of a stateful one that ignores and keeps its
state: `runState` then has the output distribution of `FreeM.evalPMF`.
