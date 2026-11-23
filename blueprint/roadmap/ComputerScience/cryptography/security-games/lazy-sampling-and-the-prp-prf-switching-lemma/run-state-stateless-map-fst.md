# Stateless oracles as stateful oracles

A randomized oracle that draws its answer to $x$ from a distribution $O(x)$ is the stateful oracle
that ignores its state and keeps it. Running an oracle computation against this stateful oracle,
from any state, and forgetting the final state gives the run of the computation against $O$, with
fresh randomness for each query.
