# Improving move

A profile $t$ is reached from $s$ by an improving move if some player $i$ changes only its own
strategy, $t = (a, s_{-i})$, and strictly lowers its cost, $c_i(t) < c_i(s)$. Sequences of
improving moves are improvement paths; best-response dynamics is a special case.

The strict better-response step of the improvement-path module, `IsStrictBetterResponse`, is the same relation with the two profiles in the opposite order: $s'$ arises from $s$ by a unilateral deviation that strictly lowers the deviator's cost.
