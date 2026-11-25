# Logarithmic event bound for indexed-queue extract-min

Let $q$ be an indexed minimum
queue whose heap has $s$ entries. For each of the five counted events (comparisons, swaps,
position reads, position writes, and entry appends, pops or replacements), the number of times
that event occurs when extracting the minimum of $q$ is at most
$20 (\lfloor \log_2 (s + 1) \rfloor + 1)$.
