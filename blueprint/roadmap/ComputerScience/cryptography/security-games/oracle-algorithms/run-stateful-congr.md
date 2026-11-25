# Locality of stateful runs

Let $s$ and $s'$ be stateful oracles that agree at every counter value other than $j$. If they also
agree at $j$ on the query that the run against $s$ from counter $i$ asks there, then the runs against
$s$ and against $s'$ from $i$ have the same output and the same transcript.
