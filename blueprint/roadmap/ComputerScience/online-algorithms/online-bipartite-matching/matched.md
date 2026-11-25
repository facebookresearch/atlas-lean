# Number of arrivals an online matcher matches

Let $A$ be an online matcher with $a$ left
vertices, $h$ a history (the neighbour lists of earlier arrivals), $U$ a list of left vertices
already matched, and $\sigma$ a sequence of arrivals, each given by its list of left neighbours.
The run of $A$ on $\sigma$ takes the arrivals in order: on an arrival with neighbour list $N$,
$A$ proposes a left vertex, or none, from the current history and $N$; a proposal $i$ with
$i \in N$ and $i \notin U$ is accepted, counting the arrival as matched and adding $i$ to $U$,
and otherwise the arrival stays unmatched; then $N$ is appended to the history. The value is the
number of arrivals matched.
