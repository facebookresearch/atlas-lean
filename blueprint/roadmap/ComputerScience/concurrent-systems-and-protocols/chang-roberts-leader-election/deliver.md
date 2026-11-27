# Delivering a message in the Chang–Roberts ring

On a ring of $n + 1$ processes with
identifiers $\mathrm{id}$, process $k$ receives the oldest message in its channel in state $s$.
If the channel of $k$ is empty there is no step. Otherwise let $j$ be the origin of that message,
which is removed from the channel: if $\mathrm{id}(k) < \mathrm{id}(j)$, process $k$ forwards it
by appending $j$ to the end of the channel of its successor on the ring; otherwise, if $j = k$,
process $k$ declares itself leader; otherwise the message is discarded. Nothing else changes.
